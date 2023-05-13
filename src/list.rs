use std::rc::Rc;

use crate::{Thunk, Thunkable, ThunkAny};

struct Node<T> {
    val: Rc<ThunkAny<'static, T>>,

    // This outer Option should only be None once Node is in state to drop.
    next: Option<Rc<ThunkAny<'static, Option<Node<T>>>>>
}

/// Checks if the given `Rc<T>` points to an *isolated* reference cycle of `Rc<T>`'s
/// (i.e., no other `Rc<T>` directly points into this reference cycle).
/// The `f` parameter details how to get from one `Rc<T>` to another.
/// 
/// If this function does find a isolated cycle, it clones a `Rc<T>` in the cycle 
/// (since this is the only `Rc<T>` pointing into the cycle, this is ensured to have 2 strong refs,
/// and every other `Rc<T>` in the cycle should only have one).
/// 
/// Otherwise, it will return None.
fn find_isolated_cycle<T>(start: Rc<T>, mut f: impl FnMut(&T) -> Option<&Rc<T>>) -> Option<Rc<T>> {
    let mut ef = |t| {
        f(t).filter(|rc| {
            // we want to ignore any cycles that are pointed to from other places
            // so we got to make sure there are no other references
            let equal = Rc::ptr_eq(&start, rc);
            let strong_ct = Rc::strong_count(rc);
    
            strong_ct == if equal { 2 } else { 1 }
        })
    };
    let mut tort = ef(&start)?;
    let mut hare = ef(tort)?;

    while !Rc::ptr_eq(tort, hare) {
        tort = ef(tort)?;
        hare = ef(hare)?;
        hare = ef(hare)?;
    }
    
    Some(tort).cloned()
}

impl<T> Node<T> {
    fn new(val: ThunkAny<'static, T>, next: Rc<ThunkAny<'static, Option<Node<T>>>>) -> Node<T> {
        Node {
            val: Rc::new(val),
            next: Some(next),
        }
    }
}
impl<T> Drop for Node<T> {
    fn drop(&mut self) {
        // Repeatedly pop nodes until we hit shared nodes, a cycle, or nothing.
        let mut head = self.next.take();
        while let Some(rc) = head.take() {
            match Rc::try_unwrap(rc) {
                Ok(thunk) => {
                    // This data is owned only by us, so we can destroy it however we like.
                    // If this thunk is initialized (outer Option), check if it holds a Node (inner Option).
                    // If it does, set its next to be destroyed.
                    if let Some(Some(mut inner)) = thunk.try_into_inner() {
                        head = inner.next.take();
                    }
                },
                Err(rc) => {
                    // This data must either be in an isolated cycle or is accessible elsewhere.
                    // If it is part of an isolated cycle, then we can destroy it.
                    if let Some(start) = find_isolated_cycle(rc, |t| t.try_get()?.as_ref()?.next.as_ref()) {
                        unsafe {
                            let ptr = Rc::into_raw(start).cast_mut();

                            // Our start Rc no longer will be used, 
                            // so destroy it in ref count to enable mutation.
                            // SAFETY: 
                            // 1. `ptr` is from Rc::into_raw
                            // 2. the associated Rc came from find_isolated_cycle, 
                            //    which dictates the returned Rc has 2 strong references.
                            Rc::decrement_strong_count(ptr);

                            // in order to chain break, we need to take an Rc off 
                            // one of the Nodes in the chain.

                            // Use the ptr to mutably access another Node and pop its .next.
                            // This is okay because only one Node points to this ptr,
                            // and that Node should not access/mutate the ptr before it's destroyed.
                            head = (*ptr).try_get_mut()
                                .unwrap_unchecked() // we know it's Some by cycle check
                                .as_mut()
                                .unwrap_unchecked() // also Some by cycle check
                                .next
                                .take();
                        }
                    }
                },
            }
        }
    }
}
impl<T> Clone for Node<T> {
    fn clone(&self) -> Self {
        Self { val: self.val.clone(), next: self.next.clone() }
    }
}

pub struct ThunkList<T> {
    head: Option<Node<T>>
}
impl<T> ThunkList<T> {
    pub fn new() -> Self {
        ThunkList { head: None }
    }

    pub fn cons<F>(f: F, lst: &Self) -> ThunkList<T> 
        where T: 'static,
              F: Thunkable<Item = T> + 'static
    {
        lst.pushed(f)
    }
    pub fn cons_known(t: T, lst: &Self) -> ThunkList<T>
        where T: 'static
    {
        lst.pushed_known(t)
    }
    pub fn cons_cyclic<F>(f: F) -> ThunkList<T> 
        where T: 'static,
              F: Thunkable<Item = T> + 'static
    {
        let next = Rc::new(Thunk::undef().boxed());
        let node = Node::new(
            f.into_thunk().boxed(),
            Rc::clone(&next)
        );
        
        next.set(Some(node.clone()))
            .ok()
            .expect("Thunk::undef should have been empty");

        ThunkList { head: Some(node) }
    }

    fn pushed<F>(&self, f: F) -> ThunkList<T> 
        where T: 'static,
              F: Thunkable<Item = T> + 'static
    {
        let next = Rc::new(
            Thunk::of(self.head.clone()).boxed()
        );
        let node = Node::new(
            f.into_thunk().boxed(),
            next
        );

        ThunkList { head: Some(node) }
    }
    fn pushed_known(&self, t: T) -> ThunkList<T> 
        where T: 'static
    {
        self.pushed(Thunk::of(t))
    }

    pub fn split_first(&self) -> Option<(Rc<ThunkAny<'static, T>>, ThunkList<T>)> {
        let Node { val, next } = self.head.as_ref()?;
        
        let head = next.as_deref()
            .map(Thunk::force)
            .and_then(Option::clone);

        Some((Rc::clone(val), ThunkList { head }))
    }
    pub fn iter(&self) -> Iter<T> {
        Iter(self.head.as_ref())
    }
    pub fn get(&self, n: usize) -> Option<&ThunkAny<'static, T>> {
        self.iter().nth(n)
    }
    pub fn get_forced(&self, n: usize) -> Option<&T> {
        self.iter().nth(n).map(Thunk::force)
    }
    pub fn len(&self) -> usize {
        self.iter().count()
    }
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }
}

impl<T> Default for ThunkList<T> {
    fn default() -> Self {
        Self::new()
    }
}
pub struct Iter<'a, T>(Option<&'a Node<T>>);
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a ThunkAny<'static, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.0?;
        let val = &*node.val;

        self.0 = node.next.as_deref()
            .map(Thunk::force)
            .and_then(Option::as_ref);
        
        Some(val)
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::Thunk;

    use super::ThunkList;

    #[test]
    fn conner() {
        let t = ThunkList::new();
        let u = ThunkList::cons_known(2usize, &ThunkList::cons_known(1usize, &t));
        let mut ui = u.iter();

        assert_eq!(ui.next().map(Thunk::force), Some(&2));
        assert_eq!(ui.next().map(Thunk::force), Some(&1));
        assert_eq!(ui.next().map(Thunk::force), None);
    }

    #[test]
    fn cc() {
        let t: usize = 0;
        let lst = ThunkList::cons_cyclic(Thunk::of(t));
        let ptr = Rc::downgrade(&lst.head.as_ref().unwrap().val);

        // println!("rc count: {}", Rc::strong_count(&lst.head.as_ref().unwrap().val));
        let first_ten: Vec<_> = lst.iter()
            .take(10)
            .map(Thunk::force)
            .copied()
            .collect();
        assert_eq!(first_ten, [t; 10]);

        std::mem::drop(lst);
        assert!(ptr.upgrade().is_none(), "rc still exists, strong count: {}", ptr.strong_count() - 1);
    }
}