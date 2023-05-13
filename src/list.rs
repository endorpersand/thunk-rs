use std::rc::Rc;

use crate::{Thunk, Thunkable, ThunkAny};

/// An Option<Node> thunk
type MaybeNode<'a, T> = ThunkAny<'a, Option<Node<'a, T>>>;

struct Node<'a, T> {
    val: Rc<ThunkAny<'a, T>>,

    // This outer Option should only be None once Node is in state to drop.
    next: Option<Rc<MaybeNode<'a, T>>>
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

impl<'a, T> Node<'a, T> {
    fn new(val: ThunkAny<'a, T>, next: Rc<ThunkAny<'a, Option<Node<'a, T>>>>) -> Node<'a, T> {
        Node {
            val: Rc::new(val),
            next: Some(next),
        }
    }
}
impl<T> Drop for Node<'_, T> {
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
impl<T> Clone for Node<'_, T> {
    fn clone(&self) -> Self {
        Self { val: self.val.clone(), next: self.next.clone() }
    }
}

pub struct ThunkList<'a, T> {
    head: MaybeNode<'a, T>
}
impl<'a, T> ThunkList<'a, T> {
    pub fn new() -> Self {
        ThunkList { head: Thunk::known(None) }
    }

    pub fn cons<F>(f: F, lst: &'a Self) -> ThunkList<'a, T> 
        where T: 'a,
              F: Thunkable<Item = T> + 'a
    {
        lst.pushed(f)
    }
    pub fn cons_known(t: T, lst: &'a Self) -> ThunkList<'a, T>
        where T: 'a
    {
        lst.pushed_known(t)
    }
    pub fn cons_cyclic<F>(f: F) -> ThunkList<'a, T> 
        where T: 'a,
              F: Thunkable<Item = T> + 'a
    {
        let next = Rc::new(Thunk::undef().boxed());
        let node = Node::new(
            f.into_thunk().boxed(),
            Rc::clone(&next)
        );
        
        next.set(Some(node.clone()))
            .ok()
            .expect("Thunk::undef should have been empty");

        ThunkList { head: Thunk::known(Some(node)) }
    }

    fn pushed<F>(&'a self, f: F) -> ThunkList<'a, T> 
        where T: 'a,
              F: Thunkable<Item = T> + 'a
    {
        let next = Rc::new(
            (&self.head).cloned()
                .into_thunk()
                .boxed()
        );
        let node = Node::new(
            f.into_thunk().boxed(),
            next
        );

        ThunkList { head: Thunk::known(Some(node)) }
    }
    fn pushed_known(&'a self, t: T) -> ThunkList<'a, T> 
        where T: 'a
    {
        self.pushed(Thunk::of(t))
    }

    pub fn split_first(&'a self) -> Option<(Rc<ThunkAny<'a, T>>, ThunkList<'a, T>)> {
        let Node { val, next } = self.head.force().as_ref()?;

        let val = Rc::clone(val);
        let rest = match next.as_deref() {
            Some(rest) => ThunkList { head: rest.cloned().into_thunk().boxed() },
            // self.head looks like T:[]
            None => ThunkList::new(),
        };
        
        Some((val, rest))
    }
    pub fn iter(&self) -> Iter<'a, '_, T> {
        Iter(Some(&self.head))
    }
    pub fn get(&self, n: usize) -> Option<&ThunkAny<'a, T>> {
        self.iter().nth(n)
    }
    pub fn get_forced(&self, n: usize) -> Option<&T> {
        self.iter().nth(n).map(Thunk::force)
    }
    pub fn len(&self) -> usize {
        self.iter().count()
    }
    pub fn is_empty(&self) -> bool {
        self.head.force().is_none()
    }
    pub fn iterate(f: impl FnMut() -> Option<T> + 'a) -> ThunkList<'a, T> {
        fn iterate_node<'a, T>(f: impl FnMut() -> Option<T> + 'a) -> MaybeNode<'a, T> {
            Thunk::of(f)
                .map(|mut f| {
                    let val = f()?;
                    let node = Node::new(Thunk::known(val), Rc::new(iterate_node(f)));
                    Some(node)
                })
                .into_thunk()
                .boxed()
        }

        ThunkList {
            head: iterate_node(f)
        }
    }

    pub fn from_iter<I: IntoIterator<Item=T> + 'a>(iter: I) -> ThunkList<'a, T> {
        let mut it = iter.into_iter();
        ThunkList::iterate(move || it.next())
    }
}

impl<T> Default for ThunkList<'_, T> {
    fn default() -> Self {
        Self::new()
    }
}
pub struct Iter<'a, 'b, T>(Option<&'b MaybeNode<'a, T>>);
impl<'a, 'b, T> Iterator for Iter<'a, 'b, T> {
    type Item = &'b ThunkAny<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.0?.force().as_ref()?;
        
        let val = node.val.as_ref();
        self.0 = node.next.as_deref();
        
        Some(val)
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::Thunk;

    use super::ThunkList;

    fn take_n<'a, T>(t: &'a ThunkList<T>, n: usize) -> Vec<&'a T> {
        t.iter()
            .take(n)
            .map(Thunk::force)
            .collect()
    }
    fn take_nc<T: Clone>(t: &ThunkList<T>, n: usize) -> Vec<T> {
        t.iter()
            .take(n)
            .map(Thunk::force)
            .cloned()
            .collect()
    }

    #[test]
    fn conner() {
        unsafe {
            let a = Box::into_raw(Box::new(ThunkList::new()));
            let b = Box::into_raw(Box::new(ThunkList::cons_known(1usize, &*a)));
            let c = ThunkList::cons_known(2usize, &*b);
            let wk = Rc::downgrade((*b).head.force().as_ref().unwrap().next.as_ref().unwrap());

            let mut cit = c.iter();
            assert_eq!(cit.next().map(Thunk::force), Some(&2));
            assert_eq!(cit.next().map(Thunk::force), Some(&1));
            assert_eq!(cit.next().map(Thunk::force), None);

            std::mem::drop(c);
            std::mem::drop(Box::from_raw(b));
            std::mem::drop(Box::from_raw(a));

            assert!(wk.upgrade().is_none());
        }
    }

    #[test]
    fn cc() {
        let t: usize = 0;
        let lst = ThunkList::cons_cyclic(Thunk::of(t));
        let ptr = Rc::downgrade(&lst.head.force().as_ref().unwrap().val);

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

    #[test]
    fn iterate() {
        let mut ctr = 0usize;
        {
            let lst = ThunkList::iterate(|| {ctr += 1; Some(dbg!(ctr))});
            println!("{:?}", take_nc(&lst, 1));
            println!("{:?}", take_nc(&lst, 5));
            println!("{:?}", take_nc(&lst, 10));
        }
        ctr += 1;
        println!("{ctr}");
    }

    #[test]
    fn iterate2() {
        let lst = ThunkList::from_iter(0..10);
        println!("{:?}", lst.get_forced(1));
        println!("{:?}", lst.get_forced(5));
    }
}