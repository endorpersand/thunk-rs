use std::rc::Rc;

use crate::{Thunk, Thunkable, ThunkAny};

/// An Option<Node> thunk
type MaybeNode<'a, T> = ThunkAny<'a, Option<Node<'a, T>>>;

#[derive(Debug)]
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

#[derive(Debug)]
pub struct ThunkList<'a, T> {
    head: Rc<MaybeNode<'a, T>>
}
impl<'a, T> ThunkList<'a, T> {
    pub fn new() -> Self {
        ThunkList { head: Rc::new(Thunk::known(None)) }
    }
    pub fn cons<F>(f: F, lst: Self) -> ThunkList<'a, T> 
        where F: Thunkable<Item = T> + 'a
    {
        lst.pushed(f)
    }
    pub fn cons_known(t: T, lst: Self) -> ThunkList<'a, T>
        where T: 'a
    {
        lst.pushed(Thunk::of(t))
    }

    pub fn raw_cons<F>(f: F) -> (LPtr<'a, T>, ThunkList<'a, T>)
        where T: 'a,
              F: Thunkable<Item = T> + 'a
    {
        let next = LPtr::new();
        let node = Node::new(
            f.into_thunk().boxed(),
            Rc::clone(&next.0)
        );

        (next, ThunkList::from(node))
    }

    pub fn cons_cyclic<F>(f: F) -> ThunkList<'a, T> 
        where T: 'a,
              F: Thunkable<Item = T> + 'a
    {
        let (next, lst) = ThunkList::raw_cons(f);
        next.bind(&lst);
        
        lst
    }

    fn pushed<F>(self, f: F) -> ThunkList<'a, T> 
        where F: Thunkable<Item = T> + 'a
    {
        let node = Node::new(
            f.into_thunk().boxed(),
            self.head
        );

        ThunkList::from(node)
    }

    pub fn split_first(&self) -> Option<(Rc<ThunkAny<'a, T>>, ThunkList<'a, T>)> {
        let Node { val, next } = self.head.force().as_ref()?;

        let val = Rc::clone(val);
        let rest = match next.as_ref() {
            Some(rest) => ThunkList { head: Rc::clone(rest) },
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
    pub fn iterate_known(mut f: impl FnMut() -> Option<T> + 'a) -> ThunkList<'a, T> {
        ThunkList::iterate(move || f().map(Thunk::known))
    }
    pub fn iterate(f: impl FnMut() -> Option<ThunkAny<'a, T>> + 'a) -> ThunkList<'a, T> {
        fn iterate_node<'a, T>(mut f: impl FnMut() -> Option<ThunkAny<'a, T>> + 'a) -> MaybeNode<'a, T> {
            Thunk::new(|| {
                    let node = Node::new(f()?, Rc::new(iterate_node(f)));
                    Some(node)
                })
                .into_thunk()
                .boxed()
        }

        ThunkList::from(iterate_node(f))
    }

    pub fn from_iter<I: IntoIterator<Item=T> + 'a>(iter: I) -> ThunkList<'a, T> {
        let mut it = iter.into_iter();
        ThunkList::iterate_known(move || it.next())
    }
}

pub struct LPtr<'a, T>(Rc<MaybeNode<'a, T>>);
impl<'a, T> LPtr<'a, T> {
    fn new() -> Self 
        where T: 'a
    {
        LPtr(Rc::new(Thunk::undef().boxed()))
    }

    pub fn bind(self, l: &ThunkList<'a, T>) -> bool {
        self.0.set(l.head.force().clone()).is_ok()
    }
}

impl<T> Default for ThunkList<'_, T> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T> Clone for ThunkList<'_, T> {
    fn clone(&self) -> Self {
        Self { head: self.head.clone() }
    }
}
impl<'a, T> From<MaybeNode<'a, T>> for ThunkList<'a, T> {
    fn from(value: MaybeNode<'a, T>) -> Self {
        ThunkList { head: Rc::new(value) }
    }
}
impl<'a, T> From<Node<'a, T>> for ThunkList<'a, T> {
    fn from(value: Node<'a, T>) -> Self {
        ThunkList::from(Thunk::known(Some(value)))
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
#[allow(dead_code)]
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
        let c = ThunkList::cons_known(2usize, ThunkList::cons_known(1usize, ThunkList::new()));

        let mut cit = c.iter();
        assert_eq!(cit.next().map(Thunk::force), Some(&2));
        assert_eq!(cit.next().map(Thunk::force), Some(&1));
        assert_eq!(cit.next().map(Thunk::force), None);
    }

    #[test]
    fn cc() {
        {
            const N: usize = 13;
            let lst = ThunkList::cons_cyclic(Thunk::of(N));
            let ptr = Rc::downgrade(&lst.head);
    
            let first_ten = take_nc(&lst, 10);
            assert_eq!(first_ten, [N; 10]);
    
            std::mem::drop(lst);
            assert_eq!(ptr.strong_count(), 0, 
                "rc still exists, strong count: {}", ptr.strong_count()
            );
        }
        
        {
            let (next, lst) = ThunkList::raw_cons(Thunk::of(0usize));
            let ptr = Rc::downgrade(&lst.head);
    
            let lst = ThunkList::cons_known(3usize, 
                ThunkList::cons_known(2usize, 
                    ThunkList::cons_known(1usize, lst)
                )
            );
            next.bind(&lst);

            let first_ten = take_nc(&lst, 10);
            assert_eq!(first_ten, [3, 2, 1, 0, 3, 2, 1, 0, 3, 2]);

            std::mem::drop(lst);

            assert_eq!(ptr.strong_count(), 0, 
                "rc still exists, strong count: {}", ptr.strong_count()
            );
        }
    }

    #[test]
    fn iterate() {
        let mut ctr = 0usize;
        {
            let lst = ThunkList::iterate_known(|| {ctr += 1; Some(dbg!(ctr))});
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