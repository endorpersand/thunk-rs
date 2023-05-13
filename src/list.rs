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

/// Checks if the given `Rc<T>` points to an *isolated* reference cycle of `Rc<T>`s
/// (i.e., no other `Rc<T>` directly points into this reference cycle).
/// The `f` callback indicates how to access the next `Rc<T>` in the sequence.
/// 
/// If this function does find a isolated cycle, it points to an `Rc<T>` in the cycle 
/// Otherwise, this function returns None.
/// 
/// If a cycle *is* found, every `Rc<T>` within the cycle is known to have 1 reference exactly.
/// 
/// # Safety
/// 
/// The provided `Rc<T>` must have at least 2 strong references.
unsafe fn find_isolated_cycle<T>(start: Rc<T>, mut f: impl FnMut(&T) -> Option<&Rc<T>>) -> Option<*const T> {
    // Destroy Rc in ref count
    // SAFETY: We know there are at least 2 strong references.
    let start = Rc::into_raw(start);
    Rc::decrement_strong_count(start);
    
    let mut ef = |t| f(t).filter(|rc| Rc::strong_count(rc) == 1);
    // SAFETY: >=1 ref, still 
    let mut tort = ef(&*start)?;
    let mut hare = ef(tort)?;

    while !Rc::ptr_eq(tort, hare) {
        tort = ef(tort)?;
        hare = ef(hare)?;
        hare = ef(hare)?;
    }
    
    Some(Rc::as_ptr(tort))
}
fn drop_maybe_node<T>(head: Rc<MaybeNode<T>>) {
    // Repeatedly pop nodes until we hit shared nodes, a cycle, or nothing.
    let mut head = Some(head);

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
            Err(rc) => unsafe {
                // This Rc has at least two references.
                // We want to check if it has multiple references because it's part of shared data
                // or because it's part of an isolated ref cycle.
                if let Some(start) = find_isolated_cycle(rc, |t| t.try_get()?.as_ref()?.next.as_ref()) {
                    // Break cycle by dereferencing Rc ptr and using it to pop Node's .next.
                    // This is okay because only one Node points to this ptr,
                    // and that Node should not access/mutate the ptr before it's destroyed.
                    head = (*start.cast_mut())
                        .try_get_mut()
                        .unwrap_unchecked() // we know it's Some by cycle check
                        .as_mut()
                        .unwrap_unchecked() // also Some by cycle check
                        .next
                        .take();
                }
            },
        }
    }
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
        if let Some(head) = self.next.take() {
            drop_maybe_node(head)
        }
    }
}
impl<T> Clone for Node<'_, T> {
    fn clone(&self) -> Self {
        Self { val: Rc::clone(&self.val), next: self.next.clone() }
    }
}

#[derive(Debug)]
pub struct ThunkList<'a, T: 'a> {
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

    fn pushed<F>(mut self, f: F) -> ThunkList<'a, T> 
        where F: Thunkable<Item = T> + 'a
    {
        let node = Node::new(
            f.into_thunk().boxed(),
            std::mem::take(&mut self.head)
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
impl<'a, T: 'a> Drop for ThunkList<'a, T> {
    fn drop(&mut self) {
        drop_maybe_node(std::mem::take(&mut self.head))
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
        Self { head: Rc::clone(&self.head) }
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
    fn examine_rc_path<T>(weak: &std::rc::Weak<super::MaybeNode<T>>, ct: usize) {
        fn get_next<'a, 'b, T>(t: &'b super::MaybeNode<'a, T>) -> Option<&'b Rc<super::MaybeNode<'a, T>>> {
            t.try_get()?.as_ref()?.next.as_ref()
        }

        println!("start ptr: {:?}, ct: {}", weak.as_ptr(), weak.strong_count());

        if weak.strong_count() < 1 { return; }
        let mut ptr = weak.as_ptr();

        // SAFETY: strong count >= 1, therefore ptr exists
        unsafe {
            for _ in 0..ct {
                if let Some(next) = get_next(&*ptr) {
                    println!("ptr: {:?}, ct: {}", Rc::as_ptr(next), Rc::strong_count(next));
                    ptr = Rc::as_ptr(next);
                } else {
                    println!("exit");
    
                }
            }
        }
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
            let (next, lst2) = ThunkList::raw_cons(Thunk::of(0usize));
            let ptr = Rc::downgrade(&lst2.head);
    
            let lst = ThunkList::cons_known(3usize, 
                ThunkList::cons_known(2usize, 
                    ThunkList::cons_known(1usize, lst2.clone())
                )
            );
            next.bind(&lst);
            
            let first_ten = take_nc(&lst, 10);
            assert_eq!(first_ten, [3, 2, 1, 0, 3, 2, 1, 0, 3, 2]);
            
            examine_rc_path(&ptr, 10);
            
            println!();
            println!("dropping {:?}", Rc::as_ptr(&lst.head));
            std::mem::drop(lst);
            examine_rc_path(&ptr, 10);
            
            println!();
            println!("dropping {:?}", Rc::as_ptr(&lst2.head));
            std::mem::drop(lst2);
            examine_rc_path(&ptr, 10);

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