use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::rc::Rc;

use crate::{Thunkable, ThunkAny};

/// An Option<Node> thunk
type MaybeNode<'a, T> = ThunkAny<'a, Option<Node<'a, T>>>;
// fn down<'a, 'b>(t: ThunkList<'static, &'static ()>) -> ThunkList<'a, &'b ()> { t }

#[derive(Debug)]
struct Node<'a, T> {
    val: Rc<ThunkAny<'a, T>>,
    next: NodePtr<'a, T>
}

/// Wrapper holding either null or an Rc ptr pointing to a Node thunk.
/// 
/// When dropped, this breaks any isolated node cycles.
#[derive(Debug)]
struct NodePtr<'a, T>(Option<Rc<MaybeNode<'a, T>>>);
impl<'a, T> NodePtr<'a, T> {
    fn new(thunk: MaybeNode<'a, T>) -> Self {
        Self(Some(Rc::new(thunk)))
    }
    /// Used for indicating this pointer is no longer used and can be dropped.
    fn take_inner(&mut self) -> Option<Rc<MaybeNode<'a, T>>> {
        self.0.take()
    }
    fn into_inner(self) -> Option<Rc<MaybeNode<'a, T>>> {
        ManuallyDrop::new(self).take_inner()
    }
    /// Force resolves thunk.
    fn force(&self) -> Option<&Node<'a, T>> {
        self.0.as_deref()?.force().as_ref()
    }

    fn as_rc(&self) -> Option<&Rc<MaybeNode<'a, T>>> {
        self.0.as_ref()
    }
}
impl<'a, T> Clone for NodePtr<'a, T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<'a, T> Drop for NodePtr<'a, T> {
    fn drop(&mut self) {
        // Repeatedly pop nodes until we hit shared nodes, a cycle, or nothing.
        let mut head = self.take_inner();
        while let Some(rc) = head.take() {
            match Rc::try_unwrap(rc) {
                Ok(thunk) => {
                    // This data is owned only by us, so we can destroy it however we like.
                    // If this thunk is initialized (outer Option), check if it holds a Node (inner Option).
                    // If it does, set its next to be destroyed.
                    if let Some(Some(mut inner)) = thunk.try_into_inner() {
                        head = inner.next.take_inner();
                    }
                },
                Err(rc) => unsafe {
                    // This Rc has at least two references.
                    // We want to check if it has multiple references because it's part of shared data
                    // or because it's part of an isolated ref cycle.
                    if let Some(start) = find_isolated_cycle(rc, |t| t.try_get()?.as_ref()?.next.as_rc()) {
                        // Break cycle by dereferencing Rc ptr and using it to pop Node's .next.
                        // This is okay because only one Node points to this ptr,
                        // and that Node should not access/mutate the ptr before it's destroyed.
                        head = (*start.cast_mut())
                            .try_get_mut()
                            .unwrap_unchecked() // we know it's Some by cycle check
                            .as_mut()
                            .unwrap_unchecked() // also Some by cycle check
                            .next
                            .take_inner();
                    }
                },
            }
        }
    }
}
impl<'a, T> From<Rc<MaybeNode<'a, T>>> for NodePtr<'a, T> {
    fn from(value: Rc<MaybeNode<'a, T>>) -> Self {
        NodePtr(Some(value))
    }
}
impl<'a, T> From<MaybeNode<'a, T>> for NodePtr<'a, T> {
    fn from(value: MaybeNode<'a, T>) -> Self {
        NodePtr::new(value)
    }
}
impl<'a, T> From<Node<'a, T>> for NodePtr<'a, T> {
    fn from(value: Node<'a, T>) -> Self {
        NodePtr::from(ThunkAny::of(Some(value)))
    }
}

impl<T> Clone for Node<'_, T> {
    fn clone(&self) -> Self {
        Self { val: Rc::clone(&self.val), next: self.next.clone() }
    }
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

pub struct ThunkList<'a, T> {
    head: NodePtr<'a, T>
}
impl<'a, T> ThunkList<'a, T> {
    pub fn new() -> Self {
        ThunkList { head: NodePtr::new(ThunkAny::of(None)) }
    }
    pub fn cons(f: ThunkAny<'a, T>, lst: Self) -> ThunkList<'a, T> {
        lst.pushed(f)
    }
    pub fn cons_known(t: T, lst: Self) -> ThunkList<'a, T> {
        lst.pushed(ThunkAny::of(t))
    }

    pub fn raw_cons(f: ThunkAny<'a, T>) -> (TailPtr<'a, T>, ThunkList<'a, T>) {
        let next = TailPtr::new();
        let node = Node {
            val: Rc::new(f),
            next: NodePtr::from(Rc::clone(&next.ptr)),
        };

        (next, ThunkList { head: NodePtr::from(node) })
    }
    fn pushed(self, f: ThunkAny<'a, T>) -> ThunkList<'a, T> {
        let node = Node {
            val: Rc::new(f),
            next: self.head,
        };

        ThunkList { head: NodePtr::from(node) }
    }

    pub fn first(&self) -> Option<&ThunkAny<T>> {
        self.iter().next()
    }
    pub fn last(&self) -> Option<&ThunkAny<T>> {
        self.iter().last()
    }

    pub fn reverse(self) -> ThunkList<'a, T> {
        let mut lst = self;
        let mut rev = NodePtr(None);

        while let Some((el, rest)) = lst.split_first() {
            lst = rest;
            
            let node = Node {val: el, next: rev };
            rev = NodePtr::from(node);
        }
        
        ThunkList { head: rev }
    }
    pub fn repeat(f: ThunkAny<'a, T>) -> ThunkList<'a, T> {
        let (next, lst) = ThunkList::raw_cons(f);
        next.bind(&lst);
        
        lst
    }
    pub fn split_first(self) -> Option<(Rc<ThunkAny<'a, T>>, ThunkList<'a, T>)> {
        let node = match Rc::try_unwrap(self.head.into_inner()?) {
            Ok(t) => t.dethunk(),
            Err(e) => e.force().clone(),
        }?;

        let Node { val, next } = node;
        Some((val, ThunkList { head: next }))
    }
    pub fn foldr<U, F>(self, f: F, base: ThunkAny<'a, U>) -> ThunkAny<'a, U> 
        where F: for<'f> FnMut(Rc<ThunkAny<'f, T>>, ThunkAny<'f, U>) -> U + 'a
    {
        fn foldr_node<'a, T, U, F>(nptr: NodePtr<'a, T>, mut f: F, base: ThunkAny<'a, U>) -> ThunkAny<'a, U>
            where F: for<'f> FnMut(Rc<ThunkAny<'f, T>>, ThunkAny<'f, U>) -> U + 'a
        {
            match nptr.into_inner() {
                Some(rc) => {
                    let node = match Rc::try_unwrap(rc) {
                        Ok(t) => t,
                        Err(e) => ThunkAny::of(e.force().clone()),
                    };

                    node.and_then(|inner| match inner {
                        Some(node) => {
                            let Node { val, next } = node;
                            let base = f(val, base);

                            foldr_node(next, f, ThunkAny::of(base))
                        },
                        None => base,
                    })
                    .into_thunk()
                    .boxed()
                },
                None => base,
            }
        }

        foldr_node(self.head, f, base)
    }
    pub fn iter(&self) -> Iter<T> {
        Iter(&self.head)
    }
    pub fn get(&self, n: usize) -> Option<&ThunkAny<T>> {
        self.iter().nth(n)
    }
    pub fn get_forced(&self, n: usize) -> Option<&T> {
        self.get(n).map(ThunkAny::force)
    }
    pub fn len(&self) -> usize {
        self.iter().count()
    }
    pub fn is_empty(&self) -> bool {
        self.head.force().is_none()
    }
    pub fn iterate_known(mut f: impl FnMut() -> Option<T> + 'a) -> ThunkList<'a, T> {
        ThunkList::iterate(move || f().map(ThunkAny::of))
    }
    pub fn iterate(f: impl FnMut() -> Option<ThunkAny<'a, T>> + 'a) -> ThunkList<'a, T> {
        fn iterate_node<'a, T>(mut f: impl FnMut() -> Option<ThunkAny<'a, T>> + 'a) -> MaybeNode<'a, T> {
            crate::ThunkBox::new(|| {
                Some(Node {
                    val: Rc::new(f()?),
                    next: NodePtr::from(iterate_node(f))
                })
            }).into_thunk_a()
        }

        ThunkList { head: NodePtr::from(iterate_node(f)) }
    }
    pub fn iterate_strict(mut f: impl FnMut() -> Option<ThunkAny<'a, T>>) -> ThunkList<'a, T> {
        match f() {
            Some(el) => {
                let (mut next, lst) = ThunkList::raw_cons(el);
                while let Some(el) = f() {
                    let (next1, lst1) = ThunkList::raw_cons(el);
                    next.bind(&lst1);
                    next = next1;
                }
                next.bind(&ThunkList::new());

                lst
            }
            None => ThunkList::new()
        }
    }
    pub fn from_iter_lazy<I: IntoIterator<Item=T> + 'a>(iter: I) -> ThunkList<'a, T> {
        let mut it = iter.into_iter();
        ThunkList::iterate_known(move || it.next())
    }
}
impl<'a, T: std::fmt::Debug> std::fmt::Debug for ThunkList<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.iter().map(ThunkAny::force))
            .finish()
    }
}

pub struct TailPtr<'a, T> {
    ptr: Rc<MaybeNode<'a, T>>,
    // Force invariance on 'a, T
    _ghost: PhantomData<*mut Node<'a, T>>
}
impl<'a, T> TailPtr<'a, T> {
    fn new() -> Self {
        TailPtr {
            ptr: Rc::new(ThunkAny::undef()),
            _ghost: PhantomData
        }
    }

    pub fn bind(self, l: &ThunkList<'a, T>) -> bool {
        let val = l.head.force().cloned();

        // SAFETY: LPtr is invariant over Node<'a, T>, 
        // so only pointers of same lifetime are allowed.
        unsafe {
            self.ptr.set(val).is_ok()
        }
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
pub struct Iter<'r, T>(&'r NodePtr<'r, T>);
impl<'r, T> Iterator for Iter<'r, T> {
    type Item = &'r ThunkAny<'r, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.0.force()?;
        
        let val = node.val.as_ref();
        self.0 = &node.next;
        
        Some(val)
    }
}
pub struct IntoIter<'a, T>(Option<ThunkList<'a, T>>);
impl<'a, T> Iterator for IntoIter<'a, T> {
    type Item = Rc<ThunkAny<'a, T>>;

    fn next(&mut self) -> Option<Self::Item> {
        let t = self.0.take()?;
        let (head, rest) = t.split_first()?;
        self.0.replace(rest);
        Some(head)
    }
}
impl<'a, T> IntoIterator for ThunkList<'a, T> {
    type Item = Rc<ThunkAny<'a, T>>;
    type IntoIter = IntoIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(Some(self))
    }
}
impl<'a, A> FromIterator<A> for ThunkList<'a, A> {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let mut it = iter.into_iter();
        ThunkList::iterate_strict(move || it.next().map(ThunkAny::of))
    }
}
impl<'a, A> FromIterator<ThunkAny<'a, A>> for ThunkList<'a, A> {
    fn from_iter<T: IntoIterator<Item = ThunkAny<'a, A>>>(iter: T) -> Self {
        let mut it = iter.into_iter();
        ThunkList::iterate_strict(move || it.next())
    }
}

#[allow(unused_macros)]
macro_rules! list {
    () => { $crate::list::ThunkList::new() };
    (; $l:expr$(,)?) => { $l };
    ($h:expr$(, $($e:expr),*)?$(; $l:expr)?$(,)?) => { $crate::list::ThunkList::cons_known($h, list![$($($e),*)?$(; $l)?]) }
}

#[cfg(test)]
#[allow(dead_code)]
mod tests {
    use std::rc::Rc;

    use crate::{ThunkAny, Thunkable};

    use super::ThunkList;

    fn take_n<'a, T>(t: &'a ThunkList<T>, n: usize) -> Vec<&'a T> {
        t.iter()
            .take(n)
            .map(ThunkAny::force)
            .collect()
    }
    fn take_nc<T: Clone>(t: &ThunkList<T>, n: usize) -> Vec<T> {
        t.iter()
            .take(n)
            .map(ThunkAny::force)
            .cloned()
            .collect()
    }
    fn examine_rc_path<T>(weak: &std::rc::Weak<super::MaybeNode<T>>, ct: usize) {
        fn get_next<'a, 'b, T>(t: &'b super::MaybeNode<'a, T>) -> Option<&'b Rc<super::MaybeNode<'a, T>>> {
            t.try_get()?.as_ref()?.next.as_rc()
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
        let c = list![2usize, 1, 0];

        let mut cit = c.iter();
        assert_eq!(cit.next().map(ThunkAny::force), Some(&2));
        assert_eq!(cit.next().map(ThunkAny::force), Some(&1));
        assert_eq!(cit.next().map(ThunkAny::force), Some(&0));
        assert_eq!(cit.next().map(ThunkAny::force), None);
        
        let mut cit = c.into_iter();
        assert_eq!(cit.next().map(|t| Rc::try_unwrap(t).unwrap()).map(ThunkAny::dethunk), Some(2));
        assert_eq!(cit.next().map(|t| Rc::try_unwrap(t).unwrap()).map(ThunkAny::dethunk), Some(1));
        assert_eq!(cit.next().map(|t| Rc::try_unwrap(t).unwrap()).map(ThunkAny::dethunk), Some(0));
        assert_eq!(cit.next().map(|t| Rc::try_unwrap(t).unwrap()).map(ThunkAny::dethunk), None);
    }

    #[test]
    fn cc() {
        {
            const N: usize = 13;
            let lst = ThunkList::repeat(ThunkAny::of(N));
            let ptr = Rc::downgrade(lst.head.as_rc().unwrap());
    
            let first_ten = take_nc(&lst, 10);
            assert_eq!(first_ten, [N; 10]);
    
            std::mem::drop(lst);
            assert_eq!(ptr.strong_count(), 0, 
                "rc still exists, strong count: {}", ptr.strong_count()
            );
        }
        
        {
            let (next, lst2) = ThunkList::raw_cons(ThunkAny::of(0usize));
            let ptr = Rc::downgrade(lst2.head.as_rc().unwrap());
    
            let lst = list![3, 2, 1; lst2.clone()];
            next.bind(&lst);
            
            let first_ten = take_nc(&lst, 10);
            assert_eq!(first_ten, [3, 2, 1, 0, 3, 2, 1, 0, 3, 2]);
            
            examine_rc_path(&ptr, 10);
            
            println!();
            println!("dropping {:?}", Rc::as_ptr(lst.head.as_rc().unwrap()));
            std::mem::drop(lst);
            examine_rc_path(&ptr, 10);
            
            println!();
            println!("dropping {:?}", Rc::as_ptr(lst2.head.as_rc().unwrap()));
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

    #[test]
    fn lifetimes() {
        let s = "str";
        {
            let t = String::from("hello");
            let x = list!["str", &t];
            std::mem::drop(x);
            std::mem::drop(t);
        }
        println!("{s}");
    }

    #[test]
    fn raw_cons_lifetimes() {
        let (_ptr1, list1) = ThunkList::raw_cons(ThunkAny::of("hello"));
        {
            let a = String::from("hello");
            let (ptr2, list2) = ThunkList::raw_cons(ThunkAny::of(a.as_str()));
            ptr2.bind(&list1);
            std::mem::drop(list2);
        }
        std::mem::drop(list1);
    }

    #[test]
    fn strict_collect() {
        let list: ThunkList<usize> = (0..=15)
            .map(|i| {
                ThunkAny::of(i)
                .inspect(|t| println!("initialized {t}"))
                    .map(|t| t * 2)
                    .into_thunk()
                    .boxed()
            })
            .collect();

        println!("{:?}", list.get(14).map(ThunkAny::force));
        println!("{:?}", list.get(3).map(ThunkAny::force));
        println!("{:?}", list.get(12).map(ThunkAny::force));
        println!("{:?}", list.get(2).map(ThunkAny::force));
        println!("{:?}", list.get(4).map(ThunkAny::force));
        println!("{:?}", list.get(9).map(ThunkAny::force));
        println!("{:?}", list.get(1).map(ThunkAny::force));
    }

    #[test]
    fn foldr_test() {
        let superand: ThunkList<bool> = (1..=100)
            .map(|i| {
                ThunkAny::of(i)
                    .inspect(|t| println!("initialized {t}"))
                    .map(|t| t % 29 != 0)
                    .into_thunk()
                    .boxed()
            })
            .collect();

        let foldy = superand
            .foldr(|t, u| u.dethunk() && *t.force(), ThunkAny::of(true));
        println!("{:?}", foldy.force());
    }
}