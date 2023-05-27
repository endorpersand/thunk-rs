use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::rc::Rc;

use crate::{ThunkAny, Thunkable, Thunk};

/// Checks if the given `Rc<T>` points to a reference cycle of `Rc<T>`s.
/// The `f` callback indicates how to access the next `Rc<T>` in the sequence.
/// 
/// If this function does find a cycle, it points to an `Rc<T>` in the cycle.
/// Otherwise, this function returns None.
fn find_cycle<T>(start: Rc<T>, mut f: impl FnMut(&T) -> Option<&Rc<T>>) -> Option<*const T> {
    let weak = Rc::downgrade(&start);
    std::mem::drop(start);

    if weak.strong_count() == 0 { return None; }
    let start = weak.as_ptr();

    // SAFETY: strong count >= 1
    let mut tort = f(unsafe { &*start })?;
    let mut hare = f(tort)?;

    while !Rc::ptr_eq(tort, hare) {
        tort = f(tort)?;
        hare = f(hare)?;
        hare = f(hare)?;
    }
    
    Some(Rc::as_ptr(tort))
}
/// Checks if the given `Rc<T>` points to an *isolated* reference cycle of `Rc<T>`s
/// (i.e., no other `Rc<T>` directly points into this reference cycle).
/// The `f` callback indicates how to access the next `Rc<T>` in the sequence.
/// 
/// If this function does find a isolated cycle, it points to an `Rc<T>` in the cycle.
/// Otherwise, this function returns None.
/// 
/// If a cycle *is* found, every `Rc<T>` within the cycle is known to have 1 reference exactly.
fn find_isolated_cycle<T>(start: Rc<T>, mut f: impl FnMut(&T) -> Option<&Rc<T>>) -> Option<*const T> {
    find_cycle(start, |t| f(t).filter(|rc| Rc::strong_count(rc) == 1))
}

/// Traverses a directed graph, calculating the length before loop, and the loop length
fn find_cycle_len<T, NEXT, EQ>(start: &T, mut next: NEXT, mut eq: EQ) -> (usize, usize) 
    where NEXT: FnMut(&T) -> Option<&T>,
        EQ: FnMut(&T, &T) -> bool
{
    // searching powers of 2
    let mut power = 1;
    let mut lambda = 1;
    let mut tort = start;
    let Some(mut hare) = next(tort) else { return (power, 0) };

    // check tort (2^i - 1) against 2^i ..= 2^(i + 1)
    while !eq(tort, hare) {
        if power == lambda {
            tort = hare;
            power *= 2;
            lambda = 0;
        }

        hare = match next(hare) {
            Some(t) => t,
            None => return (power + lambda, 0),
        };
        lambda += 1;
    }

    // Distance tort & hare by lambda
    tort = start;
    hare = start;
    for _ in 0..lambda {
        hare = next(hare)
            .expect("hare failed to traverse through known pointers");
    }

    // count mu
    let mut mu = 0;
    while !eq(tort, hare) {
        tort = next(tort)
            .expect("tort failed to traverse through known pointers");
        hare = next(hare)
            .expect("hare failed to traverse through known pointers");
        mu += 1;
    }
 
    (mu, lambda)
}

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
    /// Dethunk inner
    fn dethunk_inner(self) -> Option<Node<'a, T>> {
        self.into_inner()?.dethunk_or_clone()
    }
    fn as_rc(&self) -> Option<&Rc<MaybeNode<'a, T>>> {
        self.0.as_ref()
    }
    /// Points to the Node, or null.
    #[allow(unused)]
    fn as_ptr(&self) -> *const MaybeNode<'a, T> {
        match &self.0 {
            Some(rc) => Rc::as_ptr(rc),
            None => std::ptr::null(),
        }
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
                Err(rc) => {
                    // We want to check if it has multiple references because it's part of shared data
                    // or because it's part of an isolated ref cycle.
                    if let Some(start) = find_isolated_cycle(rc, |t| t.try_get()?.as_ref()?.next.as_rc()) {
                        unsafe {
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
impl<T> PartialEq for NodePtr<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (None, None) => true,
            (None, Some(_)) => false,
            (Some(_), None) => false,
            (Some(t), Some(u)) => Rc::ptr_eq(t, u),
        }
    }
}
impl<T> Eq for NodePtr<'_, T> {}
impl<T> Clone for Node<'_, T> {
    fn clone(&self) -> Self {
        Self { val: Rc::clone(&self.val), next: self.next.clone() }
    }
}

/// A singly-linked linked list aimed to be similar to Haskell's Data.List.
pub struct ThunkList<'a, T> {
    head: NodePtr<'a, T>
}
impl<'a, T> ThunkList<'a, T> {
    /// Creates a new empty list.
    pub fn new() -> Self {
        ThunkList { head: NodePtr::new(ThunkAny::of(None)) }
    }

    /// Concats a thunk to the front of this list.
    pub fn cons(f: Thunk<T, impl Thunkable<Item = T> + 'a>, this: impl Into<Self>) -> ThunkList<'a, T> {
        let node = Node {
            val: Rc::new(f.boxed()),
            next: this.into().head,
        };

        ThunkList { head: NodePtr::from(node) }
    }
    /// Concats a value to the front of this list.
    pub fn cons_known(t: T, this: impl Into<Self>) -> ThunkList<'a, T> {
        ThunkList::cons(ThunkAny::of(t), this.into())
    }

    /// Creates a list whose tail can be edited.
    pub fn tailed() -> (TailPtr<'a, T>, ThunkList<'a, T>) {
        let tail = TailPtr::new();
        let list = ThunkList { head: tail.as_node_ptr() };

        (tail, list)
    }

    /// Adds a pointer to the end of the list.
    pub fn raw_append(self) -> (TailPtr<'a, T>, ThunkList<'a, T>) {
        fn insert_end<'a, T>(ptr: NodePtr<'a, T>, end: NodePtr<'a, T>) -> NodePtr<'a, T> {
            NodePtr::from({
                (|| match ptr.dethunk_inner() {
                    Some(Node { val, next }) => Some(Node { val, next: insert_end(next, end) }),
                    None => end.dethunk_inner()
                }).into_thunk_any()
            })
        }

        let tail = TailPtr::new();
        let head = insert_end(self.head, tail.as_node_ptr());
        (tail, ThunkList { head })
    }
    /// Appends two lists together.
    pub fn append(self, rest: ThunkList<'a, T>) -> ThunkList<'a, T> {
        let (next, list) = self.raw_append();
        next.bind(&rest);
        list
    }

    /// Gets the first thunk in the list.
    pub fn first(&self) -> Option<&ThunkAny<T>> {
        self.iter().next()
    }
    /// Gets the last thunk in the list.
    /// 
    /// This will hang if the list is infinite.
    pub fn last(&self) -> Option<&ThunkAny<T>> {
        self.iter().last()
    }
    /// Reverses the list.
    /// 
    /// This will hang when this list is resolved if the list is infinite.
    pub fn reverse(self) -> ThunkList<'a, T> {
        crate::ThunkBox::new(|| {
            let mut lst = self;
            let mut rev = NodePtr(None);
    
            while let Some((val, rest)) = lst.split_first() {
                lst = rest;
                
                let node = Node { val, next: rev };
                rev = NodePtr::from(node);
            }
            
            ThunkList { head: rev }
        }).into_thunk_any().into()
    }
    /// Creates a list where the provided thunk element is repeated infinitely.
    /// 
    /// This is a lazy operation.
    pub fn repeat(f: Thunk<T, impl Thunkable<Item=T> + 'a>) -> ThunkList<'a, T> {
        let (mut tail, lst) = ThunkList::tailed();
        tail.append(f);
        tail.bind(&lst);
        
        lst
    }
    /// Splits the first element.
    /// 
    /// This is a strict operation and will immediately split the list.
    pub fn split_first(self) -> Option<(Rc<ThunkAny<'a, T>>, ThunkList<'a, T>)> {
        let Node { val, next } = self.head.dethunk_inner()?;
        Some((val, ThunkList { head: next }))
    }

    fn cursor(self, n: usize) -> (ThunkList<'a, T>, TailPtr<'a, T>, ThunkList<'a, T>) {
        let (mut tail, left) = ThunkList::tailed();
        let mut right = self;

        for _ in 0..n {
            if let Some((val, rest)) = right.split_first() {
                right = rest;
                tail.raw_append(val);
            } else {
                return (left, tail, ThunkList::new());
            }
        }

        (left, tail, right)
    }
    pub fn split_at(self, n: usize) -> (ThunkList<'a, T>, ThunkList<'a, T>) {
        let (left, ltail, right) = self.cursor(n);
        ltail.close();
        (left, right)
    }
    pub fn insert(self, n: usize, t: Thunk<T, impl Thunkable<Item=T> + 'a>) -> ThunkList<'a, T> {
        let (left, mut ltail, right) = self.cursor(n);
        ltail.append(t);
        ltail.bind(&right);
        left
    }
    pub fn foldr<U, F>(self, f: F, base: Thunk<U, impl Thunkable<Item=U> + 'a>) -> ThunkAny<'a, U> 
        where F: FnMut(Rc<ThunkAny<'a, T>>, ThunkAny<'a, U>) -> U + Copy + 'a
    {
        fn foldr_node<'a, T, U, F>(nptr: NodePtr<'a, T>, mut f: F, base: ThunkAny<'a, U>) -> ThunkAny<'a, U>
            where F: FnMut(Rc<ThunkAny<'a, T>>, ThunkAny<'a, U>) -> U + Copy + 'a
        {
            crate::ThunkBox::new(move || {
                let Some(node) = nptr.dethunk_inner() else { return base.dethunk() };
                let Node { val, next } = node;
    
                let rhs = foldr_node(next, f, base);
                f(val, rhs)
            }).into_thunk_any()
        }

        foldr_node(self.head, f, base.boxed())
    }
    pub fn iter(&self) -> Iter<T> {
        Iter(&self.head)
    }
    pub fn iter_strict(&self) -> IterStrict<T> {
        IterStrict(&self.head)
    }
    /// Gets the thunk at this index.
    pub fn get(&self, n: usize) -> Option<&ThunkAny<T>> {
        self.iter().nth(n)
    }
    /// Gets the value at this index.
    /// 
    /// This will resolve the value at the index if not already resolved.
    pub fn get_strict(&self, n: usize) -> Option<&T> {
        self.get(n).map(ThunkAny::force)
    }
    /// Gets the length of the linked list (as an iterator).
    /// 
    /// This will hang if the list is infinite.
    pub fn len(&self) -> usize {
        self.iter().count()
    }
    /// Gets the length of the linked list.
    /// 
    /// This returns the length of the list prior to any cycle, and then the length of the cycle.
    /// This will hang if the list is infinite but does not have a cycle.
    pub fn list_len(&self) -> (usize, usize) {
        fn eq<T>(a: &Node<T>, b: &Node<T>) -> bool {
            // Two nodes are list_len equal if they have the same value ptr
            // and same next ptr
            Rc::ptr_eq(&a.val, &b.val) && a.next == b.next
        }

        match self.head.force() {
            Some(node) => find_cycle_len(node, |t| t.next.force(), eq),
            None => (0, 0),
        }
    }
    /// Gets whether the linked list is empty or not.
    pub fn is_empty(&self) -> bool {
        self.head.force().is_none()
    }
    pub fn iterate_known(mut f: impl FnMut() -> Option<T> + 'a) -> ThunkList<'a, T> {
        ThunkList::iterate(move || f().map(ThunkAny::of))
    }
    pub fn iterate<F>(f: impl FnMut() -> Option<Thunk<T, F>> + 'a) -> ThunkList<'a, T> 
        where F: Thunkable<Item=T> + 'a
    {
        fn iterate_node<'a, T, F>(mut f: impl FnMut() -> Option<Thunk<T, F>> + 'a) -> NodePtr<'a, T> 
            where F: Thunkable<Item = T> + 'a
        {
            NodePtr::from({
                crate::ThunkBox::new(|| {
                    Some(Node {
                        val: Rc::new(f()?.boxed()),
                        next: iterate_node(f)
                    })
                }).into_thunk_any()
            })
        }

        ThunkList { head: iterate_node(f) }
    }
    pub fn iterate_strict<F>(f: impl FnMut() -> Option<Thunk<T, F>>) -> ThunkList<'a, T> 
        where F: Thunkable<Item=T> + 'a
    {
        let (mut tail, lst) = ThunkList::tailed();

        tail.extend(std::iter::from_fn(f));
        tail.close();
        lst
    }
    pub fn from_iter_lazy<F, I>(iter: I) -> ThunkList<'a, T> 
        where F: Thunkable<Item=T> + 'a,
            I: IntoIterator<Item=Thunk<T, F>> + 'a
    {
        let mut it = iter.into_iter();
        ThunkList::iterate(move || it.next())
    }
}
impl<'a, T: std::fmt::Debug> std::fmt::Debug for ThunkList<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.iter_strict())
            .finish()
    }
}
impl<'a, T, F> From<Thunk<ThunkList<'a, T>, F>> for ThunkList<'a, T> 
    where F: Thunkable<Item = ThunkList<'a, T>> + 'a
{
    /// Creates a new ThunkList from a lazily evaluated ThunkList.
    ///
    /// This does not evaluate the list.
    /// This should be used instead of [`Thunk::dethunk`] in situations
    /// where the list does not need to be resolved.
    fn from(thunk: Thunk<ThunkList<'a, T>, F>) -> Self {
        ThunkList {
            head: NodePtr::from({
                (|| {
                    thunk.dethunk().head.dethunk_inner()
                }).into_thunk_any()
            })
        }
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

    fn as_node_ptr(&self) -> NodePtr<'a, T> {
        NodePtr::from(Rc::clone(&self.ptr))
    }

    /// Appends an Rc value into the node.
    fn raw_append(&mut self, val: Rc<ThunkAny<'a, T>>) {
        use std::mem::replace;

        let tail = TailPtr::new();
        let node = Node { val, next: tail.as_node_ptr() };

        // SAFETY: TailPtr is invariant over Node<'a, T>, 
        // so parameters will match lifetime of initialized TailPtr.
        unsafe {
            replace(self, tail).ptr.set_unchecked(Some(node))
                .ok()
                .expect("TailPtr should not have been set")
        }
    }

    /// Appends a thunk value to the current tail.
    pub fn append(&mut self, val: Thunk<T, impl Thunkable<Item=T> + 'a>) {
        self.raw_append(Rc::new(val.boxed()))
    }

    pub fn bind(self, l: &ThunkList<'a, T>) {
        let val = l.head.force().cloned();

        // SAFETY: TailPtr is invariant over Node<'a, T>, 
        // so parameters will match lifetime of initialized TailPtr.
        unsafe {
            self.ptr.set_unchecked(val)
                .ok()
                .expect("TailPtr should not have been set")
        }
    }
    pub fn close(self) {
        // SAFETY: None is not dependent on lifetime.
        unsafe {
            self.ptr.set_unchecked(None)
                .ok()
                .expect("TailPtr should not have been set")
        }
    }
}
impl<A> Extend<A> for TailPtr<'_, A> {
    fn extend<T: IntoIterator<Item = A>>(&mut self, iter: T) {
        for el in iter {
            self.append(ThunkAny::of(el));
        }
    }
}
impl<'a, A, F> Extend<Thunk<A, F>> for TailPtr<'a, A> 
    where F: Thunkable<Item=A> + 'a
{
    fn extend<T: IntoIterator<Item = Thunk<A, F>>>(&mut self, iter: T) {
        for el in iter {
            self.append(el);
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
impl<T: PartialEq> PartialEq for ThunkList<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        let (mu1, la1) = self.list_len();
        let (mu2, la2) = other.list_len();
        let cmp_size = mu1.max(mu2) + la1 * la2;

        self.iter().take(cmp_size)
            .eq(other.iter().take(cmp_size))
    }
}
impl<T: Eq> Eq for ThunkList<'_, T> {}

impl<T: PartialOrd> PartialOrd for ThunkList<'_, T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}
impl<T: Ord> Ord for ThunkList<'_, T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}

pub struct Iter<'r, T>(&'r NodePtr<'r, T>);
impl<'r, T> Iterator for Iter<'r, T> {
    type Item = &'r ThunkAny<'r, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let Node { val, next } = self.0.force()?;
        
        self.0 = next;
        Some(val.as_ref())
    }
}
pub struct IterStrict<'r, T>(&'r NodePtr<'r, T>);
impl<'r, T> Iterator for IterStrict<'r, T> {
    type Item = &'r T;

    fn next(&mut self) -> Option<Self::Item> {
        let Node { val, next } = self.0.force()?;
        
        self.0 = next;
        Some(val.force())
    }
}

pub struct IntoIter<'a, T>(Option<ThunkList<'a, T>>);
impl<'a, T> Iterator for IntoIter<'a, T> {
    type Item = Rc<ThunkAny<'a, T>>;

    fn next(&mut self) -> Option<Self::Item> {
        let (head, rest) = self.0.take()?.split_first()?;
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
impl<A> FromIterator<A> for ThunkList<'_, A> {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let mut it = iter.into_iter();
        ThunkList::iterate_strict(move || it.next().map(ThunkAny::of))
    }
}
impl<'a, A, F: Thunkable<Item=A> + 'a> FromIterator<Thunk<A, F>> for ThunkList<'a, A> {
    fn from_iter<T: IntoIterator<Item = Thunk<A, F>>>(iter: T) -> Self {
        let mut it = iter.into_iter();
        ThunkList::iterate_strict(move || it.next())
    }
}
impl<T, const N: usize> From<[T; N]> for ThunkList<'_, T> {
    fn from(value: [T; N]) -> Self {
        ThunkList::from_iter(value)
    }
}
impl<'a, T, const N: usize> From<([T; N], ThunkList<'a, T>)> for ThunkList<'a, T> {
    fn from(value: ([T; N], ThunkList<'a, T>)) -> Self {
        let (left, right) = value;
        
        left.into_iter()
            .rfold(right, |acc, cv| ThunkList::cons_known(cv, acc))
    }
}

#[cfg(test)]
#[allow(dead_code)]
mod tests {
    use std::rc::{Rc, Weak};

    use crate::iter::ThunkItertools;
    use crate::ThunkAny;

    use super::ThunkList;

    fn take_n<'a, T>(t: &'a ThunkList<T>, n: usize) -> Vec<&'a T> {
        t.iter_strict()
            .take(n)
            .collect()
    }
    fn take_nc<T: Clone>(t: &ThunkList<T>, n: usize) -> Vec<T> {
        t.iter_strict()
            .take(n)
            .cloned()
            .collect()
    }
    fn examine_rc_path<T>(weak: &Weak<super::MaybeNode<T>>, ct: usize) {
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
    fn get_weak_head<'a, T>(list: &ThunkList<'a, T>) -> Weak<super::MaybeNode<'a, T>> {
        Rc::downgrade(list.head.as_rc().unwrap())
    }

    #[test]
    fn list_to_iter() {
        let c = ThunkList::from([2usize, 1, 0]);

        let mut cit = c.iter();
        assert_eq!(cit.next().map(ThunkAny::force), Some(&2));
        assert_eq!(cit.next().map(ThunkAny::force), Some(&1));
        assert_eq!(cit.next().map(ThunkAny::force), Some(&0));
        assert_eq!(cit.next().map(ThunkAny::force), None);

        let mut cit = c.iter_strict();
        assert_eq!(cit.next(), Some(&2));
        assert_eq!(cit.next(), Some(&1));
        assert_eq!(cit.next(), Some(&0));
        assert_eq!(cit.next(), None);
        
        let mut cit = c.into_iter();
        assert_eq!(cit.next().map(|t| t.dethunk_or_clone()), Some(2));
        assert_eq!(cit.next().map(|t| t.dethunk_or_clone()), Some(1));
        assert_eq!(cit.next().map(|t| t.dethunk_or_clone()), Some(0));
        assert_eq!(cit.next().map(|t| t.dethunk_or_clone()), None);
    }

    #[test]
    fn tail_ptr_test() {
        {
            const N: usize = 13;
            let lst = ThunkList::repeat(ThunkAny::of(N)); // [N, ...]
            let ptr = get_weak_head(&lst);
    
            let first_ten = take_nc(&lst, 10);
            assert_eq!(first_ten, [N; 10]);
    
            std::mem::drop(lst);
            assert_eq!(ptr.strong_count(), 0, 
                "rc still exists, strong count: {}", ptr.strong_count()
            );
        }
        
        {
            let (tail, lst2) = ThunkList::tailed();
            let ptr = get_weak_head(&lst2);
    
            let lst = ThunkList::from(([3, 2, 1, 0], lst2.clone()));
            tail.bind(&lst);
            
            let first_ten = take_nc(&lst, 10);
            assert_eq!(first_ten, [3, 2, 1, 0, 3, 2, 1, 0, 3, 2]);
            
            examine_rc_path(&ptr, 10);
            
            println!();
            println!("dropping {:?}", lst.head.as_ptr());
            std::mem::drop(lst);
            examine_rc_path(&ptr, 10);
            
            println!();
            println!("dropping {:?}", lst2.head.as_ptr());
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
            assert_eq!(take_nc(&lst, 1), [1]);
            assert_eq!(take_nc(&lst, 5), [1, 2, 3, 4, 5]);
            assert_eq!(take_nc(&lst, 10), [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
        }
        ctr += 1;
        assert_eq!(ctr, 11);
    }

    #[test]
    fn lifetimes() {
        let s = "str";
        {
            let t = String::from("hello");
            let x = ThunkList::from(["str", &t]);
            std::mem::drop(x);
            std::mem::drop(t);
        }
        println!("{s}");
    }

    #[test]
    fn tail_ptr_lifetimes() {
        let (mut ptr1, list1) = ThunkList::tailed();
        ptr1.append(ThunkAny::of("hello"));

        {
            let a = String::from("hello");
            let (mut ptr2, list2) = ThunkList::tailed();
            ptr2.append(ThunkAny::of(a.as_str()));
            ptr2.bind(&list1);
            std::mem::drop(list2);
        }
        std::mem::drop(list1);
    }

    #[test]
    fn strict_collect() {
        let list: ThunkList<usize> = (0..=15)
            .map_delayed(|i| {
                println!("initialized {i}");
                i * 2
            })
            .collect();

        assert_eq!(list.get_strict(14), Some(&28));
        assert_eq!(list.get_strict(3),  Some(&6));
        assert_eq!(list.get_strict(12), Some(&24));
        assert_eq!(list.get_strict(2),  Some(&4));
        assert_eq!(list.get_strict(4),  Some(&8));
        assert_eq!(list.get_strict(9),  Some(&18));
        assert_eq!(list.get_strict(1),  Some(&2));
    }

    #[test]
    fn foldr_test() {
        let superand: ThunkList<bool> = (1..=100)
            .map_delayed(|i| {
                println!("initialized {i}");
                i % 29 != 0
            })
            .collect();

        let foldy = superand.foldr(
            |t, u| *t.force() && u.dethunk(), 
            ThunkAny::of(true)
        );
        assert!(!*foldy.force());

        let list: ThunkList<usize> = (1..=100).collect();

        let list2: ThunkList<_> = list.foldr(
            |acc, cv| ThunkList::cons(acc.unwrap_or_clone(), cv), 
            ThunkAny::of(ThunkList::new())
        ).into();

        assert!({
            list2.iter_strict()
                .copied()
                .eq(1..=100)
        }, "{list2:?} != {:?}", 1..=100);

        let list3: ThunkList<usize> = ThunkList::repeat(ThunkAny::of(0));
        let list4 = list3.foldr(
            |acc, cv| ThunkList::cons(acc.unwrap_or_clone(), cv), 
            ThunkAny::of(ThunkList::new())
        ).dethunk();

        let vec4 = take_nc(&list4, 25);
        assert_eq!(vec4, [0; 25]);
    }

    #[test]
    fn raw_append_test() {
        let mut list: ThunkList<usize> = (1..=15).collect();
        list = list.append(ThunkList::from([16, 17, 18]));

        assert!(list.iter_strict().copied().eq(1..=18), "{list:?} != {:?}", 1..=18);
    }

    #[test]
    fn split_test() {
        let list: ThunkList<usize> = (1..=15).collect();
        let (left, right) = list.split_at(4);
        assert!(left.iter_strict().copied().eq(1..=4), "{left:?} != {:?}", 1..=4);
        assert!(right.iter_strict().copied().eq(5..=15), "{right:?} != {:?}", 5..=15);

        let list: ThunkList<usize> = (1..=15).collect();
        let list = list.insert(4, ThunkAny::of(100));
        assert_eq!(take_nc(&list, 16), [1, 2, 3, 4, 100, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);

        let list = ThunkList::repeat(ThunkAny::of(0));
        let list = list.insert(10, ThunkAny::of(1));
        assert_eq!(take_nc(&list, 25), 
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        );
    }

    #[test]
    fn len_test() {
        // let a = 0:a;
        let list01 = ThunkList::repeat(ThunkAny::of(0));
        assert_eq!(list01.list_len(), (0, 1));

        // let b = 3:2:1:0:b;
        let (ptr, list) = ThunkList::tailed();
        let list04 = ThunkList::from(([3, 2, 1, 0], list));
        ptr.bind(&list04);
        assert_eq!(list04.list_len(), (0, 4));
        
        // let c = 4:5:6:b;
        let list34 = ThunkList::from(([4, 5, 6], list04));
        assert_eq!(list34.list_len(), (3, 4));
        
        // let d = [0, 1, 2, 3];
        let list40 = ThunkList::from_iter(0..4);
        assert_eq!(list40.list_len(), (4, 0));
        
        // let e = [];
        let list00 = ThunkList::from_iter(0..0);
        assert_eq!(list00.list_len(), (0, 0));
        
        let list50 = list01.split_at(4).0.append([1].into());
        assert_eq!(list50.list_len(), (5, 0));
        
        // this tests adding extra els, which aren't the same ref 
        // and can't be considered the same.
        let (ptr, list) = ThunkList::tailed();
        let list04a = ThunkList::from(([3, 2, 1, 0], list));
        ptr.bind(&list04a);
        let list04a = ThunkList::from(([3, 2, 1, 0], list04a));
        assert_eq!(list04a.list_len(), (4, 4));
    }
    
    #[test]
    fn eq_test() {
        // let a1 = 0:a1;
        // let a2 = 0:a2;
        // a1 == a2
        let list01a = ThunkList::repeat(ThunkAny::of(0));
        let list01b = ThunkList::repeat(ThunkAny::of(0));
        assert_eq!(list01a, list01b);
        
        // let b = 1:b;
        // a1 != b
        let list01c = ThunkList::repeat(ThunkAny::of(1));
        assert_ne!(list01a, list01c);
        
        // let c = 1:a1;
        // a2 != c
        // b != c
        let list11a = ThunkList::cons_known(1, list01a);
        assert_ne!(list01b, list11a);
        assert_ne!(list01c, list11a);
        
        // let d = 1:a2;
        // c == d
        let list11b = ThunkList::cons_known(1, list01b);
        assert_eq!(list11a, list11b);

        // add extra elements on one side, remove extra elements on the other, what happens?
        let (ptr, list) = ThunkList::tailed();
        let list03a = ThunkList::from(([3, 2, 1, 0], list));
        ptr.bind(&list03a);
        
        let (_, right) = list03a.clone().split_at(1);
        let list03b = ThunkList::cons_known(3, right);
        assert_eq!(list03a.list_len(), (0, 4));
        assert_eq!(list03b.list_len(), (1, 4));
        assert_eq!(list03a, list03b);

        // long
        let (ptr, list) = ThunkList::tailed();
        let list03a = ThunkList::from(([2, 1, 0], list));
        ptr.bind(&list03a);
        let (ptr, list) = ThunkList::tailed();
        let list03b = ThunkList::from(([2, 1, 0, 2, 1, 0], list));
        ptr.bind(&list03b);

        assert_eq!(list03a.list_len(), (0, 3));
        assert_eq!(list03b.list_len(), (0, 6));
        assert_eq!(list03a, list03b);
    }
}