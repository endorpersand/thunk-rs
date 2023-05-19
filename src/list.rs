use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::rc::Rc;

use crate::{Thunkable, ThunkAny};

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

impl<'a, T> Node<'a, T> {
    pub fn tailed(val: Rc<ThunkAny<'a, T>>) -> (TailPtr<'a, T>, Node<'a, T>) {
        let tail = TailPtr::new();
        let node = Node { val, next: tail.as_node_ptr() };

        (tail, node)
    }
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

    /// Concats a thunk to the end of this list.
    pub fn cons(f: ThunkAny<'a, T>, this: Self) -> ThunkList<'a, T> {
        let node = Node {
            val: Rc::new(f),
            next: this.head,
        };

        ThunkList { head: NodePtr::from(node) }
    }
    /// Concats a value to the end of this list.
    pub fn cons_known(t: T, this: Self) -> ThunkList<'a, T> {
        ThunkList::cons(ThunkAny::of(t), this)
    }
    /// Constructs a list using two lazy parameters.
    pub fn cons_lazy(f: ThunkAny<'a, T>, this: ThunkAny<'a, Self>) -> ThunkList<'a, T> {
        let node = Node {
            val: Rc::new(f),
            next: NodePtr::from({
                    crate::ThunkBox::new(|| {
                    this.resolve().head.force().cloned()
                }).into_thunk_any()
            }),
        };

        ThunkList { head: NodePtr::from(node) }
    }
    /// A raw version of [`ThunkList::cons`].
    /// 
    /// If cons is considered to take in a head element and a tail list (`head : tail`),
    /// this function accepts the head element and returns a not-yet-defined tail 
    /// and the resultant `head : tail` list.
    /// 
    /// The tail can be set to a list via [`TailPtr::bind`].
    pub fn raw_cons(head: ThunkAny<'a, T>) -> (TailPtr<'a, T>, ThunkList<'a, T>) {
        let (tail, node) = Node::tailed(Rc::new(head));
        (tail, ThunkList { head: NodePtr::from(node) })
    }

    /// Adds a pointer to the end of the list.
    pub fn raw_append(self) -> (TailPtr<'a, T>, ThunkList<'a, T>) {
        fn insert_end<'a, T>(ptr: NodePtr<'a, T>, end: NodePtr<'a, T>) -> NodePtr<'a, T> {
            match ptr.into_inner() {
                Some(rc) => {
                    match rc.unwrap_or_clone().dethunk() {
                        Some(Node { val, next }) => {
                            NodePtr::from(
                                crate::ThunkBox::new(move || {
                                    Some(Node { val, next: insert_end(next, end)})
                                }).into_thunk_any()
                            )
                        },
                        None => end,
                    }
                },
                None => end,
            }
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
    pub fn last(&self) -> Option<&ThunkAny<T>> {
        self.iter().last()
    }
    /// Reverses the list.
    /// 
    /// This is a strict operation and will immediately reverse the entire list.
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
    /// Creates a list where the provided thunk element is repeated infinitely.
    pub fn repeat(f: ThunkAny<'a, T>) -> ThunkList<'a, T> {
        let (next, lst) = ThunkList::raw_cons(f);
        next.bind(&lst);
        
        lst
    }
    /// Splits the first element.
    /// 
    /// This is a strict operation and will immediately split the list.
    pub fn split_first(self) -> Option<(Rc<ThunkAny<'a, T>>, ThunkList<'a, T>)> {
        let node = match Rc::try_unwrap(self.head.into_inner()?) {
            Ok(t) => t.dethunk(),
            Err(e) => e.force().clone(),
        }?;

        let Node { val, next } = node;
        Some((val, ThunkList { head: next }))
    }

    fn raw_split_at(self, n: usize) -> (ThunkList<'a, T>, TailPtr<'a, T>, ThunkList<'a, T>) {
        let mut tail = TailPtr::new();
        let left = ThunkList { head: tail.as_node_ptr() };
        let mut right = self;

        for _ in 0..n {
            if let Some((val, rest)) = right.split_first() {
                right = rest;

                let (new_tail, node) = Node::tailed(val);
                tail.bind(&ThunkList { head: NodePtr::from(node) });
                tail = new_tail;
            } else {
                return (left, tail, ThunkList::new());
            }
        }

        (left, tail, right)
    }
    pub fn split_at(self, n: usize) -> (ThunkList<'a, T>, ThunkList<'a, T>) {
        let (left, ltail, right) = self.raw_split_at(n);
        ltail.close();
        (left, right)
    }
    pub fn insert(self, n: usize, t: ThunkAny<'a, T>) -> ThunkList<'a, T> {
        let (left, ltail, right) = self.raw_split_at(n);
        ltail.bind(&ThunkList::cons(t, right));
        left
    }
    pub fn foldr<U, F>(self, f: F, base: ThunkAny<'a, U>) -> ThunkAny<'a, U> 
        where F: FnMut(Rc<ThunkAny<'a, T>>, ThunkAny<'a, U>) -> U + Copy + 'a
    {
        fn foldr_node<'a, T, U, F>(nptr: NodePtr<'a, T>, mut f: F, base: ThunkAny<'a, U>) -> ThunkAny<'a, U>
            where F: FnMut(Rc<ThunkAny<'a, T>>, ThunkAny<'a, U>) -> U + Copy + 'a
        {
            match nptr.into_inner() {
                Some(rc) => {
                    crate::ThunkBox::new(move || {
                        match rc.unwrap_or_clone().dethunk() {
                            Some(node) => {
                                let Node { val, next } = node;
    
                                let rhs = foldr_node(next, f, base);
                                f(val, rhs)
                            },
                            None => base.dethunk()
                        }
                    }).into_thunk_any()
                },
                None => base,
            }
        }

        foldr_node(self.head, f, base)
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
    /// Gets the strict value at this index.
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
        match self.head.force() {
            Some(node) => find_cycle_len(node, |t| t.next.force(), |a, b| Rc::ptr_eq(&a.val, &b.val)),
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
    pub fn iterate(f: impl FnMut() -> Option<ThunkAny<'a, T>> + 'a) -> ThunkList<'a, T> {
        fn iterate_node<'a, T>(mut f: impl FnMut() -> Option<ThunkAny<'a, T>> + 'a) -> MaybeNode<'a, T> {
            crate::ThunkBox::new(|| {
                Some(Node {
                    val: Rc::new(f()?),
                    next: NodePtr::from(iterate_node(f))
                })
            }).into_thunk_any()
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
                next.close();

                lst
            }
            None => ThunkList::new()
        }
    }
    pub fn from_iter_lazy<I: IntoIterator<Item=ThunkAny<'a, T>> + 'a>(iter: I) -> ThunkList<'a, T> {
        let mut it = iter.into_iter();
        ThunkList::iterate(move || it.next())
    }
}
impl<'a, T: std::fmt::Debug> std::fmt::Debug for ThunkList<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.iter().map(ThunkAny::force))
            .finish()
    }
}

#[must_use = "unconsumed TailPtr leads to broken lists"]
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
    pub fn bind(self, l: &ThunkList<'a, T>) -> bool {
        let val = l.head.force().cloned();

        // SAFETY: LPtr is invariant over Node<'a, T>, 
        // so only pointers of same lifetime are allowed.
        unsafe {
            self.ptr.set(val).is_ok()
        }
    }
    pub fn close(self) -> bool {
        // SAFETY: None is not dependent on lifetime.
        unsafe {
            self.ptr.set(None).is_ok()
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
pub struct IterStrict<'r, T>(&'r NodePtr<'r, T>);
impl<'r, T> Iterator for IterStrict<'r, T> {
    type Item = &'r T;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.0.force()?;
        
        let val = node.val.force();
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
    use std::rc::Rc;

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
        assert_eq!(cit.next().map(|t| t.unwrap_or_clone().dethunk()), Some(2));
        assert_eq!(cit.next().map(|t| t.unwrap_or_clone().dethunk()), Some(1));
        assert_eq!(cit.next().map(|t| t.unwrap_or_clone().dethunk()), Some(0));
        assert_eq!(cit.next().map(|t| t.unwrap_or_clone().dethunk()), None);
    }

    #[test]
    fn raw_cons_test() {
        {
            const N: usize = 13;
            let lst = ThunkList::repeat(ThunkAny::of(N)); // [N, ...]
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
    
            let lst = ThunkList::from(([3, 2, 1], lst2.clone()));
            next.bind(&lst);
            
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
                crate::ThunkBox::new(move || {
                    println!("initialized {i}");
                    i * 2
                }).into_thunk_any()
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
            .map(|i| {
                crate::ThunkBox::new(move || {
                    println!("initialized {i}");
                    i % 29 != 0
                }).into_thunk_any()
            })
            .collect();

        let foldy = superand.foldr(
            |t, u| *t.force() && u.dethunk(), 
            ThunkAny::of(true)
        );
        assert!(!*foldy.force());

        let list: ThunkList<usize> = (1..=100).collect();

        let list2 = list.foldr(
            |acc, cv| ThunkList::cons_lazy(acc.unwrap_or_clone(), cv), 
            ThunkAny::of(ThunkList::new())
        );
        assert!({
            list2.force()
                .iter_strict()
                .copied()
                .eq(1..=100)
        }, "{list2:?} != {:?}", 1..=100);

        let list3: ThunkList<usize> = ThunkList::repeat(ThunkAny::of(0));
        let list4 = list3.foldr(
            |acc, cv| ThunkList::cons_lazy(acc.unwrap_or_clone(), cv), 
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
        let (next, list) = ThunkList::raw_cons(ThunkAny::of(0usize));
        let list04 = ThunkList::from(([3, 2, 1], list));
        next.bind(&list04);
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

        // this tests adding extra els, which aren't the same ref 
        // and can't be considered the same.
        let (next, list) = ThunkList::raw_cons(ThunkAny::of(0usize));
        let list04a = ThunkList::from(([3, 2, 1], list));
        next.bind(&list04a);
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
        let (next, list) = ThunkList::raw_cons(ThunkAny::of(0usize));
        let list03a = ThunkList::from(([3, 2, 1], list));
        next.bind(&list03a);
        
        let (_, right) = list03a.clone().split_at(1);
        let list03b = ThunkList::cons_known(3, right);
        assert_eq!(list03a.list_len(), (0, 4));
        assert_eq!(list03b.list_len(), (1, 4));
        assert_eq!(list03a, list03b);

        // long
        let (next, list) = ThunkList::raw_cons(ThunkAny::of(0usize));
        let list03a = ThunkList::from(([2, 1], list));
        next.bind(&list03a);
        let (next, list) = ThunkList::raw_cons(ThunkAny::of(0usize));
        let list03b = ThunkList::from(([2, 1, 0, 2, 1], list));
        next.bind(&list03b);

        assert_eq!(list03a.list_len(), (0, 3));
        assert_eq!(list03b.list_len(), (0, 6));
        assert_eq!(list03a, list03b);
    }
}