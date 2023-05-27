pub mod tuple;
pub mod transform;
pub mod list;
mod cell;
pub mod iter;
use cell::{TakeCell, CovOnceCell};
pub use transform::zip;

use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ptr::NonNull;
use std::rc::Rc;

pub trait Thunkable {
    type Item;
    fn resolve(self) -> Self::Item;

    fn into_thunk(self) -> Thunk<Self::Item, Self> 
        where Self: Sized
    {
        Thunk::new(self)
    }
    fn into_box<'a>(self) -> ThunkBox<'a, Self::Item> 
        where Self: Sized + 'a
    {
        ThunkBox::new(self)
    }
    fn into_thunk_any<'a>(self) -> ThunkAny<'a, Self::Item> 
        where Self: Sized + 'a
    {
        self.into_thunk().boxed()
    }

    fn map<U, F: FnOnce(Self::Item) -> U>(self, f: F) -> transform::Map<Self, F> 
        where Self: Sized
    {
        transform::Map(self, f)
    }
    fn and_then<U: Thunkable, F: FnOnce(Self::Item) -> U>(self, f: F) -> transform::AndThen<Self, F> 
        where Self: Sized
    {
        transform::AndThen(self, f)
    }
    fn flatten(self) -> transform::Flatten<Self> 
        where Self: Sized,
              Self::Item: Thunkable
    {
        transform::Flatten(self)
    }
    fn cloned<'a, T: 'a + Clone>(self) -> transform::Cloned<Self>
        where Self: Sized + Thunkable<Item=&'a T>,
    {
        transform::Cloned(self)
    }
    fn copied<'a, T: 'a + Copy>(self) -> transform::Copied<Self>
        where Self: Sized + Thunkable<Item=&'a T>,
    {
        transform::Copied(self)
    }
    fn inspect<I: FnOnce(&Self::Item)>(self, f: I) -> transform::Inspect<Self, I>
        where Self: Sized
    {
        transform::Inspect(self, f)
    }
    fn zip<B: Thunkable>(self, b: B) -> transform::ZipMap<(Self, B), ()>
        where Self: Sized
    {
        zip(self, b)
    }
    fn zip_map<U, B: Thunkable, F: FnOnce((Self, B)) -> U>(self, b: B, f: F) -> transform::ZipMap<(Self, B), F>
        where Self: Sized
    {
        transform::ZipMap((self, b), f)
    }
}
impl<T, F: FnOnce() -> T> Thunkable for F {
    type Item = T;

    fn resolve(self) -> Self::Item {
        self()
    }
}

struct ThunkInner<T, F> {
    inner: CovOnceCell<T>,
    init: TakeCell<F>
}
impl<T, F> ThunkInner<T, F> {
    fn uninitialized(f: F) -> Self {
        ThunkInner { inner: CovOnceCell::new(), init: TakeCell::new(f) }
    }
    fn initialized(t: T) -> Self {
        ThunkInner { inner: CovOnceCell::from(t), init: TakeCell::empty() }
    }

    /// # Safety
    /// 
    /// Value returned must match the lifetime this struct had when it was initialized.
    unsafe fn force(&self, r: impl FnOnce(F) -> T) -> &T {
        self.inner.get_or_init(|| match self.init.take() {
            Some(f) => r(f),
            None => panic!("no initializer"),
        })
    }

    fn get(&self) -> Option<&T> {
        self.inner.get()
    }
    fn get_mut(&mut self) -> Option<&mut T> {
        self.inner.get_mut()
    }
    fn into_inner(self) -> Option<T> {
        self.inner.into_inner()
    }

    /// # Safety
    /// 
    /// Set value must match the lifetime this struct had when it was initialized.
    unsafe fn set(&self, val: T) -> Result<(), T> {
        self.init.take();
        self.inner.set(val)
    }
    fn is_initialized(&self) -> bool {
        self.inner.get().is_some()
    }
}

impl<T: Clone, F: Clone> Clone for ThunkInner<T, F> {
    fn clone(&self) -> Self {
        Self { 
            inner: self.inner.clone(), 
            init: self.init.clone()
        }
    }
}
impl<T: std::fmt::Debug, F> std::fmt::Debug for ThunkInner<T, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ThunkInner")
            .field("inner", &self.inner)
            .field("init", &"..")
            .finish()
    }
}

#[derive(Clone)]
pub struct Thunk<T, F: Thunkable<Item=T>> {
    inner: ThunkInner<T, F>
}
impl<F: Thunkable> Thunk<F::Item, F> {
    pub fn new(f: F) -> Self {
        Thunk { inner: ThunkInner::uninitialized(f) }
    }
    pub fn of(t: F::Item) -> Self {
        Thunk { inner: ThunkInner::initialized(t) }
    }
    pub fn force(&self) -> &F::Item {
        // SAFETY: F's lifetime matches lifetime of this Thunk at initialization, 
        // so covariance is preserved
        unsafe {
            self.inner.force(|f| f.resolve())
        }
    }
    pub fn force_mut(&mut self) -> &mut F::Item {
        self.force();
        self.try_get_mut().expect("force should have succeeded")
    }
    pub fn dethunk(self) -> F::Item {
        self.force();
        self.try_into_inner().expect("force should have succeeded")
    }

    /// # Safety
    /// 
    /// Set value must match the lifetime this struct had when it was initialized.
    pub unsafe fn set_unchecked(&self, val: F::Item) -> Result<(), F::Item> {
        self.inner.set(val)
    }
    pub fn set(&self, val: F::Item) -> Result<(), F::Item> 
        where F::Item: 'static 
    {
        // Since F::Item is 'static, this value cannot be dropped before
        // the cell is dropped.
        unsafe {
            self.inner.set(val)
        }
    }
    pub fn is_initialized(&self) -> bool {
        self.inner.is_initialized()
    }

    pub fn boxed<'a>(self) -> ThunkAny<'a, F::Item>
        where F: 'a
    {
        let ThunkInner { inner, init } = self.inner;
        Thunk {
            inner: ThunkInner {
                inner,
                init: TakeCell::from(init.take().map(Thunkable::into_box))
            }
        }
    }
    /// If the Rc is known to only be referenced once, this can be used
    /// to unwrap and dethunk the Rc.
    pub fn unwrap_dethunk(self: Rc<Self>) -> F::Item {
        match Rc::try_unwrap(self) {
            Ok(thunk) => !thunk,
            Err(e) => panic!("couldn't unwrap Rc, has {} references", Rc::strong_count(&e)),
        }
    }
    pub fn dethunk_or_clone(self: Rc<Self>) -> F::Item 
        where F::Item: Clone
    {
        match Rc::try_unwrap(self) {
            Ok(t) => t.dethunk(),
            Err(e) => e.force().clone(),
        }
    }

    pub fn try_get(&self) -> Option<&F::Item> {
        self.inner.get()
    }
    pub fn try_get_mut(&mut self) -> Option<&mut F::Item> {
        self.inner.get_mut()
    }
    pub fn try_into_inner(self) -> Option<F::Item> {
        self.inner.into_inner()
    }
}
impl<F: Thunkable> PartialEq for Thunk<F::Item, F> 
    where F::Item: PartialEq
{
    /// This function will resolve the thunks and checks if they are equal.
    fn eq(&self, other: &Self) -> bool {
        self.force() == other.force()
    }
}
impl<F: Thunkable> Eq for Thunk<F::Item, F> 
    where F::Item: Eq
{}
impl<F: Thunkable> PartialOrd for Thunk<F::Item, F>
    where F::Item: PartialOrd
{
    /// This function will resolve the thunks and compare them.
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.force().partial_cmp(other.force())
    }
}
impl<F: Thunkable> Ord for Thunk<F::Item, F>
    where F::Item: Ord
{
    /// This function will resolve the thunks and compare them.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.force().cmp(other.force())
    }
}

impl<F: Thunkable> Thunkable for Thunk<F::Item, F> {
    type Item = F::Item;

    fn resolve(self) -> Self::Item {
        self.dethunk()
    }
    fn into_thunk_any<'a>(self) -> ThunkAny<'a, Self::Item> 
            where Self: 'a 
    {
        self.boxed()
    }
}
impl<'a, F: Thunkable> Thunkable for &'a Thunk<F::Item, F> {
    type Item = &'a F::Item;

    fn resolve(self) -> Self::Item {
        self.force()
    }
}
impl<'a, F: Thunkable> Thunkable for &'a mut Thunk<F::Item, F> {
    type Item = &'a mut F::Item;

    fn resolve(self) -> Self::Item {
        self.force_mut()
    }
}
impl<F: Thunkable> std::ops::Not for Thunk<F::Item, F> {
    type Output = F::Item;

    /// Resolves a thunk.
    /// 
    /// This syntax is inspired by the strict use of `!` in Haskell.
    fn not(self) -> Self::Output {
        self.dethunk()
    }
}
impl<'a, F: Thunkable> std::ops::Not for &'a Thunk<F::Item, F> {
    type Output = &'a F::Item;

    /// Resolves a thunk.
    /// 
    /// This syntax is inspired by the strict use of `!` in Haskell.
    fn not(self) -> Self::Output {
        self.force()
    }
}
impl<'a, F: Thunkable> std::ops::Not for &'a mut Thunk<F::Item, F> {
    type Output = &'a mut F::Item;

    /// Resolves a thunk.
    /// 
    /// This syntax is inspired by the strict use of `!` in Haskell.
    fn not(self) -> Self::Output {
        self.force_mut()
    }
}
impl<F: Thunkable> std::fmt::Debug for Thunk<F::Item, F> 
    where F::Item: std::fmt::Debug
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Thunk")
            .field("inner", &self.inner.inner)
            .field("init", &"..")
            .finish()
    }
}

pub type ThunkFn<T> = Thunk<T, fn() -> T>;
impl<T> ThunkFn<T> {
    pub fn undef() -> Self {
        Thunk::new(|| panic!("undef"))
    }
}
impl<T: Default> Default for ThunkFn<T> {
    fn default() -> Self {
        Thunk::new(Default::default)
    }
}
impl<T> From<T> for Thunk<T, transform::Known<T>> {
    fn from(value: T) -> Self {
        Thunk::of(value)
    }
}

/// Similar to Thunkable but using a &mut self binding.
/// The ThunkDrop object should not be used afterwards.
trait ThunkDrop {
    type Item;
    fn drop_resolve(&mut self) -> Self::Item;
}
impl<F: Thunkable> ThunkDrop for Option<F> {
    type Item = F::Item;

    fn drop_resolve(&mut self) -> Self::Item {
        self.take()
            .expect("Thunkable was already dropped")
            .resolve()
    }
}

/// This struct should be used in situations where a `Box<dyn Thunkable>` is needed.
/// Unlike `Box<dyn Thunkable>`, this struct allows [`Thunkable::resolve`] to be called,
/// and is covariant over 'a and T.
/// 
/// This type still internally uses a `dyn Trait`, so the same warnings about `dyn Trait`
/// apply when considering using this type.
pub struct ThunkBox<'a, T>(NonNull<dyn ThunkDrop<Item=()> + 'a>, PhantomData<&'a T>);

impl<'a, T> ThunkBox<'a, T> {
    pub fn new<F: Thunkable<Item=T> + 'a>(f: F) -> Self {
        let ptr = unsafe {
            let p = Box::into_raw(Box::new(Some(f)))
                as *mut dyn ThunkDrop<Item=T>
                as *mut dyn ThunkDrop<Item=()>;

            // SAFETY: ptr came from Box, cannot be null
            NonNull::new_unchecked(p)
        };
        
        ThunkBox(ptr, PhantomData)
    }

    /// # Safety
    /// 
    /// ThunkBox's ptr should not be used afterwards
    #[allow(clippy::wrong_self_convention)]
    unsafe fn to_tdbox(&mut self) -> Box<dyn ThunkDrop<Item=T> + 'a> {
        // SAFETY: ptr came from Box during initialization
        unsafe { Box::from_raw(self.0.as_ptr() as *mut dyn ThunkDrop<Item=T>) }
    }
}
impl<'a, T> Thunkable for ThunkBox<'a, T> {
    type Item = T;

    fn resolve(self) -> Self::Item {
        // SAFETY: ManuallyDrop => destructor not called, so this is last action
        unsafe {
            ManuallyDrop::new(self)
                .to_tdbox()
                .drop_resolve()
        }
    }
    fn into_box<'b>(self) -> ThunkBox<'b, Self::Item> 
            where Self: 'b {
        self
    }
}
impl<'a, T> Drop for ThunkBox<'a, T> {
    fn drop(&mut self) {
        // SAFETY: Nothing happens after drop.
        unsafe {
            std::mem::drop(self.to_tdbox());
        }
    }
}

/// A wrapper that ignores differences between Thunk initializers.
pub type ThunkAny<'a, T> = Thunk<T, ThunkBox<'a, T>>;

impl<'a, T> ThunkAny<'a, T> {
    pub fn undef() -> Self {
        (|| panic!("undef")).into_thunk_any()
    }
    pub fn fix(f: fn(ThunkAny<'a, T>) -> T) -> ThunkAny<'a, T> {
        (move || f(Self::fix(f))).into_thunk_any()
    }
}
impl<'a, T: Clone> ThunkAny<'a, T> {
    pub fn unwrap_or_clone(self: Rc<Self>) -> Self {
        match Rc::try_unwrap(self) {
            Ok(t) => t,
            Err(e) => (move || e.force().clone()).into_thunk_any(),
        }
    }
}
impl<'a, T: Default + 'a> Default for ThunkAny<'a, T> {
    fn default() -> Self {
        (Default::default).into_thunk_any()
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::rc::Rc;

    use crate::iter::ThunkItertools;
    use crate::transform::Seq;
    use crate::{Thunk, Thunkable, ThunkFn};

    /// Creates a Thunk with a const value and a cell that indicates how many times that
    /// the initializer function has been initialized.
    /// 
    /// If things go right, the Cell should only ever hold a 0 or a 1.
    fn init_thunk<T>(t: T) -> (Rc<Cell<usize>>, Thunk<T, impl Thunkable<Item=T>>) {
        init_inspect(Thunk::from(t))
    }
    fn init_inspect<F: Thunkable>(t: Thunk<F::Item, F>) -> (Rc<Cell<usize>>, Thunk<F::Item, impl Thunkable<Item=F::Item>>) {
        let cell = Rc::new(Cell::new(0));
        let cell2 = Rc::clone(&cell);

        let thunk = t.inspect(move |_| cell.set(cell.get() + 1))
            .into_thunk();

        (cell2, thunk)
    }
    #[test]
    fn thunky() {
        let (x_init, x) = init_thunk(2);
        let (y_init, y) = init_thunk(3);
        
        assert_eq!(x_init.get(), 0);
        assert_eq!(y_init.get(), 0);

        let list = vec![
            (&x).map(|t| t + 14).into_thunk_any(),
            (&x).cloned().into_thunk_any(),
            (&y).cloned().into_thunk_any(),
            (&x).cloned().into_thunk_any(),
        ];
        let list2 = Thunk::new(|| {
            list.into_iter()
                .resolved()
                .collect::<Vec<_>>()
        });

        assert_eq!(x_init.get(), 0);
        assert_eq!(y_init.get(), 0);

        let xy = (&x).map(|t| t + 1).into_thunk();
        let _ = x.set(13);

        assert_eq!(!xy, 14);
        assert_eq!(!list2, [27, 13, 3, 13]);

        assert_eq!(x_init.get(), 0);
        assert_eq!(y_init.get(), 1);
    }

    #[test]
    fn sequer_zipper() {
        // seq
        let (x_init, x) = init_thunk(14);
        let (y_init, y) = init_thunk(25);
        
        let seq = Seq(&x, &y)
            .map(|(x, y)| x + y)
            .into_thunk();

        assert_eq!(!seq, 39);
        assert_eq!(x_init.get(), 1);
        assert_eq!(y_init.get(), 1);

        let (x_init, x) = init_thunk(false);
        let (y_init, y) = init_inspect(ThunkFn::undef());

        // zip2
        let zip = (&x).zip(&y)
            .map(|(x, y)| *!x && *!y);
        
        assert!(!zip.resolve());
        assert_eq!(x_init.get(), 1);
        assert_eq!(y_init.get(), 0);
        
        // zip4
        let zip = (&x).zip(&y).zip(&y).zip(&y)
            .map(|(a, b, c, d)| *!a && *!b && *!c && *!d);
        assert!(!zip.resolve());
        assert_eq!(x_init.get(), 1);
        assert_eq!(y_init.get(), 0);
    }
    #[test]
    fn time_travel() {
        let y = ThunkFn::undef();
        let m = vec![1, 2, 4, 5, 9, 7, 4, 1, 2, 329, 23, 23, 21, 123, 123, 0, 324];
        
        let (m, it) = m.into_iter()
            .fold((vec![], 0), |(mut vec, r), t| {
                vec.push(&y);
                (vec, r.max(t))
            });
        y.set(it).ok().unwrap();

        let m: Vec<_> = m.into_iter()
            .forced()
            .copied()
            .collect();
        
        assert_eq!(m, [329; 17]);
    }
}