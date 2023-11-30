#![warn(missing_docs)]
//! A library for handling thunk (lazily-evaluated) values.
//! 
//! This is similar to `LazyCell`, but extends its functionality.
//! 
//! ```
//! # use thunk::Thunk;
//! # use thunk::ThunkAny;
//! # use thunk::Thunkable;
//! # use thunk::Seq;
//! # 
//! fn add<'a>(l: &'a ThunkAny<'a, &'a usize>, r: &'a ThunkAny<'a, &'a usize>) 
//!     -> Thunk<usize, impl Thunkable<Item = usize> + 'a> 
//! {
//!     Seq(l, r)
//!         .map(|(&l, &r)| l + r)
//!         .into_thunk()
//! }
//! 
//! let t = 10;
//! let a = Thunk::new(|| {
//! println!("initialized 10");
//! &t
//! }).into_thunk_any();
//! 
//! {
//!     let u = 20;
//!     let b = Thunk::new(|| {
//!         println!("initialized 20");
//!         &u
//!     }).into_thunk_any();
//! 
//!     assert_eq!(add(&a, &b).force(), &30);
//! }
//! 
//! assert_eq!(a.dethunk(), &10);
//! ```

pub mod concat;
pub mod transform;
pub mod list;
mod cell;
pub mod iter;
use cell::{TakeCell, CovOnceCell};

pub use transform::{zip, Seq};
pub use iter::ThunkItertools;
pub use list::ThunkList;

use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ptr::NonNull;
use std::rc::Rc;

/// This trait is applied to types that can be used to generate a value once.
/// 
/// These act as initializers for a thunk value in [`Thunk`].
/// These `Thunkable`s can also have special transformations applied to them,
/// similar to iterator transformers.
pub trait Thunkable {
    /// Type that this `Thunkable` generates.
    type Item;
    /// Initializes a new `Self::Item` from this initializer.
    fn resolve(self) -> Self::Item;

    /// Wraps this `Thunkable` into a [`Thunk`].
    fn into_thunk(self) -> Thunk<Self::Item, impl Thunkable<Item=Self::Item>> 
        where Self: Sized
    {
        Thunk::new(self)
    }
    /// Converts this Thunkable into a [`ThunkBox`].
    /// 
    /// This is a heap-allocated pointer to an initializer for `Self::Item`
    /// which does not preserve details about the initializer.
    /// 
    /// It is meant to be a drop-in replacement for `Box<dyn Thunkable>`.
    fn into_box<'a>(self) -> ThunkBox<'a, Self::Item> 
        where Self: Sized + 'a
    {
        ThunkBox::new(self)
    }
    /// Converts this `Thunkable` into a [`ThunkAny`].
    fn into_thunk_any<'a>(self) -> ThunkAny<'a, Self::Item> 
        where Self: Sized + 'a
    {
        self.into_thunk().boxed()
    }
    /// Maps a Thunkable's `Self::Item` to `U` by applying a mapper function
    /// once the Thunkable is resolved.
    fn map<U, F: FnOnce(Self::Item) -> U>(self, f: F) -> transform::Map<Self, F> 
        where Self: Sized
    {
        transform::Map(self, f)
    }
    /// Maps a Thunkable's `Self::Item` to `U::Item` by applying a mapper function
    /// and resolving the returned `Thunkable` once this `Thunkable` is resolved.
    fn and_then<U: Thunkable, F: FnOnce(Self::Item) -> U>(self, f: F) -> transform::AndThen<Self, F> 
        where Self: Sized
    {
        transform::AndThen(self, f)
    }
    /// Flattens a `Thunkable` which initializes another `Thunkable`.
    fn flatten(self) -> transform::Flatten<Self> 
        where Self: Sized,
              Self::Item: Thunkable
    {
        transform::Flatten(self)
    }
    /// Clones the initialized reference once this `Thunkable` is resolved.
    fn cloned<'a, T: 'a + Clone>(self) -> transform::Cloned<Self>
        where Self: Sized + Thunkable<Item=&'a T>,
    {
        transform::Cloned(self)
    }
    /// Copies the initialized reference once this `Thunkable` is resolved.
    fn copied<'a, T: 'a + Copy>(self) -> transform::Copied<Self>
        where Self: Sized + Thunkable<Item=&'a T>,
    {
        transform::Copied(self)
    }
    /// Applies an inspection function once this `Thunkable` is resolved.
    fn inspect<I: FnOnce(&Self::Item)>(self, f: I) -> transform::Inspect<Self, I>
        where Self: Sized
    {
        transform::Inspect(self, f)
    }
    /// Collects two `Thunkable`s into a tuple. 
    /// These can be resolved together with [`transform::ZipMap::map`].
    /// 
    /// More `Thunkable`s can be concatenated with [`transform::ZipMap::zip`].
    /// 
    /// Unlike [`Seq`], `zip` will not resolve all `Thunkable`s when the conjoining
    /// `Thunkable` is resolved.
    fn zip<B: Thunkable>(self, b: B) -> transform::ZipMap<(Self, B), ()>
        where Self: Sized
    {
        zip(self, b)
    }
    /// Collects two `Thunkable`s into a tuple and applies a mapper to both.
    /// 
    /// Unlike [`Seq`], `zip_map` will not resolve all `Thunkable`s when the conjoining
    /// `Thunkable` is resolved.
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
            None => panic!("thunk does not have initializer"),
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
    /// # Safety
    /// 
    /// Replacing thunk must match the lifetime this struct had when it was initialized.
    unsafe fn replace(&self, thunk: Self) -> Result<(), Self> {
        if !self.is_initialized() {
            let Self { inner, init } = thunk;

            if let Some(val) = inner.into_inner() {
                // SAFETY: user has to assert cov
                self.set(val)
                    .unwrap_or_else(|_| unreachable!());
            } else if let Some(init) = init.take() {
                // SAFETY: user has to assert cov
                self.init.replace(init);
            } else {
                panic!("replacing thunk cannot be initialized")
            }

            Ok(())
        } else {
            Err(thunk)
        }
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

/// A thunk value. 
/// This can either hold an initialized value or an initializer to initialize the value.
/// 
/// Unlike `LazyCell`, this value is covariant over T and F, enabling a few extended uses.
/// 
/// This value can be initialized without an initializer as well, using [`Thunk::set`].
/// However, once this value has been initialized it cannot be uninitialized.
#[derive(Clone)]
pub struct Thunk<T, F: Thunkable<Item=T>> {
    inner: ThunkInner<T, F>
}
impl<F: Thunkable> Thunk<F::Item, F> {
    /// Creates a new Thunk value that is lazily initialized.
    pub fn new(f: F) -> Self {
        Thunk { inner: ThunkInner::uninitialized(f) }
    }
    /// Creates a new Thunk value with an already resolved value.
    pub fn of(t: F::Item) -> Self {
        Thunk { inner: ThunkInner::initialized(t) }
    }

    /// Initializes the value and returns an immutable reference to the value.
    pub fn force(&self) -> &F::Item {
        // SAFETY: F's lifetime matches lifetime of this Thunk at initialization, 
        // so covariance is preserved
        unsafe {
            self.inner.force(|f| f.resolve())
        }
    }
    /// Initializes the value and returns a mutable reference to the value.
    pub fn force_mut(&mut self) -> &mut F::Item {
        self.force();
        self.try_get_mut().expect("force should have succeeded")
    }
    /// Initializes the value and returns a strict value out of it.
    pub fn dethunk(self) -> F::Item {
        self.force();
        self.try_into_inner().expect("force should have succeeded")
    }

    /// Initializes the thunk value with a known value.
    /// 
    /// If this thunk is already initialized, this will fail and return the argument.
    /// 
    /// # Safety
    /// For this to be safely used, the lifetime of the value to set must match
    /// the lifetime of this `Thunk` when it was initialized.
    /// It cannot simply match the value of the `Thunk`'s current lifetime in this scope.
    /// 
    /// Setting a value which has a shorter lifetime than the initialized value will
    /// result in dangling pointers.
    /// 
    /// If the set value is known to be `'static`, you can safely use [`Thunk::set`].
    pub unsafe fn set_unchecked(&self, val: F::Item) -> Result<(), F::Item> {
        self.inner.set(val)
    }

    /// Initializes the thunk value with a known value.
    /// 
    /// If this thunk is already initialized, this will fail and return the argument.
    pub fn set(&self, val: F::Item) -> Result<(), F::Item> 
        where F::Item: 'static 
    {
        // Since F::Item is 'static, this value cannot be dropped before
        // the cell is dropped.
        unsafe {
            self.inner.set(val)
        }
    }

    /// Replaces this thunk's initializer with another thunk's initializer.
    /// If this thunk is already initialized, this will fail and return the thunk.
    /// 
    /// # Safety
    /// For this to be safely used, the provided Thunk's lifetimes 
    /// (for the value type and initializer type) must match the lifetimes of this `Thunk`
    /// when it was initialized.
    /// It cannot simply match the value of the `Thunk`'s current lifetime in this scope.
    /// 
    /// Setting a value which has a shorter lifetime than the initialized value will
    /// result in dangling pointers.
    /// 
    /// If the new `Thunk` is known to have `'static` parameters, you can safely use [`Thunk::replace`].
    pub unsafe fn replace_unchecked(&self, thunk: Self) -> Result<(), Self> {
        self.inner.replace(thunk.inner)
            .map_err(|inner| Thunk { inner })
    }

    /// Replaces this thunk's initializer with another thunk's initializer.
    /// If this thunk is already initialized, this will fail and return the thunk.
    pub fn replace(&self, thunk: Self) -> Result<(), Self> 
        where F::Item: 'static, F: 'static
    {
        // Since F is 'static, this value cannot be dropped before
        // the cell is dropped.
        unsafe {
            self.replace_unchecked(thunk)
        }
    }
    /// Checks whether the Thunk has been initialized.
    pub fn is_initialized(&self) -> bool {
        self.inner.is_initialized()
    }
    /// Converts the initializer value into a [`ThunkBox`].
    /// 
    /// This is a heap-allocated pointer to an initializer for `Self::Item`
    /// which does not preserve details about the initializer.
    /// 
    /// It is meant to be a drop-in replacement for `Box<dyn Thunkable>`.
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
    /// For a `Rc<Thunk>`, this unwraps and dethunks the value.
    /// 
    /// If the Rc is referenced more than once, this will panic.
    pub fn unwrap_dethunk(self: Rc<Self>) -> F::Item {
        match Rc::try_unwrap(self) {
            Ok(thunk) => !thunk,
            Err(e) => panic!("couldn't unwrap Rc, has {} references", Rc::strong_count(&e)),
        }
    }
    /// For a `Rc<Thunk>` which has a clonable value type, this will initialize the value.
    /// If there is more than one reference to the given Rc, the value is cloned out of the thunk.
    pub fn dethunk_or_clone(self: Rc<Self>) -> F::Item 
        where F::Item: Clone
    {
        match Rc::try_unwrap(self) {
            Ok(t) => t.dethunk(),
            Err(e) => e.force().clone(),
        }
    }

    /// Returns an immutable reference to the inner value if it is initialized.
    pub fn try_get(&self) -> Option<&F::Item> {
        self.inner.get()
    }
    /// Returns a mutable reference to the inner value if it is initialized.
    pub fn try_get_mut(&mut self) -> Option<&mut F::Item> {
        self.inner.get_mut()
    }
    /// Consumes the thunk, returning the inner value if it is initialized.
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
    #[allow(refining_impl_trait)]
    fn into_thunk(self) -> Self {
        self
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

/// A thunk whose initializers are function pointers.
pub type ThunkFn<T> = Thunk<T, fn() -> T>;
impl<T> ThunkFn<T> {
    /// Creates a Thunk which panics when initialized.
    /// 
    /// Similar to Haskell bottom.
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
    /// Creates a new `ThunkBox` out of a [`Thunkable`].
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
    /// Creates a Thunk which panics when initialized.
    /// 
    /// Similar to Haskell bottom.
    pub fn undef() -> Self {
        ThunkFn::undef().boxed()
    }
    /// The fixed combinator.
    /// 
    /// This is a fixed point for a given function. For example:
    /// ```
    /// # use thunk::ThunkAny;
    /// assert_eq!(ThunkAny::fix(|_| 5).dethunk(), 5);
    /// 
    /// let t = ThunkAny::<Box<dyn FnOnce(usize) -> usize>>::fix(|f| {
    ///     Box::new(move |n| match n {
    ///         0 => 1,
    ///         n => f.dethunk()(n - 1) * n
    ///     })
    /// }).dethunk();
    /// assert_eq!(t(5), 120);
    /// ```
    /// 
    /// This is not very powerful (especially when considering the Haskell version)...
    /// but it's very fun
    pub fn fix(f: fn(ThunkAny<'a, T>) -> T) -> ThunkAny<'a, T> {
        (move || f(Self::fix(f))).into_thunk_any()
    }
}
impl<'a, T: Clone> ThunkAny<'a, T> {
    /// For an `Rc<Thunk>`, this unwraps the thunk 
    /// or creates a new Thunk which clones the value when it needs to initialize.
    pub fn unwrap_or_clone(self: Rc<Self>) -> Self {
        match Rc::try_unwrap(self) {
            Ok(t) => t,
            Err(rc) => (move || rc.dethunk_or_clone()).into_thunk_any(),
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