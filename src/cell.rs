#![allow(dead_code)]

use std::cell::UnsafeCell;
use std::convert::Infallible;
use std::fmt::Debug;
use std::mem::ManuallyDrop;

/// Covariant version of [`UnsafeCell`][`std::cell::UnsafeCell`].
#[repr(C)]
pub(crate) union CovUnsafeCell<T> {
    value: ManuallyDrop<T>,
    cell: ManuallyDrop<UnsafeCell<()>>
}

impl<T> CovUnsafeCell<T> {
    /// Initializes a new `CovUnsafeCell` with the provided value.
    pub fn new(t: T) -> Self {
        CovUnsafeCell { value: ManuallyDrop::new(t) }
    }

    /// SAFETY: Same requirements as UnsafeCell, with the additional requirement
    /// that any changes made using this pointer must maintain covariance.
    /// 
    /// Possible ways of maintaining covariance include...
    /// - changes are only done prior to any downcast
    /// - changes are lifetime agnostic
    pub fn get(&self) -> *mut T {
        unsafe {
            // SAFETY: The space has an UnsafeCell in it, which indicates
            // that & optimizations are not applied.
            // Thus, this can be treated as an UnsafeCell<T>.
            let cell: &UnsafeCell<T> = std::mem::transmute(self);
            cell.get()
        }
    }
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: Since only way to init CovUnsafeCell is a value initialization,
        // we can access self.value.
        unsafe {
            &mut self.value
        }
    }
    pub fn into_inner(mut self) -> T {
        // SAFETY: Since only way to init CovUnsafeCell is a value initialization,
        // we can access self.value.
        let val = unsafe {
            ManuallyDrop::take(&mut self.value)
        };
        std::mem::forget(self);

        val
    }
    pub fn raw_get(this: *const Self) -> *mut T {
        UnsafeCell::raw_get(this as *const UnsafeCell<T>) as *mut T
    }
}
impl<T> Debug for CovUnsafeCell<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CovUnsafeCell")
            .finish_non_exhaustive()
    }
}
impl<T: Default> Default for CovUnsafeCell<T> {
    fn default() -> Self {
        CovUnsafeCell::new(Default::default())
    }
}
impl<T> From<T> for CovUnsafeCell<T> {
    fn from(value: T) -> Self {
        CovUnsafeCell::new(value)
    }
}
impl<T> Drop for CovUnsafeCell<T> {
    // SAFETY: Only way to init CovUnsafeCell is a value initialization
    fn drop(&mut self) {
        unsafe {
            ManuallyDrop::drop(&mut self.value)
        }
    }
}

/// Covariant version of [`OnceCell`][`std::cell::OnceCell`].
pub(crate) struct CovOnceCell<T> {
    inner: CovUnsafeCell<Option<T>>
}
impl<T> CovOnceCell<T> {
    /// Initializes a new empty `CovOnceCell`.
    pub fn new() -> Self {
        CovOnceCell { inner: CovUnsafeCell::new(None) }
    }
    pub fn get(&self) -> Option<&T> {
        // SAFETY: See OnceCell
        unsafe { &*self.inner.get() }.as_ref()
    }

    pub fn get_mut(&mut self) -> Option<&mut T> {
        self.inner.get_mut().as_mut()
    }

    /// # Safety
    /// 
    /// T must match the original lifetime of the cell 
    /// in order to maintain covariance.
    pub unsafe fn set(&self, t: T) -> Result<(), T> {
        match &*self.inner.get() {
            Some(_) => Err(t),
            None => {
                let r = &mut *self.inner.get();
                *r = Some(t);
                Ok(())
            },
        }
    }

    /// # Safety
    /// 
    /// T must match the original lifetime of the cell 
    /// in order to maintain covariance.
    pub unsafe fn get_or_init(&self, f: impl FnOnce() -> T) -> &T {
        self.get_or_try_init(|| Ok::<_, Infallible>(f()))
            .unwrap_unchecked()
    }

    /// # Safety
    /// 
    /// T must match the original lifetime of the cell 
    /// in order to maintain covariance.
    pub unsafe fn get_or_try_init<E>(&self, f: impl FnOnce() -> Result<T, E>) -> Result<&T, E> {
        match self.get() {
            Some(t) => Ok(t),
            None => {
                self.set(f()?).ok().expect("set operation should have succeeded");
                Ok(self.get().unwrap())
            },
        }
    }

    pub fn into_inner(self) -> Option<T> {
        self.inner.into_inner()
    }

    pub fn take(&mut self) -> Option<T> {
        self.inner.get_mut().take()
    }
}
impl<T: Debug> Debug for CovOnceCell<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.get() {
            Some(t) => f.debug_tuple("CovOnceCell").field(t).finish(),
            None => write!(f, "CovOnceCell(?)"),
        }
    }
}
impl<T> Default for CovOnceCell<T> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T: Clone> Clone for CovOnceCell<T> {
    fn clone(&self) -> Self {
        CovOnceCell { inner: CovUnsafeCell::new(self.get().cloned()) }
    }
}
impl<T> From<T> for CovOnceCell<T> {
    fn from(value: T) -> Self {
        CovOnceCell { inner: CovUnsafeCell::new(Some(value)) }
    }
}
impl<T: PartialEq> PartialEq for CovOnceCell<T> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}
impl<T: Eq> Eq for CovOnceCell<T> {}

/// A cell which only allows one read via immutable reference.
/// 
/// This cell is covariant over T.
pub(crate) struct TakeCell<T> {
    inner: CovUnsafeCell<Option<T>>
}
impl<T> TakeCell<T> {
    /// Initializes a new `TakeCell` with the provided value.
    pub fn new(t: T) -> Self {
        TakeCell::from(Some(t))
    }
    pub fn empty() -> Self {
        TakeCell::from(None)
    }
    pub fn take(&self) -> Option<T> {
        // SAFETY: 
        // - Covariance is maintained because taking can't
        // mutate a memory location with a lifetime dependent value
        // - Since we cannot have a reference to the inner value, 
        // mutation is allowed.
        unsafe { &mut *self.inner.get() }.take()
    }
    /// # Safety
    /// T being inserted into this function must meet covariance 
    /// (it must match the lifetime of this cell on initialization).
    pub unsafe fn replace(&self, t: T) -> Option<T> {
        // SAFETY: 
        // - User must verify covariance
        // - Since we cannot have a reference to the inner value, 
        // mutation is allowed.
        unsafe { &mut *self.inner.get() }.replace(t)
    }
    pub fn get_mut(&mut self) -> Option<&mut T> {
        self.inner.get_mut().as_mut()
    }
    pub fn into_inner(self) -> Option<T> {
        self.inner.into_inner()
    }
}
impl<T> From<Option<T>> for TakeCell<T> {
    fn from(value: Option<T>) -> Self {
        TakeCell { inner: CovUnsafeCell::new(value) }
    }
}
impl<T: Default> Default for TakeCell<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}
impl<T: Clone> Clone for TakeCell<T> {
    fn clone(&self) -> Self {
        Self::from(unsafe { &*self.inner.get() }.clone())
    }
}
/// Covariant version of LazyCell.
pub(crate) struct CovLazyCell<T, F> {
    inner: CovOnceCell<T>,
    init: TakeCell<F>
}

impl<T, F> CovLazyCell<T, F> 
    where F: FnOnce() -> T
{
    /// Creates a new `CovLazyCell` with the provided initializer.
    pub fn new(f: F) -> Self {
        CovLazyCell { inner: CovOnceCell::new(), init: TakeCell::new(f) }
    }

    pub fn force(&self) -> &T {
        // SAFETY: T and F were present at the creation of the cell,
        // so they must have compatible lifetimes
        unsafe {
            self.inner.get_or_init(|| match self.init.take() {
                Some(f) => f(),
                None => panic!("no initializer"),
            })

        }
    }
}
impl<T: Debug, F> Debug for CovLazyCell<T, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut tpl = f.debug_tuple("CovLazyCell");
        
        match self.inner.get() {
            Some(t) => tpl.field(t),
            None => tpl.field(&"?"),
        }.finish()
    }
}
#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::CovUnsafeCell;
    
    #[derive(PartialEq, Eq, Debug)]
    struct Foo(usize);
    #[derive(PartialEq, Eq, Debug)]
    struct Fool<'a>(usize, PhantomData<&'a ()>);

    #[test]
    fn is_miri_happy() {
        unsafe {
            let z = CovUnsafeCell::new(Foo(0));
            z.get().write(Foo(15));
            assert_eq!(*z.get(), Foo(15));
        }
    }

    #[test]
    fn is_miri_happy2() {
        fn write<T>(c: &CovUnsafeCell<T>, t: T) {
            unsafe { c.get().write(t); }
        }

        let cell: CovUnsafeCell<i8> = CovUnsafeCell::new(14);
        write(&cell, 0);
        println!("{}", unsafe { &*cell.get() });
    }
}