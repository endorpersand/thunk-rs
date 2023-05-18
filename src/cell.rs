#![allow(dead_code)]

use std::cell::UnsafeCell;
use std::convert::Infallible;
use std::fmt::Debug;
use std::mem::{ManuallyDrop, size_of};

/// Covariant version of UnsafeCell.
#[repr(C)]
pub(crate) union CovUnsafeCell<T, const T_SIZE: usize> {
    cell: ManuallyDrop<UnsafeCell<[u8; T_SIZE]>>,
    value: ManuallyDrop<T>
}

impl<T, const T_SIZE: usize> CovUnsafeCell<T, T_SIZE> {
    /// # Panics
    /// 
    /// Panics if `T_SIZE` < `size_of::<T>()`.
    /// This is necessary in order for the `*mut T` pointer from `.get` to safely
    /// access the stored value `T`.
    pub fn new(t: T) -> Self {
        assert!(
            T_SIZE >= size_of::<T>(), 
            "cell needed {} bytes for safe access, but it only got {T_SIZE} bytes",
            size_of::<T>()
        );
        CovUnsafeCell { value: ManuallyDrop::new(t) }
    }

    /// SAFETY: Same requirements as UnsafeCell, with the additional requirement
    /// that any changes made using this pointer must maintain covariance.
    /// 
    /// Possible ways of maintaining covariance include...
    /// - changes are only done prior to any downcast
    /// - changes are lifetime agnostic
    pub fn get(&self) -> *mut T {
        // SAFETY: If the pointer exceeds the size of `T`,
        // the UnsafeCell can access all of the space shared by `T`.
        unsafe { &self.cell }.get() as *mut T 
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
        UnsafeCell::raw_get(this as *const UnsafeCell<[u8; T_SIZE]>) as *mut T
    }
}
impl<T, const T_SIZE: usize> Debug for CovUnsafeCell<T, T_SIZE> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CovUnsafeCell")
            .finish_non_exhaustive()
    }
}
impl<T, const T_SIZE: usize> Drop for CovUnsafeCell<T, T_SIZE> {
    // SAFETY: Only way to init CovUnsafeCell is a value initialization
    fn drop(&mut self) {
        unsafe {
            ManuallyDrop::drop(&mut self.value)
        }
    }
}

/// Covariant version of OnceCell.
pub(crate) struct CovOnceCell<T, const OT_SIZE: usize> {
    inner: CovUnsafeCell<Option<T>, OT_SIZE>
}
impl<T, const OT_SIZE: usize> CovOnceCell<T, OT_SIZE> {
    /// # Panics
    /// 
    /// Panics if `OT_SIZE` < `size_of::<Option<T>>()`.
    /// This is necessary in order for this cell's operations to be valid.
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
impl<T: Debug, const OT_SIZE: usize> Debug for CovOnceCell<T, OT_SIZE> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.get() {
            Some(t) => f.debug_tuple("CovOnceCell").field(t).finish(),
            None => write!(f, "CovOnceCell(?)"),
        }
    }
}
impl<T: PartialEq, const OT_SIZE: usize> PartialEq for CovOnceCell<T, OT_SIZE> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}
impl<T: Eq, const OT_SIZE: usize> Eq for CovOnceCell<T, OT_SIZE> {}

/// A cell which holds a value which can be taken at any time with a immutable reference.
pub(crate) struct TakeCell<T, const OT_SIZE: usize> {
    inner: CovUnsafeCell<Option<T>, OT_SIZE>
}
impl<T, const OT_SIZE: usize> TakeCell<T, OT_SIZE> {
    /// # Panics
    /// 
    /// Panics if `OT_SIZE` < `size_of::<Option<T>>()`.
    /// This is necessary in order for this cell's operations to be valid.
    pub fn new(t: Option<T>) -> Self {
        TakeCell { inner: CovUnsafeCell::new(t) }
    }

    pub fn take(&self) -> Option<T> {
        // SAFETY: Covariance is maintained because taking can't
        // mutate a memory location with a lifetime dependent value
        //
        // There is no other way to read the data here, so we're fine.
        unsafe { &mut *self.inner.get() }.take()
    }
    pub fn get_mut(&mut self) -> Option<&mut T> {
        self.inner.get_mut().as_mut()
    }
    pub fn into_inner(self) -> Option<T> {
        self.inner.into_inner()
    }
}

/// Covariant version of LazyCell.
pub(crate) struct CovLazyCell<T, F, const OT_SIZE: usize, const OF_SIZE: usize> {
    inner: CovOnceCell<T, OT_SIZE>,
    init: TakeCell<F, OF_SIZE>
}

impl<T, F, const OT_SIZE: usize, const OF_SIZE: usize> CovLazyCell<T, F, OT_SIZE, OF_SIZE> 
    where F: FnOnce() -> T
{
    /// # Panics
    /// 
    /// Panics if `OT_SIZE` < `size_of::<Option<T>>()` or `OF_SIZE` < `size_of::<Option<F>>()`.
    /// This is necessary in order for this cell's operations to be valid.
    pub fn new(f: F) -> Self {
        CovLazyCell { inner: CovOnceCell::new(), init: TakeCell::new(Some(f)) }
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
#[cfg(test)]
mod tests {
    use std::marker::PhantomData;
    use std::mem::size_of;

    use super::CovUnsafeCell;
    
    #[derive(PartialEq, Eq, Debug)]
    struct Foo(usize);
    #[derive(PartialEq, Eq, Debug)]
    struct Fool<'a>(usize, PhantomData<&'a ()>);

    #[test]
    fn is_miri_happy() {
        unsafe {
            let z = CovUnsafeCell::<Foo, { size_of::<Foo>() }>::new(Foo(0));
            z.get().write(Foo(15));
            assert_eq!(*z.get(), Foo(15));
        }
    }

    #[test]
    fn is_miri_happy2() {
        fn write<T>(c: &CovUnsafeCell<T, 1>, t: T) {
            unsafe { c.get().write(t); }
        }

        let cell: CovUnsafeCell<i8, 1> = CovUnsafeCell { value: std::mem::ManuallyDrop::new(14) };
        write(&cell, 0);
        println!("{}", unsafe { &*cell.get() });
    }
}