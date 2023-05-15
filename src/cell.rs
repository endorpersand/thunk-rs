#![allow(dead_code)]

use std::cell::UnsafeCell;
use std::convert::Infallible;
use std::mem::{ManuallyDrop, size_of};

#[repr(C)]
pub(crate) union CovUnsafeCell<T, const T_SIZE: usize> {
    cell: ManuallyDrop<UnsafeCell<[u8; T_SIZE]>>,
    value: ManuallyDrop<T>
}

impl<T> CovUnsafeCell<T, {size_of::<T>()}> {
    pub fn new(t: T) -> Self {
        unsafe { CovUnsafeCell::new_unchecked(t) }
    }
}
impl<T, const T_SIZE: usize> CovUnsafeCell<T, T_SIZE> {
    pub unsafe fn new_unchecked(t: T) -> Self {
        CovUnsafeCell { value: ManuallyDrop::new(t) }
    }
    /// SAFETY: Same requirements as UnsafeCell, with the additional requirement
    /// that any changes made using this pointer must maintain covariance.
    /// 
    /// Possible ways of maintaining covariance include...
    /// - changes are only done prior to any downcast
    /// - changes are lifetime agnostic
    pub fn get(&self) -> *mut T {
        // SAFETY: Only way to init CovUnsafeCell is a value initialization
        // So, UnsafeCell lends `size_of::<T>()` bytes in ptr-space
        unsafe { self.cell.get() as *mut T }
    }
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: Only way to init CovUnsafeCell is a value initialization
        unsafe {
            &mut self.value
        }
    }
    pub fn into_inner(mut self) -> T {
        // SAFETY: Only way to init CovUnsafeCell is a value initialization.
        // into_inner can't be used because we have a Drop impl.
        // We consumed the whole Cell, so `self.value` is no longer accessible.
        unsafe {
            ManuallyDrop::take(&mut self.value)
        }
    }
    pub fn raw_get(this: *const Self) -> *mut T {
        UnsafeCell::raw_get(this as *const UnsafeCell<[u8; T_SIZE]>) as *mut T
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
pub(crate) struct CovOnceCell<T, const OT_SIZE: usize> {
    inner: CovUnsafeCell<Option<T>, OT_SIZE>
}
impl<T> CovOnceCell<T, {size_of::<Option<T>>()}> {
    pub fn new() -> Self {
        CovOnceCell { inner: CovUnsafeCell::new(None) }
    }
}
impl<T, const N: usize> CovOnceCell<T, N> {
    pub fn get(&self) -> Option<&T> {
        // SAFETY: See OnceCell
        unsafe { &*self.inner.get() }.as_ref()
    }
    pub fn get_mut(&mut self) -> Option<&mut T> {
        self.inner.get_mut().as_mut()
    }
    /// SAFETY: This operation must maintain covariance.
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
    /// SAFETY: This operation must maintain covariance.
    pub unsafe fn get_or_init(&self, f: impl FnOnce() -> T) -> &T {
        self.get_or_try_init(|| Ok::<_, Infallible>(f())).unwrap_unchecked()
    }
    /// SAFETY: This operation must maintain covariance.
    pub unsafe fn get_or_try_init<E>(&self, f: impl FnOnce() -> Result<T, E>) -> Result<&T, E> {
        match self.get() {
            Some(t) => Ok(t),
            None => {
                self.set(f()?).ok().unwrap();
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

pub(crate) struct TakeCell<T, const OT_SIZE: usize> {
    inner: CovUnsafeCell<Option<T>, OT_SIZE>
}
impl<T> TakeCell<T, {size_of::<Option<T>>()}> {
    pub fn new(t: Option<T>) -> Self {
        unsafe {TakeCell::new_unchecked(t) }
    }
}
impl<T, const OT_SIZE: usize> TakeCell<T, OT_SIZE> {
    pub unsafe fn new_unchecked(t: Option<T>) -> Self {
        TakeCell { inner: CovUnsafeCell::new_unchecked(t) }
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

pub(crate) struct CovLazyCell<T, F, const OT_SIZE: usize, const OF_SIZE: usize> {
    inner: CovOnceCell<T, OT_SIZE>,
    init: TakeCell<F, OF_SIZE>
}
impl<T, F> CovLazyCell<T, F, { size_of::<Option<T>>() }, { size_of::<Option<F>>() }> 
    where F: FnOnce() -> T
{
    pub fn new(f: F) -> Self {
        CovLazyCell { inner: CovOnceCell::new(), init: TakeCell::new(Some(f)) }
    }
}
impl<T, F, const OT_SIZE: usize, const OF_SIZE: usize> CovLazyCell<T, F, OT_SIZE, OF_SIZE> 
    where F: FnOnce() -> T
{
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

    use super::{CovUnsafeCell, CovLazyCell};
    
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

        {
            let lazy = CovLazyCell::new(|| Fool(0, PhantomData));
            {
                let lazy2 = &lazy;
                println!("{:?}", CovLazyCell::force(lazy2));
            }
            CovLazyCell::force(&lazy);
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