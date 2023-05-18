pub mod tuple;
pub mod transform;
pub mod list;
mod cell;
use cell::{TakeCell, CovOnceCell};
pub use transform::zip;

use std::cell::{OnceCell, Cell};
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ptr::NonNull;

pub trait Thunkable {
    type Item;
    fn resolve(self) -> Self::Item;

    fn into_thunk(self) -> Thunk<Self> 
        where Self: Sized
    {
        Thunk::new(self)
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
    fn into_box<'a>(self) -> ThunkBox<'a, Self::Item> 
        where Self: Sized + 'a
    {
        ThunkBox::new(self)
    }
}
impl<T, F: FnOnce() -> T> Thunkable for F {
    type Item = T;

    fn resolve(self) -> Self::Item {
        self()
    }
}

struct ThunkInner<T, F> {
    inner: OnceCell<T>,
    init: Cell<Option<F>>
}
impl<T, F> ThunkInner<T, F> {
    fn uninitialized(f: F) -> Self {
        ThunkInner { inner: OnceCell::new(), init: Cell::new(Some(f)) }
    }
    fn initialized(t: T) -> Self {
        ThunkInner { inner: OnceCell::from(t), init: Cell::new(None) }
    }

    fn force(&self, r: impl FnOnce(F) -> T) -> &T {
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
    fn set(&self, val: T) -> Result<(), T> {
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
            init: match self.init.take() {
                Some(t) => {
                    let tc = t.clone();
                    self.init.replace(Some(t));
                    Cell::new(Some(tc))
                },
                None => Cell::new(None),
        } }
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
pub struct Thunk<F: Thunkable> {
    inner: ThunkInner<F::Item, F>
}
impl<T> Thunk<fn() -> T> {
    pub fn undef() -> Self {
        Thunk::new(|| panic!("undef"))
    }
    pub fn of(t: T) -> Self {
        Thunk::known(t)
    }
}
impl<F: Thunkable> Thunk<F> {
    pub fn new(f: F) -> Self {
        Thunk { inner: ThunkInner::uninitialized(f) }
    }
    pub fn known(t: F::Item) -> Self {
        Thunk { inner: ThunkInner::initialized(t) }
    }
    pub fn force(&self) -> &F::Item {
        self.inner.force(|f| f.resolve())
    }
    pub fn force_mut(&mut self) -> &mut F::Item {
        self.force();
        self.try_get_mut().expect("force should have succeeded")
    }
    pub fn dethunk(self) -> F::Item {
        self.force();
        self.try_into_inner().expect("force should have succeeded")
    }

    pub fn set(&self, val: F::Item) -> Result<(), F::Item> {
        self.inner.set(val)
    }
    pub fn is_initialized(&self) -> bool {
        self.inner.is_initialized()
    }

    pub fn boxed<'a>(self) -> ThunkAny<'a, F::Item>
        where F: 'a
    {
        let inner = CovOnceCell::new();
        // SAFETY: lifetime matches lifetime on init
        if let Some(val) = self.inner.inner.into_inner() {
            unsafe {
                inner.set(val)
                    .ok()
                    .expect("CovOnceCell should not have been initialized");
            }
        };

            let init = TakeCell::new(
                self.inner.init
                    .into_inner()
                    .map(Thunkable::into_box)
            );
            
            ThunkAny { inner, init }
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
impl<F: Thunkable> Thunkable for Thunk<F> {
    type Item = F::Item;

    fn resolve(self) -> Self::Item {
        self.dethunk()
    }
}
impl<'a, F: Thunkable> Thunkable for &'a Thunk<F> {
    type Item = &'a F::Item;

    fn resolve(self) -> Self::Item {
        self.force()
    }
}
impl<'a, F: Thunkable> Thunkable for &'a mut Thunk<F> {
    type Item = &'a mut F::Item;

    fn resolve(self) -> Self::Item {
        self.force_mut()
    }
}
impl<F: Thunkable> std::fmt::Debug for Thunk<F> 
    where F::Item: std::fmt::Debug
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Thunk")
            .field("inner", &self.inner.inner)
            .field("init", &"..")
            .finish()
    }
}
impl<T: Default> Default for Thunk<fn() -> T> {
    fn default() -> Self {
        Thunk::new(Default::default)
    }
}
// impl<'a, T: Default + 'a> Default for ThunkAny<'a, T> {
//     fn default() -> Self {
//         Thunk::<fn() -> T>::default().boxed()
//     }
// }
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
/// Unlike `Box<dyn Thunkable>`, this struct allows [`Thunkable::resolve`] to be called.
/// 
/// This type still internally uses a `dyn Trait`, so the same warnings about `dyn Trait`
/// apply when considering using this type.
pub struct ThunkBox<'a, T>(NonNull<dyn ThunkDrop<Item=()> + 'a>, PhantomData<&'a T>);

impl<'a, T> ThunkBox<'a, T> {
    fn new<F: Thunkable<Item=T> + 'a>(f: F) -> Self {
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
    /// ptr should not be used afterwards
    #[allow(clippy::wrong_self_convention)]
    unsafe fn to_tdbox(&mut self) -> Box<dyn ThunkDrop<Item=T> + 'a> {
        // SAFETY: ptr came from Box during initialization
        unsafe { Box::from_raw(self.0.as_ptr() as *mut dyn ThunkDrop<Item=T>) }
    }
    fn into_thunk_a(self) -> ThunkAny<'a, T> {
        ThunkAny::new(self)
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
            let _ = self.to_tdbox();
        }
    }
}

// #[derive(Clone)]
pub struct ThunkAny<'a, T> {
    inner: CovOnceCell<T, 32>, // this is invalid
    init: TakeCell<ThunkBox<'a, T>, 16>
}
impl<'a, T> ThunkAny<'a, T> {
    pub fn undef() -> Self {
        ThunkAny::new((|| panic!("undef")).into_box())
    }
    pub fn new(f: ThunkBox<'a, T>) -> Self {
        ThunkAny { 
            inner: CovOnceCell::new(),
            init: TakeCell::new(Some(f))
        }
    }
    pub fn of(t: T) -> Self {
        let inner = CovOnceCell::new();
        unsafe {
            inner.set(t) // <-- same lifetime as inner, therefore safe
                .ok()
                .expect("CovOnceCell should not have been initialized");
        }
        let init = TakeCell::new(None);

        ThunkAny { inner, init }
    }
    pub fn force(&self) -> &T {
        // SAFETY: cov met because T, 
        // ThunkBox have matching variances in initialization
        unsafe {
            self.inner.get_or_init(|| match self.init.take() {
                Some(f) => f.resolve(),
                None => panic!("no initializer")
            })
        }
    }
    pub fn force_mut(&mut self) -> &mut T {
        self.force();
        self.try_get_mut().expect("force should have succeeded")
    }
    pub fn dethunk(self) -> T {
        self.force();
        self.try_into_inner().expect("force should have succeeded")
    }

    /// # Safety
    /// 
    /// This function has to meet covariance. Type `T`'s lifetime should
    /// match the lifetime at initialization of this `ThunkAny`.
    pub unsafe fn set(&self, val: T) -> Result<(), T> {
        self.inner.set(val)
    }
    pub fn is_initialized(&self) -> bool {
        self.inner.get().is_some()
    }

    pub fn try_get(&self) -> Option<&T> {
        self.inner.get()
    }
    pub fn try_get_mut(&mut self) -> Option<&mut T> {
        self.inner.get_mut()
    }
    pub fn try_into_inner(self) -> Option<T> {
        self.inner.into_inner()
    }
}
impl<'a, T> Thunkable for ThunkAny<'a, T> {
    type Item = T;

    fn resolve(self) -> Self::Item {
        self.dethunk()
    }
}
impl<'a, T> Thunkable for &'a ThunkAny<'a, T> {
    type Item = &'a T;

    fn resolve(self) -> Self::Item {
        self.force()
    }
}
impl<'a, T> Thunkable for &'a mut ThunkAny<'a, T> {
    type Item = &'a mut T;

    fn resolve(self) -> Self::Item {
        self.force_mut()
    }
}
impl<'a, T: std::fmt::Debug> std::fmt::Debug for ThunkAny<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ThunkAny")
            .field("inner", &self.inner.get())
            .field("init", &"..")
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use crate::transform::Seq;
    use crate::{Thunk, Thunkable};

    #[test]
    fn thunky() {
        let x = Thunk::new(|| {
            println!("initialized x");
            2u32
        });
        let y = Thunk::new(|| {
            println!("initialized y");
            3u32
        });
        let y = vec![
            (&x).map(|t| t + 14).into_box(),
            (&x).cloned().into_box(),
            (&y).cloned().into_box(),
            (&x).cloned().into_box(),
        ];
        let z = Thunk::new(|| {
                y.into_iter()
                    .map(|b| b.resolve())
                    .collect::<Vec<_>>()
            })
            .into_thunk();

        let xy = (&x).map(|t| t + 1).into_thunk();
        let _ = x.set(13);
        println!("{:?}", xy.force());
        println!("{:?}", z.force());
    }

    #[test]
    fn doubler() {
        let x = Thunk::new(|| dbg!(false));
        let y = Thunk::undef();
        let w = (&x).zip(&y)
            .map(|(x, y)| *x.resolve() && *y.resolve())
            .map(|t| !t);
        println!("{}", w.into_thunk().force());
    }
    #[test]
    fn time_travel() {
        let y = Thunk::undef();
        let m = vec![1, 2, 4, 5, 9, 7, 4, 1, 2, 329, 23, 23, 21, 123, 123, 0, 324];
        let (m, it) = m.into_iter()
            .fold((vec![], 0), |(mut vec, r), t| {
                vec.push(&y);
                (vec, r.max(t))
            });
        y.set(it).ok().unwrap();
        let m: Vec<_> = m.into_iter()
            .map(Thunk::force)
            .copied()
            .collect();
        println!("{m:?}");
    }

    #[test]
    fn newthunk() {
        let x = Thunk::new(|| dbg!(2));
        let y = Thunk::new(|| dbg!(3));

        println!("creating thunk sum");
        let sum = Seq(&x, &y)
            .map(|(x, y)| x + y)
            .inspect(|_| println!("loaded thunk sum"))
            .into_thunk();
        println!("created thunk sum");
        println!("{}", sum.force());

        let z = Thunk::new(|| dbg!(true));
        let w = Thunk::undef();
        let res = (&z).zip(&w)
            .zip(&w)
            .map(|(l, r, c)| *l.force() || *r.force() || *c.force())
            .inspect(|_| println!("loaded result"))
            .into_thunk();
        println!("{}", res.force());
    }
}