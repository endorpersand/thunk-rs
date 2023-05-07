use std::cell::{OnceCell, Cell};

pub trait Thunkable {
    type Item;

    fn resolve(self) -> Self::Item;
    fn map<U, F: FnOnce(Self::Item) -> U>(self, f: F) -> Map<Self, F> 
        where Self: Sized
    {
        Map(self, f)
    }
    fn into_thunk(self) -> Thunk<Self> 
        where Self: Sized
    {
        Thunk::new(self)
    }
    fn cloned<'a, T: 'a + Clone>(self) -> Cloned<Self>
        where Self: Sized + Thunkable<Item=&'a T>,
    {
        Cloned(self)
    }
    fn copied<'a, T: 'a + Copy>(self) -> Copied<Self>
        where Self: Sized + Thunkable<Item=&'a T>,
    {
        Copied(self)
    }
    fn inspect<I: FnOnce(&Self::Item)>(self, f: I) -> Inspect<Self, I>
        where Self: Sized
    {
        Inspect(self, f)
    }
    fn zip<B: Thunkable>(self, b: B) -> ZipMap<Self, B, ()>
        where Self: Sized
    {
        zip(self, b)
    }
    fn zip_map<U, B: Thunkable, F: FnOnce(Self, B) -> U>(self, b: B, f: F) -> ZipMap<Self, B, F>
        where Self: Sized
    {
        ZipMap(self, b, f)
    }
}
impl<T> Thunkable for fn() -> T {
    type Item = T;

    fn resolve(self) -> Self::Item {
        self()
    }
}
impl<T: Thunkable, U: Thunkable> Thunkable for (T, U) {
    type Item = (T::Item, U::Item);

    fn resolve(self) -> Self::Item {
        (self.0.resolve(), self.1.resolve())
    }
}

pub struct Thunk<F: Thunkable> {
    inner: ThunkInner<F::Item, F>
}
impl<T> Thunk<fn() -> T> {
    pub fn undef() -> Self {
        Thunk::with(|| panic!("undef"))
    }
    pub fn known(t: T) -> Self {
        let thunk = Thunk::undef();
        thunk.set(t)
            .ok()
            .expect("Thunk::undef should have been uninitialized");
        thunk
    }
    pub fn with(f: fn() -> T) -> Self {
        Thunk::new(f)
    }
}
impl<F: Thunkable> Thunk<F> {
    pub fn new(t: F) -> Self {
        Thunk { inner: ThunkInner::new(t) }
    }
    pub fn force(&self) -> &F::Item {
        self.inner.force(|f| f.resolve())
    }
    pub fn force_mut(&mut self) -> &mut F::Item {
        self.force();
        self.inner.get_mut().expect("force should have succeeded")
    }
    pub fn dethunk(self) -> F::Item {
        self.force();
        self.inner.into_inner().expect("force should have succeeded")
    }

    pub fn set(&self, val: F::Item) -> Result<(), F::Item> {
        self.inner.set(val)
    }
    pub fn is_initialized(&self) -> bool {
        self.inner.is_initialized()
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

pub struct AsRef<'a, F: Thunkable>(&'a Thunk<F>);
impl<'a, F: Thunkable> Thunkable for AsRef<'a, F> {
    type Item = &'a F::Item;

    fn resolve(self) -> Self::Item {
        self.0.force()
    }
}
pub struct Map<F, M>(F, M);
impl<U, F: Thunkable, M: FnOnce(F::Item) -> U> Thunkable for Map<F, M> {
    type Item = U;

    fn resolve(self) -> Self::Item {
        self.1(self.0.resolve())
    }
}

pub struct Cloned<F>(F);
impl<'a, T: 'a + Clone, F: Thunkable<Item=&'a T>> Thunkable for Cloned<F> {
    type Item = T;

    fn resolve(self) -> Self::Item {
        self.0.resolve().clone()
    }
}
pub struct Copied<F>(F);
impl<'a, T: 'a + Copy, F: Thunkable<Item=&'a T>> Thunkable for Copied<F> {
    type Item = T;

    fn resolve(self) -> Self::Item {
        *self.0.resolve()
    }
}

pub struct Inspect<F, I>(F, I);
impl<F: Thunkable, I: FnOnce(&F::Item)> Thunkable for Inspect<F, I> {
    type Item = F::Item;

    fn resolve(self) -> Self::Item {
        let t = self.0.resolve();
        self.1(&t);
        t
    }
}

pub fn zip<A: Thunkable, B: Thunkable>(a: A, b: B) -> ZipMap<A, B, ()> {
    ZipMap(a, b, ())
}
pub struct ZipMap<A, B, F>(A, B, F);
impl<A: Thunkable, B: Thunkable> ZipMap<A, B, ()> {
    pub fn map<U, F: FnOnce(A, B) -> U>(self, f: F) -> ZipMap<A, B, F> {
        ZipMap(self.0, self.1, f)
    }
}
impl<A: Thunkable, B: Thunkable, U, F: FnOnce(A, B) -> U> Thunkable for ZipMap<A, B, F> {
    type Item = U;

    fn resolve(self) -> Self::Item {
        self.2(self.0, self.1)
    }
}

pub trait Lazy<T> {
    fn resolve_ref(&self) -> &T;
    fn resolve_mut(&mut self) -> &mut T;
}

impl<T> Lazy<T> for T {
    fn resolve_ref(&self) -> &T {
        self
    }

    fn resolve_mut(&mut self) -> &mut T {
        self
    }
}

impl<T, F: FnOnce() -> T> Lazy<T> for ClosureThunk<T, F> {
    fn resolve_ref(&self) -> &T {
        self.force()
    }

    fn resolve_mut(&mut self) -> &mut T {
        self.force_mut()
    }
}
impl<T, A> Lazy<T> for ArgThunk<T, A> {
    fn resolve_ref(&self) -> &T {
        self.force()
    }

    fn resolve_mut(&mut self) -> &mut T {
        self.force_mut()
    }
}
struct ThunkInner<T, F> {
    inner: OnceCell<T>,
    init: Cell<Option<F>>
}
impl<T, F> ThunkInner<T, F> {
    fn new(f: F) -> Self {
        ThunkInner { inner: OnceCell::new(), init: Cell::new(Some(f)) }
    }

    fn force(&self, r: impl FnOnce(F) -> T) -> &T {
        self.inner.get_or_init(|| match self.init.take() {
            Some(f) => r(f),
            None => panic!("no initializer"),
        })
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

#[derive(Clone)]
pub struct ClosureThunk<T, F = fn() -> T> {
    inner: ThunkInner<T, F>
}

impl<T> ClosureThunk<T> {
    pub fn undef() -> Self {
        ClosureThunk::new(|| panic!("undef"))
    }
}
impl<T, F: FnOnce() -> T> ClosureThunk<T, F> {
    pub fn new(f: F) -> Self {
        ClosureThunk { inner: ThunkInner::new(f) }
    }

    pub fn as_ref<'a>(&'a self) -> ClosureThunk<&'a T, Box<dyn FnOnce() -> &'a T + 'a>> {
        ClosureThunk::new(Box::new(|| self.force()))
    }

    pub fn force(&self) -> &T {
        self.inner.force(|f| f())
    }

    pub fn force_mut(&mut self) -> &mut T {
        self.force();
        self.inner.get_mut().expect("force should have succeeded")
    }

    pub fn map<'a, U>(self, f: impl FnOnce(T) -> U + 'a) -> ClosureThunk<U, Box<dyn FnOnce() -> U + 'a>> 
        where T: 'a, F: 'a
    {
        ClosureThunk::new(Box::new(|| f(self.dethunk())))
    }

    pub fn set(&self, val: T) -> Result<(), T> {
        self.inner.set(val)
    }

    pub fn dethunk(self) -> T {
        self.force();
        self.inner.into_inner().expect("force should have succeeded")
    }

    pub fn is_initialized(&self) -> bool {
        self.inner.is_initialized()
    }
}

#[derive(Clone)]
pub struct ArgThunk<T, A> {
    #[allow(clippy::type_complexity)]
    inner: ThunkInner<T, (fn(A) -> T, A)>
}

impl<T> ArgThunk<T, ()> {
    pub fn undef() -> Self {
        ArgThunk::new(|_| panic!("undef"), ())
    }
}
impl<T> ArgThunk<T, fn() -> T> {
    pub fn nz(f: fn() -> T) -> Self {
        ArgThunk::new(|f| f(), f)
    }
}
impl<T, A> ArgThunk<T, A> {
    pub fn new(f: fn(A) -> T, a: A) -> Self {
        Self { inner: ThunkInner::new((f, a)) }
    }

    pub fn as_ref(&self) -> ArgThunk<&T, &Self> {
        ArgThunk::new(ArgThunk::force, self)
    }

    pub fn force(&self) -> &T {
        self.inner.force(|(f, a)| f(a))
    }

    pub fn force_mut(&mut self) -> &mut T {
        self.force();
        self.inner.get_mut().expect("force should have succeeded")
    }

    #[allow(clippy::type_complexity)]
    pub fn map<U>(self, f: fn(T) -> U) -> ArgThunk<U, (fn(T) -> U, Self)> {
        ArgThunk::new(|(f, t)| f(t.dethunk()), (f, self))
    }

    pub fn set(&self, val: T) -> Result<(), T> {
        self.inner.set(val)
    }

    pub fn dethunk(self) -> T {
        self.force();
        self.inner.into_inner().expect("force should have succeeded")
    }

    pub fn is_initialized(&self) -> bool {
        self.inner.is_initialized()
    }

    pub fn boxed<'a>(self) -> Box<dyn Lazy<T> + 'a> 
        where T: 'a, A: 'a
    {
        Box::new(self)
    }
}
impl<T: Clone, A> ArgThunk<T, A> {
    pub fn cloned(&self) -> ArgThunk<T, &Self> {
        ArgThunk::new(|t| t.force().clone(), self)
    }
}
impl<T: Copy, A> ArgThunk<T, A> {
    pub fn copied(&self) -> ArgThunk<T, &Self> {
        ArgThunk::new(|t| *t.force(), self)
    }
}

impl<T: Clone, F: Clone> Clone for ThunkInner<T, F> {
    fn clone(&self) -> Self {
        Self { inner: self.inner.clone(), init: match self.init.take() {
            Some(t) => {
                let tc = t.clone();
                self.init.replace(Some(t));
                Cell::new(Some(tc))
            },
            None => Cell::new(None),
        } }
    }
}

#[allow(unused_macros)]
macro_rules! thunk_arg {
    ($i:ident) => {$i};
    ($_:ident = $e:expr) => {$e};
}
#[allow(unused_macros)]
macro_rules! thunk_args {
    ($($i:ident $(= $ie:expr)?),*) => {
        ($(thunk_arg!($i $(= $ie)?)),*)
    };
}
#[allow(unused_macros)]
macro_rules! thunk {
    (|| $e:expr) => { $crate::ArgThunk::nz(|| $e) };
    (|$i:ident $(= ($ie:expr))?| $e:expr) => {
        $crate::ArgThunk::new(|$i| $e, thunk_arg!($i $(= $ie)?))
    };
    (|($($i:ident $(= $ie:expr)?),+)| $e:expr) => {
        $crate::ArgThunk::new(|($($i),+)| $e, thunk_args!($($i $(= $ie)?),+))
    };
}

#[cfg(test)]
mod tests {
    use crate::{Lazy, ArgThunk, Thunk, Thunkable};

    #[test]
    fn thunky() {
        let x = thunk!(|| {
            println!("initialized x");
            2u32
        });
        let y = thunk!(|| {
            println!("initialized y");
            3u32
        });
        let y = vec![
            x.as_ref().map(|t| t + 14).boxed(), 
            x.cloned().boxed(), 
            y.cloned().boxed(), 
            x.cloned().boxed()
        ];
        let z: ArgThunk<Vec<_>, _> = thunk!(|y| {
            y.into_iter()
                .map(|b| *(*b).resolve_ref())
                .collect()
        });

        let xy = x.as_ref().map(|t| t + 1);
        let _ = x.set(13);
        println!("{:?}", xy.force());
        println!("{:?}", z.force());
    }

    #[test]
    fn doubler() {
        fn and<'a>(left: &'a dyn Lazy<bool>, right: &'a dyn Lazy<bool>) -> impl Lazy<bool> + 'a {
            thunk!(|(l = left, r = right)| *l.resolve_ref() && *r.resolve_ref())
        }

        let x = thunk!(|| false);
        let y = ArgThunk::undef();
        let w = thunk!(|(x = &x, y = &y)| and(x, y))
            .map(|t| !t.resolve_ref())
            .boxed();
        println!("{}", (*w).resolve_ref());
    }
    #[test]
    fn time_travel() {
        let y: ArgThunk<usize, _> = ArgThunk::undef();
        let m = vec![1, 2, 4, 5, 9, 7, 4, 1, 2, 329, 23, 23, 21, 123, 123, 0, 324];
        let (m, it) = m.into_iter()
            .fold((vec![], 0), |(mut vec, r), t| {
                vec.push(&y);
                (vec, r.max(t))
            });
        y.set(it).ok().unwrap();
        let m: Vec<_> = m.into_iter()
            .map(ArgThunk::force)
            .copied()
            .collect();
        println!("{m:?}");
    }

    #[test]
    fn newthunk() {
        let x = Thunk::with(|| dbg!(2));
        let y = Thunk::with(|| dbg!(3));

        println!("creating thunk sum");
        let sum = (&x, &y)
            .map(|(x, y)| x + y)
            .inspect(|_| println!("loaded thunk sum"))
            .into_thunk();
        println!("created thunk sum");
        println!("{}", sum.force());

        let z = Thunk::with(|| dbg!(true));
        let w = Thunk::undef();
        let res = (&z).zip(&w)
            .map(|l, r| *l.force() || *r.force())
            .inspect(|_| println!("loaded result"))
            .into_thunk();
        println!("{}", res.force());
    }
}