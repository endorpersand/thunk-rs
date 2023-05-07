use std::cell::{OnceCell, Cell};

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
impl<T, A> Lazy<T> for Thunk<T, A> {
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
pub struct Thunk<T, A> {
    #[allow(clippy::type_complexity)]
    inner: ThunkInner<T, (fn(A) -> T, A)>
}

impl<T> Thunk<T, ()> {
    pub fn undef() -> Self {
        Thunk::new(|_| panic!("undef"), ())
    }
}
impl<T> Thunk<T, fn() -> T> {
    pub fn nz(f: fn() -> T) -> Self {
        Thunk::new(|f| f(), f)
    }
}
impl<T, A> Thunk<T, A> {
    pub fn new(f: fn(A) -> T, a: A) -> Self {
        Self { inner: ThunkInner::new((f, a)) }
    }

    pub fn as_ref(&self) -> Thunk<&T, &Self> {
        Thunk::new(Thunk::force, self)
    }

    pub fn force(&self) -> &T {
        self.inner.force(|(f, a)| f(a))
    }

    pub fn force_mut(&mut self) -> &mut T {
        self.force();
        self.inner.get_mut().expect("force should have succeeded")
    }

    #[allow(clippy::type_complexity)]
    pub fn map<U>(self, f: fn(T) -> U) -> Thunk<U, (fn(T) -> U, Self)> {
        Thunk::new(|(f, t)| f(t.dethunk()), (f, self))
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
impl<T: Clone, A> Thunk<T, A> {
    pub fn cloned(&self) -> Thunk<T, &Self> {
        Thunk::new(|t| t.force().clone(), self)
    }
}
impl<T: Copy, A> Thunk<T, A> {
    pub fn copied(&self) -> Thunk<T, &Self> {
        Thunk::new(|t| *t.force(), self)
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
    (|| $e:expr) => { $crate::Thunk::nz(|| $e) };
    (|$i:ident $(= ($ie:expr))?| $e:expr) => {
        $crate::Thunk::new(|$i| $e, thunk_arg!($i $(= $ie)?))
    };
    (|($($i:ident $(= $ie:expr)?),+)| $e:expr) => {
        $crate::Thunk::new(|($($i),+)| $e, thunk_args!($($i $(= $ie)?),+))
    };
}

#[cfg(test)]
mod tests {
    use crate::{Lazy, Thunk};

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
        let z: Thunk<Vec<_>, _> = thunk!(|y| {
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
        let y = Thunk::undef();
        let w = thunk!(|(x = &x, y = &y)| and(x, y))
            .map(|t| !t.resolve_ref())
            .boxed();
        println!("{}", (*w).resolve_ref());
    }
    #[test]
    fn time_travel() {
        let y: Thunk<usize, _> = Thunk::undef();
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
}