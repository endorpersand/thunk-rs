pub mod tuple;
pub mod transform;
pub mod list;
pub use transform::zip;

use std::cell::{OnceCell, Cell};

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
impl<T> Thunkable for fn() -> T {
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
        let inner = OnceCell::new();
        let _ = inner.set(t);

        ThunkInner { inner, init: Cell::new(None) }
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
    fn map<G>(self, m: impl FnOnce(F) -> G) -> ThunkInner<T, G> {
        ThunkInner {
            inner: self.inner,
            init: Cell::new(self.init.into_inner().map(m))
        }
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
        Thunk::with(|| panic!("undef"))
    }
    pub fn with(f: fn() -> T) -> Self {
        Thunk::new(f)
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
        Thunk { inner: self.inner.map(Thunkable::into_box) }
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
pub struct ThunkBox<'a, T>(Box<dyn ThunkDrop<Item=T> + 'a>);

impl<'a, T> ThunkBox<'a, T> {
    fn new<F: Thunkable<Item=T> + 'a>(f: F) -> Self {
        ThunkBox(Box::new(Some(f)))
    }
}
impl<'a, T> Thunkable for ThunkBox<'a, T> {
    type Item = T;

    fn resolve(mut self) -> Self::Item {
        self.0.drop_resolve()
    }
    fn into_box<'b>(self) -> ThunkBox<'b, Self::Item> 
            where Self: 'b {
        self
    }
}

pub type ThunkAny<'a, T> = Thunk<ThunkBox<'a, T>>;

#[cfg(test)]
mod tests {
    use crate::transform::Seq;
    use crate::{Thunk, Thunkable};

    #[test]
    fn thunky() {
        let x = Thunk::with(|| {
            println!("initialized x");
            2u32
        });
        let y = Thunk::with(|| {
            println!("initialized y");
            3u32
        });
        let y = vec![
            (&x).map(|t| t + 14).into_box(),
            (&x).cloned().into_box(),
            (&y).cloned().into_box(),
            (&x).cloned().into_box(),
        ];
        let z = Thunk::of(y)
            .map(|y| {
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
        let x = Thunk::with(|| dbg!(false));
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
        let x = Thunk::with(|| dbg!(2));
        let y = Thunk::with(|| dbg!(3));

        println!("creating thunk sum");
        let sum = Seq(&x, &y)
            .map(|(x, y)| x + y)
            .inspect(|_| println!("loaded thunk sum"))
            .into_thunk();
        println!("created thunk sum");
        println!("{}", sum.force());

        let z = Thunk::with(|| dbg!(true));
        let w = Thunk::undef();
        let res = (&z).zip(&w)
            .zip(&w)
            .map(|(l, r, c)| *l.force() || *r.force() || *c.force())
            .inspect(|_| println!("loaded result"))
            .into_thunk();
        println!("{}", res.force());
    }
}