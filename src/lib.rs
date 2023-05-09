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
    fn zip<B: Thunkable>(self, b: B) -> ZipMap<(Self, B), ()>
        where Self: Sized
    {
        zip(self, b)
    }
    fn zip_map<U, B: Thunkable, F: FnOnce((Self, B)) -> U>(self, b: B, f: F) -> ZipMap<(Self, B), F>
        where Self: Sized
    {
        ZipMap((self, b), f)
    }
    fn boxed<'a>(self) -> ThunkBox<'a, Self::Item> 
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

#[derive(Clone)]
pub struct Thunk<F: Thunkable> {
    inner: ThunkInner<F::Item, F>
}
impl<T> Thunk<fn() -> T> {
    pub fn undef() -> Self {
        Thunk::with(|| panic!("undef"))
    }
    pub fn of(t: T) -> Self {
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

pub trait TupleConcat {
    type Out<T>;
    fn concat<T>(self, t: T) -> Self::Out<T>;
}

impl TupleConcat for () {
    type Out<T> = (T,);

    fn concat<T>(self, t: T) -> Self::Out<T> {
        (t,)
    }
}
macro_rules! tuple_concat_impl {
    ($($i:ident: $e:tt),+) => {
        impl<$($i),*> TupleConcat for ($($i),+,) {
            type Out<T> = ($($i),+, T);

            fn concat<T>(self, t: T) -> Self::Out<T> {
                ($(self.$e),+, t)
            }
        }
    }
}

tuple_concat_impl! { T0: 0 }
tuple_concat_impl! { T0: 0, T1: 1 }
tuple_concat_impl! { T0: 0, T1: 1, T2: 2 }
tuple_concat_impl! { T0: 0, T1: 1, T2: 2, T3: 3 }
tuple_concat_impl! { T0: 0, T1: 1, T2: 2, T3: 3, T4: 4 }
tuple_concat_impl! { T0: 0, T1: 1, T2: 2, T3: 3, T4: 4, T5: 5 }
tuple_concat_impl! { T0: 0, T1: 1, T2: 2, T3: 3, T4: 4, T5: 5, T6: 6 }
tuple_concat_impl! { T0: 0, T1: 1, T2: 2, T3: 3, T4: 4, T5: 5, T6: 6, T7: 7 }
tuple_concat_impl! { T0: 0, T1: 1, T2: 2, T3: 3, T4: 4, T5: 5, T6: 6, T7: 7, T8: 8 }
tuple_concat_impl! { T0: 0, T1: 1, T2: 2, T3: 3, T4: 4, T5: 5, T6: 6, T7: 7, T8: 8, T9: 9 }
tuple_concat_impl! { T0: 0, T1: 1, T2: 2, T3: 3, T4: 4, T5: 5, T6: 6, T7: 7, T8: 8, T9: 9, T10: 10 }
tuple_concat_impl! { T0: 0, T1: 1, T2: 2, T3: 3, T4: 4, T5: 5, T6: 6, T7: 7, T8: 8, T9: 9, T10: 10, T11: 11 }
tuple_concat_impl! { T0: 0, T1: 1, T2: 2, T3: 3, T4: 4, T5: 5, T6: 6, T7: 7, T8: 8, T9: 9, T10: 10, T11: 11, T12: 12 }

pub fn zip<A: Thunkable, B: Thunkable>(a: A, b: B) -> ZipMap<(A, B), ()> {
    ZipMap((a, b), ())
}
pub struct ZipMap<T, F>(T, F);

impl<T: TupleConcat> ZipMap<T, ()> {
    pub fn zip<U: Thunkable>(self, u: U) -> ZipMap<T::Out<U>, ()> {
        ZipMap(self.0.concat(u), ())
    }
}
impl<T> ZipMap<T, ()> {
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> ZipMap<T, F> {
        ZipMap(self.0, f)
    }
}
impl<T, U, F: FnOnce(T) -> U> Thunkable for ZipMap<T, F> {
    type Item = U;

    fn resolve(self) -> Self::Item {
        self.1(self.0)
    }
}

pub struct Seq<A: Thunkable, B: Thunkable>(pub A, pub B);
impl<A: Thunkable, B: Thunkable> Thunkable for Seq<A, B> {
    type Item = (A::Item, B::Item);

    fn resolve(self) -> Self::Item {
        (self.0.resolve(), self.1.resolve())
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
}

#[cfg(test)]
mod tests {
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
            (&x).map(|t| t + 14).boxed(),
            (&x).cloned().boxed(),
            (&y).cloned().boxed(),
            (&x).cloned().boxed(),
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
        let sum = crate::Seq(&x, &y)
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