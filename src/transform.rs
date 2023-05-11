use crate::tuple::TupleConcat;
use crate::{Thunkable, Thunk};

pub struct AsRef<'a, F: Thunkable>(pub(crate) &'a Thunk<F>);
impl<'a, F: Thunkable> Thunkable for AsRef<'a, F> {
    type Item = &'a F::Item;

    fn resolve(self) -> Self::Item {
        self.0.force()
    }
}
pub struct Map<F, M>(pub(crate) F, pub(crate) M);
impl<U, F: Thunkable, M: FnOnce(F::Item) -> U> Thunkable for Map<F, M> {
    type Item = U;

    fn resolve(self) -> Self::Item {
        self.1(self.0.resolve())
    }
}

pub struct Cloned<F>(pub(crate) F);
impl<'a, T: 'a + Clone, F: Thunkable<Item=&'a T>> Thunkable for Cloned<F> {
    type Item = T;

    fn resolve(self) -> Self::Item {
        self.0.resolve().clone()
    }
}
pub struct Copied<F>(pub(crate) F);
impl<'a, T: 'a + Copy, F: Thunkable<Item=&'a T>> Thunkable for Copied<F> {
    type Item = T;

    fn resolve(self) -> Self::Item {
        *self.0.resolve()
    }
}

pub struct Inspect<F, I>(pub(crate) F, pub(crate) I);
impl<F: Thunkable, I: FnOnce(&F::Item)> Thunkable for Inspect<F, I> {
    type Item = F::Item;

    fn resolve(self) -> Self::Item {
        let t = self.0.resolve();
        self.1(&t);
        t
    }
}

pub fn zip<A: Thunkable, B: Thunkable>(a: A, b: B) -> ZipMap<(A, B), ()> {
    ZipMap((a, b), ())
}
pub struct ZipMap<T, F>(pub(crate) T, pub(crate) F);

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