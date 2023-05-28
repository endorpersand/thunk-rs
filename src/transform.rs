//! Transformers for [`Thunkable`]s.
//! 
//! These modify or apply behavior once a `Thunkable` value is resolved.

use std::marker::PhantomData;

use crate::concat::TupleConcat;
use crate::Thunkable;

/// Maps a resolved value into another. Created by [`Thunkable::map`].
pub struct Map<F, M>(pub(crate) F, pub(crate) M);
impl<U, F: Thunkable, M: FnOnce(F::Item) -> U> Thunkable for Map<F, M> {
    type Item = U;

    fn resolve(self) -> Self::Item {
        self.1(self.0.resolve())
    }
}
/// Maps a resolved value into another thunkable. Created by [`Thunkable::and_then`].
pub struct AndThen<F, M>(pub(crate) F, pub(crate) M);
impl<U: Thunkable, F: Thunkable, M: FnOnce(F::Item) -> U> Thunkable for AndThen<F, M> {
    type Item = U::Item;

    fn resolve(self) -> Self::Item {
        self.1(self.0.resolve()).resolve()
    }
}
/// Flattens a thunkable initializing a thunkable. Created by [`Thunkable::flatten`].
pub struct Flatten<F>(pub(crate) F);
impl<U: Thunkable, F: Thunkable<Item = U>> Thunkable for Flatten<F> {
    type Item = U::Item;

    fn resolve(self) -> Self::Item {
        self.0.resolve().resolve()
    }
}
/// Clones an initialized reference. Created by [`Thunkable::cloned`].
pub struct Cloned<F>(pub(crate) F);
impl<'a, T: 'a + Clone, F: Thunkable<Item=&'a T>> Thunkable for Cloned<F> {
    type Item = T;

    fn resolve(self) -> Self::Item {
        self.0.resolve().clone()
    }
}
/// Copies an initialized reference. Created by [`Thunkable::cloned`].
pub struct Copied<F>(pub(crate) F);
impl<'a, T: 'a + Copy, F: Thunkable<Item=&'a T>> Thunkable for Copied<F> {
    type Item = T;

    fn resolve(self) -> Self::Item {
        *self.0.resolve()
    }
}
/// Applies an inspector function once resolved. Created by [`Thunkable::inspect`].
pub struct Inspect<F, I>(pub(crate) F, pub(crate) I);
impl<F: Thunkable, I: FnOnce(&F::Item)> Thunkable for Inspect<F, I> {
    type Item = F::Item;

    fn resolve(self) -> Self::Item {
        let t = self.0.resolve();
        self.1(&t);
        t
    }
}

/// Collects two `Thunkable`s into a tuple.
/// These can be resolved together with [`ZipMap::map`].
/// 
/// More `Thunkable`s can be concatenated with [`ZipMap::zip`].
/// 
/// Unlike [`Seq`], `zip` will not resolve all `Thunkable`s when the conjoining
/// `Thunkable` is resolved.
pub fn zip<A: Thunkable, B: Thunkable>(a: A, b: B) -> ZipMap<(A, B), ()> {
    ZipMap((a, b), ())
}
/// Collects two `Thunkable`s into a tuple. Created by [`zip`], [`Thunkable::zip`], or [`Thunkable::zip_map`].
pub struct ZipMap<T, F>(pub(crate) T, pub(crate) F);

impl<T: TupleConcat> ZipMap<T, ()> {
    /// Concatenates another element to the tuple of elements held by this `ZipMap`.
    pub fn zip<U: Thunkable>(self, u: U) -> ZipMap<T::Out<U>, ()> {
        ZipMap(self.0.concat(u), ())
    }
}
impl<T> ZipMap<T, ()> {
    /// Applies a mapper function to all of the elements.
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

/// Collects a sequence of elements, immediately resolving both of them 
/// if the conjoining `Thunkable` is resolved.
pub struct Seq<A: Thunkable, B: Thunkable>(pub A, pub B);
impl<A: Thunkable, B: Thunkable> Thunkable for Seq<A, B> {
    type Item = (A::Item, B::Item);

    fn resolve(self) -> Self::Item {
        (self.0.resolve(), self.1.resolve())
    }
}

/// This struct is used to indicate that there is no initializer.
/// 
/// A [`Thunk`][`crate::Thunk`] with this type as the initializer 
/// should be initialized manually with [`Thunk::set`][`crate::Thunk::set`] 
/// or through similar means.
pub struct Known<T>(PhantomData<T>);
impl<T> Thunkable for Known<T> {
    type Item = T;

    fn resolve(self) -> Self::Item {
        unreachable!("Known structs should never be initialized")
    }
}