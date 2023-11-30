//! Utilities to better handle [`Thunk`][`crate::Thunk`]s when used with iterators.

use std::iter::FusedIterator;

use crate::list::ThunkList;
use crate::{Thunk, Thunkable, transform};

/// A set of methods to apply onto iterators to better interop with thunks.
/// 
/// These can be accessed by importing this trait.
pub trait ThunkItertools: Iterator {
    /// Like [`Iterator::map`], but instead of evaluating the result,
    /// it is delegated to a thunk which will lazily evaluates the result
    /// when it is needed.
    fn map_delayed<U, F>(self, f: F) -> MapThunk<Self, F>
        where Self: Sized,
            F: FnMut(Self::Item) -> U + Copy
    {
        MapThunk(self, f)
    }
    /// Evaluates all the thunks in this iterator and returns a reference to the value.
    fn forced<'a, F: Thunkable + 'a>(self) -> Forced<Self>
        where Self: Sized + Iterator<Item=&'a Thunk<F::Item, F>>
    {
        Forced(self)
    }
    /// Evaluates all the thunks in this iterator and returns a mutable reference to
    /// the value.
    fn forced_mut<'a, F: Thunkable + 'a>(self) -> ForcedMut<Self>
        where Self: Sized + Iterator<Item=&'a mut Thunk<F::Item, F>>
    {
        ForcedMut(self)
    }
    /// Evaluates all the thunks in this iterator and returns the value.
    fn resolved<F: Thunkable>(self) -> Resolved<Self>
        where Self: Sized + Iterator<Item = F>,
    {
        Resolved(self)
    }
    /// This collector holds the iterator and uses it to build a [`ThunkList`].
    /// 
    /// Unlike [`Iterator::collect`], this does not evaluate every element of the iterator,
    /// but rather evaluates new elements once they need be resolved.
    /// 
    /// As a result, this iterator has to last as long as the resulting `ThunkList`.
    fn collect_lazy<'a, F: Thunkable + 'a>(self) -> ThunkList<'a, F::Item>
        where Self: Sized + Iterator<Item = F> + 'a
    {
        ThunkList::from_iter_lazy(self.map(Thunkable::into_thunk))
    }
}
impl<I: Iterator> ThunkItertools for I {}

/// Like [`Iterator::map`], but with lazy resolution. Created by [`ThunkItertools::map_delayed`].
pub struct MapThunk<I, F>(I, F);
impl<R, I: Iterator, F: FnMut(I::Item) -> R + Copy> Iterator for MapThunk<I, F> {
    type Item = Thunk<R, transform::Map<Thunk<I::Item, crate::transform::Known<I::Item>>, F>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
            .map(|t| Thunk::from(t).map(self.1))
            .map(Thunk::new)
    }
}
impl<R, I: DoubleEndedIterator, F: FnMut(I::Item) -> R + Copy> DoubleEndedIterator for MapThunk<I, F> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
            .map(|t| Thunk::from(t).map(self.1))
            .map(Thunk::new)
    }
}
impl<R, I: ExactSizeIterator, F: FnMut(I::Item) -> R + Copy> ExactSizeIterator for MapThunk<I, F> {
    fn len(&self) -> usize {
        self.0.len()
    }
}
impl<R, I: FusedIterator, F: FnMut(I::Item) -> R + Copy> FusedIterator for MapThunk<I, F> {}

/// Forces all thunks in the iterator. Created by [`ThunkItertools::forced`].
pub struct Forced<I>(I);
impl<'a, I, F> Iterator for Forced<I>
    where F: Thunkable + 'a,
        I: Iterator<Item=&'a Thunk<F::Item, F>>
{
    type Item = &'a F::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Thunk::force)
    }
}
impl<'a, I, F> DoubleEndedIterator for Forced<I>
    where F: Thunkable + 'a,
        I: DoubleEndedIterator<Item=&'a Thunk<F::Item, F>>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(Thunk::force)
    }
}
impl<'a, I, F> ExactSizeIterator for Forced<I>
    where F: Thunkable + 'a,
        I: ExactSizeIterator<Item=&'a Thunk<F::Item, F>>
{
    fn len(&self) -> usize {
        self.0.len()
    }
}
impl<'a, I, F> FusedIterator for Forced<I>
    where F: Thunkable + 'a,
        I: FusedIterator<Item=&'a Thunk<F::Item, F>>
{}

/// Forces all thunks in the iterator. Created by [`ThunkItertools::forced_mut`].
pub struct ForcedMut<I>(I);
impl<'a, I, F> Iterator for ForcedMut<I>
    where F: Thunkable + 'a,
        I: Iterator<Item=&'a mut Thunk<F::Item, F>>
{
    type Item = &'a mut F::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Thunk::force_mut)
    }
}
impl<'a, I, F> DoubleEndedIterator for ForcedMut<I>
    where F: Thunkable + 'a,
        I: DoubleEndedIterator<Item=&'a mut Thunk<F::Item, F>>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(Thunk::force_mut)
    }
}
impl<'a, I, F> ExactSizeIterator for ForcedMut<I>
    where F: Thunkable + 'a,
        I: ExactSizeIterator<Item=&'a mut Thunk<F::Item, F>>
{
    fn len(&self) -> usize {
        self.0.len()
    }
}
impl<'a, I, F> FusedIterator for ForcedMut<I>
    where F: Thunkable + 'a,
        I: FusedIterator<Item=&'a mut Thunk<F::Item, F>>
{}

/// Resolves all thunkables in the iterator. Created by [`ThunkItertools::resolved`].
pub struct Resolved<I>(I);
impl<I, F> Iterator for Resolved<I>
    where F: Thunkable,
        I: Iterator<Item=F>
{
    type Item = F::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Thunkable::resolve)
    }
}
impl<I, F> DoubleEndedIterator for Resolved<I>
    where F: Thunkable,
        I: DoubleEndedIterator<Item=F>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(Thunkable::resolve)
    }
}
impl<I, F> ExactSizeIterator for Resolved<I>
    where F: Thunkable,
        I: ExactSizeIterator<Item=F>
{
    fn len(&self) -> usize {
        self.0.len()
    }
}
impl<I, F> FusedIterator for Resolved<I>
    where F: Thunkable,
        I: FusedIterator<Item=F>
{}