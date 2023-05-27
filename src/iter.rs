use std::iter::FusedIterator;

use crate::{Thunk, ThunkFn, Thunkable, transform};

pub trait ThunkItertools: Iterator {
    fn map_delayed<U, F>(self, f: F) -> MapThunk<Self, F>
        where Self: Sized,
            F: FnMut(Self::Item) -> U + Copy
    {
        MapThunk(self, f)
    }
    fn forced<'a, F: Thunkable + 'a>(self) -> Forced<Self>
        where Self: Sized + Iterator<Item=&'a Thunk<F::Item, F>>
    {
        Forced(self)
    }
    fn forced_mut<'a, F: Thunkable + 'a>(self) -> ForcedMut<Self>
        where Self: Sized + Iterator<Item=&'a mut Thunk<F::Item, F>>
    {
        ForcedMut(self)
    }
    fn resolved<F: Thunkable>(self) -> Resolved<Self>
        where Self: Sized + Iterator<Item = F>,
    {
        Resolved(self)
    }
}
impl<I: Iterator> ThunkItertools for I {}

pub struct MapThunk<I, F>(I, F);
impl<R, I: Iterator, F: FnMut(I::Item) -> R + Copy> Iterator for MapThunk<I, F> {
    type Item = Thunk<R, transform::Map<ThunkFn<I::Item>, F>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|t| ThunkFn::of(t).map(self.1).into_thunk())
    }
}
impl<R, I: DoubleEndedIterator, F: FnMut(I::Item) -> R + Copy> DoubleEndedIterator for MapThunk<I, F> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|t| ThunkFn::of(t).map(self.1).into_thunk())
    }
}
impl<R, I: ExactSizeIterator, F: FnMut(I::Item) -> R + Copy> ExactSizeIterator for MapThunk<I, F> {
    fn len(&self) -> usize {
        self.0.len()
    }
}
impl<R, I: FusedIterator, F: FnMut(I::Item) -> R + Copy> FusedIterator for MapThunk<I, F> {}

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