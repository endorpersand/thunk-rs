use std::iter::FusedIterator;

use crate::{Thunk, ThunkFn, Thunkable, transform};

pub trait ThunkItertools: Iterator {
    fn map_delayed<U, F>(self, f: F) -> MapThunk<Self, F>
        where Self: Sized,
            F: FnMut(Self::Item) -> U + Copy
    {
        MapThunk(self, f)
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