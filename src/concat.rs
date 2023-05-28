//! A util to append elements to a tuple.
//! See [`TupleConcat`] for more details.

/// A trait which enables concatenation for tuples up to length 12.
pub trait TupleConcat {
    /// The type of newly constructed tuple after concatenating an element to it.
    type Out<T>;

    /// Constructs a new tuple after concatenating the provided element.
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
