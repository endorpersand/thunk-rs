use std::cell::{OnceCell, Cell};
use std::ops::Deref;

pub struct Thunk<T, F = fn() -> T> {
    inner: OnceCell<T>,
    init: Cell<Option<F>>
}
impl<T, F: FnOnce() -> T> Thunk<T, F> {
    pub fn new(f: F) -> Self {
        Thunk { inner: OnceCell::new(), init: Cell::new(Some(f)) }
    }

    pub fn get_ref<'a>(this: &'a Thunk<T, F>) -> Thunk<&'a T, Box<dyn FnOnce() -> &'a T + 'a>> {
        Thunk::new(Box::new(|| Thunk::force(this)))
    }

    pub fn force(this: &Thunk<T, F>) -> &T {
        this.inner.get_or_init(|| match this.init.take() {
            Some(f) => f(),
            None => panic!("no initializer"),
        })
    }

    pub fn map<'a, U>(this: Thunk<T, F>, f: impl FnOnce(T) -> U + 'a) -> Thunk<U, Box<dyn FnOnce() -> U + 'a>> 
        where T: 'a, F: 'a
    {
        Thunk::new(Box::new(|| f(Thunk::dethunk(this))))
    }
    pub fn dethunk(this: Thunk<T, F>) -> T {
        Thunk::force(&this);
        this.inner.into_inner().expect("resolved dethunk")
    }

    pub fn dethunk_all<I: IntoIterator<Item=Thunk<T, F>>>(t: I) -> impl Iterator<Item=T> {
        t.into_iter().map(Thunk::dethunk)
    }
}

impl<T, F: FnOnce() -> T> Deref for Thunk<T, F> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        Thunk::force(self)
    }
}

impl<U: 'static, T: std::ops::Add<U> + 'static, F: FnOnce() -> T + 'static> std::ops::Add<U> for Thunk<T, F> {
    type Output = Thunk<T::Output, Box<dyn FnOnce() -> T::Output>>;

    fn add(self, rhs: U) -> Self::Output {
        Thunk::map(self, |t| t + rhs)
    }
}

#[cfg(test)]
mod tests {
    use crate::Thunk;

    #[test]
    fn thunky() {
        let x = Thunk::new(|| {
            println!("initialized x");
            2u32
        });
        let y = Thunk::new(|| {
            println!("initialized y");
            3u32
        });
        let y = vec![Thunk::get_ref(&x), Thunk::get_ref(&x), Thunk::get_ref(&y), Thunk::get_ref(&x)];
        let z: Thunk<Vec<_>, _> = Thunk::new(|| Thunk::dethunk_all(y).collect());

        let xy = Thunk::map(Thunk::get_ref(&x), |t| t + 1);

        println!("{:?}", *xy);
        println!("{:?}", *z);
    }
}