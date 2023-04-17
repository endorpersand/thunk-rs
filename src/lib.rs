use std::cell::{OnceCell, Cell};

pub struct Thunk<T, F = fn() -> T> {
    inner: OnceCell<T>,
    init: Cell<Option<F>>
}

impl<T> Thunk<T> {
    pub fn empty() -> Self {
        Thunk { inner: OnceCell::new(), init: Cell::new(Some(|| panic!("thunk value unknown"))) }
    }
}
impl<T, F: FnOnce() -> T> Thunk<T, F> {
    pub fn new(f: F) -> Self {
        Thunk { inner: OnceCell::new(), init: Cell::new(Some(f)) }
    }

    pub fn as_ref<'a>(&'a self) -> Thunk<&'a T, Box<dyn FnOnce() -> &'a T + 'a>> {
        Thunk::new(Box::new(|| Thunk::get(self)))
    }

    pub fn get(&self) -> &T {
        self.inner.get_or_init(|| match self.init.take() {
            Some(f) => f(),
            None => panic!("no initializer"),
        })
    }

    pub fn map<'a, U>(self, f: impl FnOnce(T) -> U + 'a) -> Thunk<U, Box<dyn FnOnce() -> U + 'a>> 
        where T: 'a, F: 'a
    {
        Thunk::new(Box::new(|| f(Thunk::dethunk(self))))
    }

    pub fn set(&self, val: T) -> Result<(), T> {
        self.inner.set(val)
    }

    pub fn dethunk(self) -> T {
        Thunk::get(&self);
        self.inner.into_inner().expect("resolved dethunk")
    }

    pub fn dethunk_all<I: IntoIterator<Item=Thunk<T, F>>>(t: I) -> impl Iterator<Item=T> {
        t.into_iter().map(Thunk::dethunk)
    }
    pub fn get_all<'a, I: IntoIterator<Item=&'a Thunk<T, F>>>(t: I) -> impl Iterator<Item=&'a T> 
        where T: 'a, F: 'a
    {
        t.into_iter().map(Thunk::get)
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
        let y = vec![
            x.as_ref().map(|t| t + 14), 
            x.as_ref().map(u32::clone), 
            y.as_ref().map(u32::clone), 
            x.as_ref().map(u32::clone)
        ];
        let z: Thunk<Vec<_>, _> = Thunk::new(|| Thunk::dethunk_all(y).collect());

        let xy = x.as_ref().map(|t| t + 1);
        let _ = x.set(13);
        println!("{:?}", xy.get());
        println!("{:?}", z.get());
    }

    #[test]
    fn time_travel() {
        let y = Thunk::<usize>::empty();
        let m = vec![1, 2, 4, 5, 9, 7, 4, 1, 2, 329, 23, 23, 21, 123, 123, 0, 324];
        let (m, it) = m.into_iter()
            .fold((vec![], 0), |(mut vec, r), t| {
                vec.push(&y);
                (vec, r.max(t))
            });
        y.set(it).ok().unwrap();
        let m: Vec<_> = Thunk::get_all(m)
            .copied()
            .collect();
        println!("{m:?}");
    }
}