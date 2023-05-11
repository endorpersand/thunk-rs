use std::rc::Rc;

use crate::{Thunk, ThunkBox, Thunkable};

pub struct ThunkList<T> {
    head: Option<Rc<Node<T>>>
}
impl<T> ThunkList<T> {
    pub fn new() -> Self {
        ThunkList { head: None }
    }

    pub fn cons_thunk<F>(f: F, lst: &Self) -> ThunkList<T> 
        where T: 'static,
              F: Thunkable<Item = T> + 'static
    {
        lst.pushed_thunk(f)
    }
    pub fn cons(t: T, lst: &Self) -> ThunkList<T>
        where T: 'static
    {
        lst.pushed(t)
    }

    pub fn pushed_thunk<F>(&self, f: F) -> ThunkList<T> 
        where T: 'static,
              F: Thunkable<Item = T> + 'static
    {
        let next = self.head.as_ref()
            .map(Rc::clone)
            .map(Thunk::of)
            .map(Thunk::boxed);
        
        let node = Node {
            val: f.into_thunk().boxed(),
            next
        };

        ThunkList { head: Some(Rc::new(node)) }
    }
    pub fn pushed(&self, t: T) -> ThunkList<T> 
        where T: 'static
    {
        self.pushed_thunk(Thunk::of(t))
    }

    pub fn split(&self) -> Option<(&Thunk<ThunkBox<'static, T>>, ThunkList<T>)> {
        let Node { val, next } = &**self.head.as_ref()?;
        
        let head = next.as_ref()
            .map(Thunk::force)
            .map(Rc::clone);

        Some((val, ThunkList { head }))
    }
}

impl<T> Default for ThunkList<T> {
    fn default() -> Self {
        Self::new()
    }
}
struct Node<T> {
    val: Thunk<ThunkBox<'static, T>>,
    next: Option<Thunk<ThunkBox<'static, Rc<Node<T>>>>>
}

impl<T> Drop for Node<T> {
    fn drop(&mut self) {
        let mut head = self.next.take();
        while let Some(thunk) = head {
            if let Some(mut inner) = thunk.try_into_inner().and_then(Rc::into_inner) {
                head = inner.next.take();
            } else {
                break;
            }
        }
    }
}