use std::rc::Rc;

use crate::{Thunk, Thunkable, ThunkAny};

struct Node<T> {
    val: Rc<ThunkAny<'static, T>>,
    next: Option<Rc<ThunkAny<'static, Node<T>>>>
}

impl<T> Drop for Node<T> {
    fn drop(&mut self) {
        let mut head = self.next.take();
        while let Some(thunk) = head {
            if let Some(mut inner) = Rc::into_inner(thunk).and_then(Thunk::try_into_inner) {
                head = inner.next.take();
            } else {
                break;
            }
        }
    }
}
impl<T> Clone for Node<T> {
    fn clone(&self) -> Self {
        Self { val: self.val.clone(), next: self.next.clone() }
    }
}

pub struct ThunkList<T> {
    head: Option<Node<T>>
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

    fn pushed_thunk<F>(&self, f: F) -> ThunkList<T> 
        where T: 'static,
              F: Thunkable<Item = T> + 'static
    {
        let next = self.head.as_ref()
            .cloned()
            .map(Thunk::of)
            .map(Thunk::boxed)
            .map(Rc::new);
        
        let node = Node {
            val: Rc::new(f.into_thunk().boxed()),
            next
        };

        ThunkList { head: Some(node) }
    }
    fn pushed(&self, t: T) -> ThunkList<T> 
        where T: 'static
    {
        self.pushed_thunk(Thunk::of(t))
    }

    pub fn split_first(&self) -> Option<(Rc<ThunkAny<'static, T>>, ThunkList<T>)> {
        let Node { val, next } = self.head.as_ref()?;
        
        let head = next.as_deref()
            .map(Thunk::force)
            .cloned();

        Some((Rc::clone(val), ThunkList { head }))
    }
    pub fn iter(&self) -> Iter<T> {
        Iter(self.head.as_ref())
    }
    pub fn get_thunk(&self, n: usize) -> Option<&ThunkAny<'static, T>> {
        self.iter().nth(n)
    }
    pub fn get(&self, n: usize) -> Option<&T> {
        self.iter().nth(n).map(Thunk::force)
    }
    pub fn len(&self) -> usize {
        self.iter().count()
    }
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }
}

impl<T> Default for ThunkList<T> {
    fn default() -> Self {
        Self::new()
    }
}
pub struct Iter<'a, T>(Option<&'a Node<T>>);
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a ThunkAny<'static, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.0?;
        let val = &*node.val;
        self.0 = node.next.as_ref().map(|t| t.force());
        
        Some(val)
    }
}