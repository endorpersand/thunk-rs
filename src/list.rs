use std::rc::Rc;

use crate::{Thunk, Thunkable, ThunkAny};

struct Node<T> {
    val: Rc<ThunkAny<'static, T>>,
    next: Option<Rc<ThunkAny<'static, Node<T>>>>
}

fn find_isolated_cycle<T>(start: Rc<T>, mut f: impl FnMut(&T) -> Option<&Rc<T>>) -> Option<Rc<T>> {
    let mut ef = |t| {
        f(t).filter(|rc| {
            // we want to ignore any cycles that are pointed to from other places
            // so we got to make sure there are no other references
            let equal = Rc::ptr_eq(&start, rc);
            let strong_ct = Rc::strong_count(rc);
    
            strong_ct == if equal { 2 } else { 1 }
        })
    };
    let mut tort = ef(&start)?;
    let mut hare = ef(tort)?;

    while !Rc::ptr_eq(tort, hare) {
        tort = ef(tort)?;
        hare = ef(hare)?;
        hare = ef(hare)?;
    }
    
    Some(tort).cloned()
}

impl<T> Drop for Node<T> {
    fn drop(&mut self) {
        let mut head = self.next.take();
        while let Some(rc) = head.take() {
            let weak = Rc::downgrade(&rc);

            if let Some(thunk) = Rc::into_inner(rc) {
                if let Some(mut inner) = thunk.try_into_inner() {
                    head = inner.next.take();
                }
            } else if let Some(rc) = weak.upgrade() {
                if let Some(iso_start) = find_isolated_cycle(rc, |t| t.try_get().and_then(|n| n.next.as_ref())) {
                    unsafe {
                        let ptr = Rc::into_raw(iso_start).cast_mut();
                        // SAFETY: Rc came from into_raw and there has to be 2 references into it
                        Rc::decrement_strong_count(ptr);

                        // access an inner Rc and drop something:
                        head = (*ptr).try_get_mut() // Rc being deref'd known to have 1 ref
                            .unwrap_unchecked() // known to be Some by cycle check
                            .next
                            .take();
                    }
                }
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

    pub fn cons<F>(f: F, lst: &Self) -> ThunkList<T> 
        where T: 'static,
              F: Thunkable<Item = T> + 'static
    {
        lst.pushed(f)
    }
    pub fn cons_known(t: T, lst: &Self) -> ThunkList<T>
        where T: 'static
    {
        lst.pushed_known(t)
    }
    pub fn cons_cyclic<F>(f: F) -> ThunkList<T> 
        where T: 'static,
              F: Thunkable<Item = T> + 'static
    {
        let next = Rc::new(Thunk::undef().boxed());
        let node = Node {
            val: Rc::new(Thunk::new(f).boxed()),
            next: Some(Rc::clone(&next)),
        };
        next.set(node.clone())
            .ok()
            .expect("Thunk::undef should have been empty");

        ThunkList { head: Some(node) }
    }

    fn pushed<F>(&self, f: F) -> ThunkList<T> 
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
    fn pushed_known(&self, t: T) -> ThunkList<T> 
        where T: 'static
    {
        self.pushed(Thunk::of(t))
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
    pub fn get(&self, n: usize) -> Option<&ThunkAny<'static, T>> {
        self.iter().nth(n)
    }
    pub fn get_forced(&self, n: usize) -> Option<&T> {
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

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::Thunk;

    use super::ThunkList;

    #[test]
    fn conner() {
        let t = ThunkList::new();
        let u = ThunkList::cons_known(2usize, &ThunkList::cons_known(1usize, &t));
        let mut ui = u.iter();

        assert_eq!(ui.next().map(Thunk::force), Some(&2));
        assert_eq!(ui.next().map(Thunk::force), Some(&1));
        assert_eq!(ui.next().map(Thunk::force), None);
    }

    #[test]
    fn cc() {
        let t: usize = 0;
        let lst = ThunkList::cons_cyclic(Thunk::of(t));
        let ptr = Rc::downgrade(&lst.head.as_ref().unwrap().val);

        // println!("rc count: {}", Rc::strong_count(&lst.head.as_ref().unwrap().val));
        let first_ten: Vec<_> = lst.iter()
            .take(10)
            .map(Thunk::force)
            .copied()
            .collect();
        assert_eq!(first_ten, [t; 10]);

        std::mem::drop(lst);
        assert!(ptr.upgrade().is_none(), "rc still exists, strong count: {}", ptr.strong_count() - 1);
    }
}