#![allow(dead_code)]
use std::cell::Ref;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct LazyCell<T, F> {
    cell: Rc<RefCell<LazyCellInner<T, F>>>,
}

#[derive(Debug)]
pub enum LazyCellInner<T, F> {
    Unforced(F),
    Forced(T),
    Empty,
}

impl<T, F: FnOnce() -> T> LazyCell<T, F> {
    pub fn new(f: F) -> Self {
        Self {
            cell: Rc::new(RefCell::new(LazyCellInner::Unforced(f))),
        }
    }
    fn force(&self) {
        use self::LazyCellInner::*;
        let mut cell_ref = self.cell.borrow_mut();
        let val = match std::mem::replace(&mut *cell_ref, Empty) {
            Forced(t) => t,
            Unforced(f) => f(),
            Empty => unreachable!(),
        };
        *cell_ref = Forced(val);
    }
    pub fn borrow(&self) -> Ref<T> {
        use self::LazyCellInner::*;
        self.force();
        Ref::map(self.cell.borrow(), |inner| match inner {
            Forced(ref t) => t,
            _ => unreachable!(),
        })
    }
}

impl<T, F> std::convert::From<T> for LazyCell<T, F> {
    fn from(t: T) -> Self {
        Self {
            cell: Rc::new(RefCell::new(LazyCellInner::Forced(t))),
        }
    }
}
