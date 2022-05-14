pub use std::collections::{HashMap as Map, HashSet as Set, VecDeque as Deque};

pub use serde;
pub mod mapstack;
pub mod newtypes;
pub mod text;

// TODO: Keep?
pub trait Foldable: Iterator {
    fn foldl<F, U>(mut self, init: U, mut f: F) -> U
    where
        Self: Sized,
        F: FnMut(U, Self::Item) -> U,
    {
        let mut acc = init;
        while let Some(t) = self.next() {
            acc = f(acc, t);
        }
        acc
    }

    fn foldr<F, U>(self, init: U, f: F) -> U
    where
        Self: Sized,
        F: FnMut(U, Self::Item) -> U,
    {
        let mut deq = Deque::new();
        self.for_each(|t| deq.push_front(t));
        deq.into_iter().fold(init, f)
    }

    fn map_accuml<F, U, V>(mut self, init: U, mut f: F) -> (U, Vec<V>)
    where
        Self: Sized,
        F: FnMut(U, Self::Item) -> (U, V),
    {
        let mut acc = init;
        let mut list = vec![];
        while let Some(t) = self.next() {
            let (u, v) = f(acc, t);
            acc = u;
            list.push(v);
        }
        (acc, list)
    }
}

#[macro_export]
macro_rules! deque {
    () => { $crate::Deque::new() };
    (
        $($ex0:expr $(, $expr:expr)*)+
    ) => {{
        let mut deq = $crate::Deque::new();
        $(
            deq.push_back($ex0);
            $(deq.push_back($expr);)*
        )+
        deq
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = 2 + 2;
        let deq = deque![1, 22, 3, 3, 4];
        assert_eq!(result, 4);
    }
}
