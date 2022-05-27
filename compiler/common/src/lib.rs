// remove when no longer on nightly!
// #![feature(explicit_generic_args_with_impl_trait)]
#![feature(generic_associated_types)]

pub use std::collections::{HashMap as Map, HashSet as Set, VecDeque as Deque};

pub use serde;

pub mod functor;
pub mod index;
pub mod mapstack;
pub mod newtypes;
pub mod pretty;
pub mod text;

pub use functor::Mappable;

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

#[macro_export]
macro_rules! struct_field_iters {
    (
        $(|$g0:ident $(, $gs:ident)*|)?
        $object:ty
        $(
           | $field:ident $(. $rest:ident)* => $method_name:ident :: $ty:ty
        )+
    ) => {
        impl $(<$g0 $(, $gs)*>)? $object {
            $(
                #[inline]
                pub fn $method_name(&self) -> std::slice::Iter<'_, $ty> {
                    self.$field $(.$rest)* .iter()
                }
            )+
        }
    };
}

#[macro_export]
macro_rules! struct_getters {
    (
        $(|$g0:ident $(, $gs:ident)*|)?
        $object:ty
        $(
           | $field:ident $(. $rest:ident)* => $method_name:ident :: $ty:ty
        )+
    ) => {
        impl $(<$g0 $(, $gs)*>)? $object {
            $(
                #[inline]
                pub fn $method_name(&self) -> &$ty {
                    &self.$field $(.$rest)*
                }
            )+
        }
    };
}

pub fn distribute<X: Copy, Y: Copy>(
    left: impl ExactSizeIterator + Iterator<Item = X>,
    mut right: impl ExactSizeIterator + Iterator<Item = Y>,
) -> Vec<(X, Y)> {
    // [x1, x2, ..., xn] x [y1, y2, ..., yn] = [(x1, y1), (x1, y2), ..., (x1,
    // yn), (x2, y1), ..., (x2, yn), ..., (xn, y1), ..., (xn, yn)]
    let mut pairs = Vec::with_capacity(left.len() * right.len());
    for x in left {
        for y in right.by_ref() {
            pairs.push((x, y))
        }
    }
    pairs
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
