// remove when no longer on nightly!
// #![feature(explicit_generic_args_with_impl_trait)]
#![feature(generic_associated_types)]

pub use std::collections::{HashMap as Map, HashSet as Set, VecDeque as Deque};

pub use serde;

pub mod index;
pub mod mapstack;
pub mod newtypes;
pub mod pretty;
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

pub trait Mappable<X> {
    type M<A>: Mappable<A>;
    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y;
}

impl<X> Mappable<X> for Vec<X> {
    type M<Y> = Vec<Y>;
    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        self.into_iter().map(f).collect()
    }
}

impl<X> Mappable<X> for Option<X> {
    type M<A> = Option<A>;

    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        self.map(f)
    }
}

impl<X, E> Mappable<X> for Result<X, E> {
    type M<A> = Result<A, E>;

    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        self.map(f)
    }
}

impl<X, const N: usize> Mappable<X> for [X; N] {
    type M<A> = [A; N];

    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        let mut array: [Y; N] = unsafe { std::mem::zeroed() };
        for (i, y) in self.into_iter().map(f).enumerate() {
            array[i] = y;
        }
        array
    }
}

impl<X> Mappable<X> for Box<X> {
    type M<A> = Box<A>;

    fn fmap<F, Y>(self, mut f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        Box::new(f(*self))
    }
}

pub fn map_vec<X, Y>(vec: Vec<X>, f: impl FnMut(X) -> Y) -> Vec<Y> {
    vec.fmap(f)
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
