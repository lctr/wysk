// remove when no longer on nightly!
// #![feature(explicit_generic_args_with_impl_trait)]
#![feature(generic_associated_types)]

pub use std::collections::{HashMap as Map, HashSet as Set, VecDeque as Deque};

pub use serde;

pub mod either;
pub mod functor;
pub mod integral;
pub mod iter;
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

/// Given some initial value `a` an iterator and a binary function `f`, this
/// returns the folding
/// `f(...(f(f(f(a, c_0), c_1), c_2), c_3), ..., c_n)`
///
/// # Example
/// ```
/// use wy_common::fold_left;
/// let things = "abcde".chars();
/// let plus = |x, y| format!("({} + {})", x, y);
/// let folded = fold_left(things, String::from("1"), plus);
/// let expected = "(((((1 + a) + b) + c) + d) + e)";
/// assert_eq!(folded.as_str(), expected)
/// ```
#[inline]
pub fn fold_left<I: Iterator, A>(iter: I, init: A, f: impl FnMut(A, I::Item) -> A) -> A {
    iter.fold(init, f)
}

/// Given some initial value `a` an iterator and a binary function `f`, this
/// returns the folding `f(c_0, f(c_1, f(c_2, f(..., f(c_n, a))...)))`
///
/// # Example
/// ```
/// use wy_common::fold_right;
/// let things = "abcde".chars();
/// let plus = |x, y| format!("({} + {})", x, y);
/// let folded = fold_right(things, String::from("1"), plus);
/// let expected = "(a + (b + (c + (d + (e + 1)))))";
/// assert_eq!(folded.as_str(), expected)
/// ```
#[inline]
pub fn fold_right<I: DoubleEndedIterator, A>(
    iter: I,
    init: A,
    mut f: impl FnMut(I::Item, A) -> A,
) -> A {
    iter.rev().fold(init, |a, c| f(c, a))
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

/// Generates `.iter()` methods for the provided fields in a struct.
///
/// For example, a generic struct `Foo<X, Y>` with fields `bar` of type `Bar<X>`
/// and `baz` of type `Baz<Y>` would be implemented as following:
///
/// ```
/// struct Foo<X, Y> {
///     bar: Bar<X>,
///     baz: Baz<Y>,
/// }
///
/// struct_field_iters! {
///     |X, Y| Foo<X, Y>
///     | bar => get_bar :: Bar<X>
///     | baz => get_baz :: Baz<Y>
/// }
/// ```
#[macro_export]
macro_rules! struct_field_iters {
    (
        $(|$g0:ident $(, $gs:ident)*|)?
        $object:ty
        $(
           | $($($field:ident .)+)? # $rest:ident :: $ty:ty
        )+
    ) => {
        impl $(<$g0 $(, $gs)*>)? $object {
            $(
                #[inline]
                pub fn $rest(&self) -> std::slice::Iter<'_, $ty> {
                    self. $($($field .)+)? $rest.iter()
                }
            )+
        }
    };
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

/// Generates an implementation of getters for the fields provided.
///
/// For example, a generic struct `Foo<X, Y>` with fields `bar` of type `Bar<X>`
/// and `baz` of type `Baz<Y>` would be implemented as following:
///
/// ```
/// struct Foo<X, Y> {
///     bar: Bar<X>,
///     baz: Baz<Y>,
/// }
///
/// struct_getters! {
///     |X, Y| Foo<X, Y>
///     | bar => get_bar :: Bar<X>
///     | baz => get_baz :: Baz<Y>
/// }
/// ```
#[macro_export]
macro_rules! struct_getters {
    (
        $(|$g0:ident $(, $gs:ident)*|)?
        $object:ty
        $(
           | $($($field:ident.)+)? # $rest:ident :: $ty:ty
        )+
    ) => {
        impl $(<$g0 $(, $gs)*>)? $object {
            $(
                #[inline]
                pub fn $rest(&self) -> &$ty {
                    &self. $($($field.)+)? $rest
                }
            )+
        }
    };
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

/// Generating predicates for a given enum to test for variants.
#[macro_export]
macro_rules! variant_preds {
    (
        $(|$g0:ident $(, $gs:ident)*|)?
        $name:ident $([$($gss:tt)+])?
        $(
            $($(#[$com:meta])+)?
            | $method:ident => $variant:ident
                // really bad hack to get all shapes of enum variants
                $(($($args:tt)*))?
                $({ $($fields:tt)+ })?
                $([$($ts:tt)+])?
        )+
    ) => {
        impl $(<$g0 $(, $gs)*>)? $name $(<$($gss)+>)? {
            $(
                $($(#[$com])+)?
                #[inline]
                pub fn $method(&self) -> bool {
                    matches!(
                        self,
                        Self::$variant $(($($args)*))? $({ $($fields)+ })? $($($ts)+)?)
                }
            )+
        }
    };
}

pub fn unzip<X, Y>(mut zipped: impl Iterator<Item = (X, Y)>) -> (Vec<X>, Vec<Y>) {
    let mut xs = vec![];
    let mut ys = vec![];
    while let Some((x, y)) = zipped.next() {
        xs.push(x);
        ys.push(y)
    }
    (xs, ys)
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

pub fn push_if_absent<T: PartialEq>(mut acc: Vec<T>, t: T) -> Vec<T> {
    if !acc.contains(&t) {
        acc.push(t);
    }
    acc
}

/// Same functionality as the std macro `matches!`, but with arguments reversed,
/// i.e., pattern then expression as opposed to expression and then pattern.
#[macro_export]
macro_rules! case {
    ($pat:pat, $expr:expr) => {{
        if let $pat = $expr {
            true
        } else {
            false
        }
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = 2 + 2;
        let deq = deque![1, 22, 3, 3, 4];
        assert_eq!(result, deq[4]);
    }
}
