// remove when no longer on nightly!
// #![feature(explicit_generic_args_with_impl_trait)]
#![feature(generic_associated_types)]

pub use std::collections::{HashMap as Map, HashSet as Set, VecDeque as Deque};

pub use serde;

pub mod data;
pub mod either;
pub mod functor;
pub mod iter;
pub mod mapstack;
pub mod newtypes;
pub mod pretty;
pub mod text;

pub use functor::Mappable;

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
///
/// # Example
/// ```
/// use wy_common::variant_preds;
///
/// enum Foo<X, Y> {
///     Bar,
///     Baz { baz: X, count: usize },
///     Barbaz(X, Y)
/// }
///
/// variant_preds! {
///     |X, Y| Foo[X, Y]
///     | is_bar => Bar
///     | is_baz => Baz {..}
///     | is_barbaz => Barbaz (..)
///     | is_baz_with_count_zero => Baz { count: 0, .. }
///     | is_baz_with_even_count => Baz { count, .. } [if count % 2 == 0]
/// }
/// ```
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
