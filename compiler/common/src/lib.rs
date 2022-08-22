// remove when no longer on nightly!
// #![feature(explicit_generic_args_with_impl_trait)]
// #![feature(generic_associated_types)]

pub use serde;

pub mod either;
pub mod functor;
pub mod iter;
mod macros;
pub mod mapstack;
pub mod newtypes;
pub mod text;

// pub use functor::Mappable;
pub use iter::{
    deque::{Deque, VecDeque},
    HashMap, HashSet, Hashable, Map, Set,
};

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
