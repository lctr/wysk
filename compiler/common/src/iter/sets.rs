use core::fmt;
pub use std::collections::HashSet;
use std::{collections::hash_map::RandomState, hash};

use indexmap::set;
pub use indexmap::IndexSet;

/// A thin wrapper around an `IndexSet`.
pub struct Set<K>(IndexSet<K>);
pub type SetIter<'a, K> = set::Iter<'a, K>;
pub type SetIntoIter<K> = set::IntoIter<K>;
pub type SetDiff<'a, T, S = RandomState> = set::Difference<'a, T, S>;
pub type SetUnion<'a, T, S = RandomState> = set::Union<'a, T, S>;
pub type SetXor<'a, T, S1 = RandomState, S2 = RandomState> =
    set::SymmetricDifference<'a, T, S1, S2>;
pub type SetIntersection<'a, T, S = RandomState> = set::Intersection<'a, T, S>;

impl<K> Default for Set<K> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<K> Set<K>
where
    K: Eq + hash::Hash,
{
    pub fn new() -> Self {
        Default::default()
    }

    #[inline]
    pub fn with_capacity(n: usize) -> Self {
        Self(IndexSet::with_capacity(n))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn iter(&self) -> SetIter<K> {
        self.0.iter()
    }

    #[inline]
    pub fn into_iter(self) -> SetIntoIter<K> {
        self.0.into_iter()
    }

    #[inline]
    pub fn difference<'a>(&'a self, other: &'a Self) -> SetDiff<K> {
        self.0.difference(other.inner())
    }

    #[inline]
    pub fn union<'a>(&'a self, other: &'a Self) -> SetUnion<K> {
        self.0.union(other.inner())
    }

    #[inline]
    pub fn symmetric_difference<'a>(&'a self, other: &'a Self) -> SetXor<K> {
        self.0.symmetric_difference(other.inner())
    }

    #[inline]
    pub fn intersection<'a>(&'a self, other: &'a Self) -> SetIntersection<K> {
        self.0.intersection(other.inner())
    }

    #[inline]
    pub fn is_subset(&self, other: &Self) -> bool {
        self.0.is_subset(other.inner())
    }

    #[inline]
    pub fn is_superset(&self, other: &Self) -> bool {
        self.0.is_superset(other.inner())
    }

    #[inline]
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.0.is_disjoint(other.inner())
    }

    #[inline]
    pub fn is_equal(&self, other: &Self) -> bool {
        self.0.is_subset(other.inner()) && self.0.is_superset(other.inner())
    }

    pub fn multi_intersection<'a>(
        &'a self,
        other: impl IntoIterator<Item = &'a Self>,
    ) -> MultiIntersect<'a, K> {
        // the `left` should be the smallest of them all
        let (left, _, right) =
            other
                .into_iter()
                .fold((self, self.len(), vec![]), |(this, len, mut others), c| {
                    let clen = c.len();
                    if clen < len {
                        others.push(this);
                        (c, clen, others)
                    } else {
                        others.push(c);
                        (this, len, others)
                    }
                });
        MultiIntersect {
            left: left.iter(),
            right,
        }
    }

    #[inline]
    pub fn inner(&self) -> &IndexSet<K> {
        &self.0
    }

    #[inline]
    pub fn inner_mut(&mut self) -> &mut IndexSet<K> {
        &mut self.0
    }

    #[inline]
    pub fn into_inner(self) -> IndexSet<K> {
        self.0
    }
}

impl<K> std::fmt::Debug for Set<K>
where
    K: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        IndexSet::fmt(&self.0, f)
    }
}

impl<K> Clone for Set<K>
where
    K: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<K> PartialEq for Set<K>
where
    K: Eq + hash::Hash,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K> std::ops::Deref for Set<K> {
    type Target = IndexSet<K>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K> std::ops::DerefMut for Set<K> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<K, I> From<I> for Set<K>
where
    IndexSet<K>: From<I>,
{
    fn from(i: I) -> Self {
        Set(IndexSet::from(i))
    }
}

impl<K> FromIterator<K> for Set<K>
where
    K: Eq + hash::Hash,
{
    fn from_iter<T: IntoIterator<Item = K>>(iter: T) -> Self {
        Self(IndexSet::from_iter(iter))
    }
}

impl<K> IntoIterator for Set<K> {
    type Item = K;

    type IntoIter = set::IntoIter<K>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<K> std::ops::Index<usize> for Set<K> {
    type Output = K;

    fn index(&self, index: usize) -> &Self::Output {
        self.get_index(index).unwrap()
    }
}

pub struct MultiIntersect<'a, T> {
    left: SetIter<'a, T>,
    right: Vec<&'a Set<T>>,
}

impl<'a, T: Eq + hash::Hash> MultiIntersect<'a, T> {
    /// Appends a reference to the set `other` to the vector of sets
    /// over which the intersections will be taken. If `other` is a
    /// subset of any of the existing sets, then this does nothing.
    pub fn intersect(&mut self, other: &'a Set<T>) {
        if {
            !self
                .right
                .as_slice()
                .into_iter()
                .any(|set| other.is_subset(*set))
        } {
            self.right.push(other)
        }
    }
}

impl<'a, T: Clone> Clone for MultiIntersect<'a, T> {
    fn clone(&self) -> Self {
        Self {
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }
}

impl<'a, T: fmt::Debug> fmt::Debug for MultiIntersect<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MultiIntersect")
            .field("left", &self.left)
            .field("right", &self.right)
            .finish()
    }
}

impl<'a, T: Eq + hash::Hash> Iterator for MultiIntersect<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let mut rest = self.right.as_slice().into_iter();
        while let Some(item) = self.left.next() {
            if rest.all(|set| set.contains(item)) {
                return Some(item);
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.left.size_hint().1)
    }
}
