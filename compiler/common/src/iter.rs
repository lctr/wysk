pub use std::collections::{HashMap as Map, HashSet as Set, VecDeque as Deque};
use std::hash::Hash;

use crate::Mappable;

/// The `Pointer` trait exposes a basic interface for dealing with `usize`
/// newtypes.
pub trait IdxPtr: Copy + Eq + Hash + std::fmt::Debug + 'static {
    fn new(n: usize) -> Self;

    fn as_usize(self) -> usize;

    fn plus(self, rhs: usize) -> Self {
        Self::new(self.as_usize() + rhs)
    }

    /// Generates a "new" pointer. Shortcut for `Self::plus(self, 1)`
    fn tick(self) -> Self {
        Self::new(self.as_usize() + 1)
    }

    fn increment_by(&mut self, dx: usize) {
        *self = self.plus(dx)
    }
}

impl IdxPtr for usize {
    #[inline]
    fn new(n: usize) -> Self {
        n
    }

    #[inline]
    fn as_usize(self) -> usize {
        self
    }
}

impl IdxPtr for u32 {
    #[inline]
    fn new(n: usize) -> Self {
        assert!(n <= u32::MAX as usize);
        n as u32
    }

    #[inline]
    fn as_usize(self) -> usize {
        self as usize
    }
}

impl<T, P: IdxPtr> std::ops::Index<P> for Vector<T, P> {
    type Output = T;

    fn index(&self, index: P) -> &Self::Output {
        &self.vec[index.as_usize()]
    }
}

impl<T, P: IdxPtr> std::ops::IndexMut<P> for Vector<T, P> {
    fn index_mut(&mut self, index: P) -> &mut Self::Output {
        &mut self.vec[index.as_usize()]
    }
}

pub struct Vector<T, P: IdxPtr> {
    pub vec: Vec<T>,
    _ptr: std::marker::PhantomData<fn(&P)>,
}

impl<T, P: IdxPtr> std::fmt::Debug for Vector<T, P>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.vec, f)
    }
}

impl<T, P: IdxPtr> Vector<T, P> {
    #[inline]
    pub fn new() -> Self {
        Self {
            vec: vec![],
            _ptr: std::marker::PhantomData,
        }
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        Self {
            vec,
            _ptr: std::marker::PhantomData,
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            vec: Vec::with_capacity(capacity),
            _ptr: std::marker::PhantomData,
        }
    }

    pub fn len(&self) -> usize {
        self.vec.len()
    }

    pub fn from_repeating_fn(f: impl FnMut(P) -> T, times: usize) -> Self {
        Self {
            vec: (0..times).map(P::new).map(f).collect(),
            _ptr: std::marker::PhantomData,
        }
    }

    pub fn get(&self, ptr: P) -> Option<&T> {
        self.vec.get(ptr.as_usize())
    }

    pub fn get_many<const N: usize>(&self, ptrs: [P; N]) -> [Option<&T>; N] {
        let mut many: [Option<&T>; N] = [None; N];
        for (i, p) in ptrs.into_iter().enumerate() {
            if let Some(t) = self.get(p) {
                many[i] = Some(t)
            }
        }
        many
    }

    pub fn get_mut(&mut self, ptr: P) -> Option<&mut T> {
        self.vec.get_mut(ptr.as_usize())
    }

    pub fn push(&mut self, t: T) -> P {
        let p = P::new(self.len());
        self.vec.push(t);
        p
    }

    pub fn pop(&mut self) -> Option<T> {
        self.vec.pop()
    }

    pub fn next_ptr(&self) -> P {
        P::new(self.len())
    }
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.vec.iter()
    }
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.vec.iter_mut()
    }
    pub fn into_iter(self) -> std::vec::IntoIter<T> {
        self.vec.into_iter()
    }
    pub fn iter_enumerated(
        &self,
    ) -> impl DoubleEndedIterator<Item = (P, &T)> + ExactSizeIterator + '_ {
        self.vec.iter().enumerate().map(|(p, t)| (P::new(p), t))
    }
    pub fn into_iter_enumerated(
        self,
    ) -> impl DoubleEndedIterator<Item = (P, T)> + ExactSizeIterator {
        self.vec
            .into_iter()
            .enumerate()
            .map(|(n, t)| (P::new(n), t))
    }

    pub fn pointers(&self) -> impl DoubleEndedIterator<Item = P> + ExactSizeIterator {
        (0..self.len()).map(P::new)
    }

    pub fn swap(&mut self, a: P, b: P) {
        self.vec.swap(a.as_usize(), b.as_usize())
    }
}

pub struct IntoIter<T>(std::vec::IntoIter<T>);

impl<T, P: IdxPtr> IntoIterator for Vector<T, P> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.into_iter())
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl<T, P: IdxPtr> Mappable<T> for Vector<T, P> {
    type M<A> = Vector<A, P>;

    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(T) -> Y,
    {
        Vector {
            vec: self.vec.fmap(f),
            _ptr: std::marker::PhantomData,
        }
    }
}

// This is safe to do since Vector<T, P> being `Send` only depends on `T` being
// `Send`, i.e., the `_ptr` (PhantomData) field is ignored.
unsafe impl<T, P: IdxPtr> Send for Vector<T, P> where T: Send {}

impl<T, P: IdxPtr> Clone for Vector<T, P>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            vec: self.vec.clone(),
            _ptr: self._ptr,
        }
    }
}

impl<T, P: IdxPtr> PartialEq for Vector<T, P>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.vec == other.vec
    }
}

impl<T, P: IdxPtr> Eq for Vector<T, P> where T: Eq {}

impl<T, P: IdxPtr> Hash for Vector<T, P>
where
    T: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.vec.hash(state);
        self._ptr.hash(state);
    }
}

pub fn push_unique<X: PartialEq>(vec: &mut Vec<X>, x: X) -> usize {
    vec.as_slice()
        .into_iter()
        .position(|it| it == &x)
        .unwrap_or_else(|| {
            let len = vec.len();
            vec.push(x);
            len
        })
}

/// Simple interface for types that are initialized with "empty" (or default,
/// though this is not strictly required) data.
///
/// Primarily used to abstract over containers.
pub trait New {
    fn new() -> Self;
    fn empty() -> Empty {
        Empty
    }
}
impl<T> New for Vec<T> {
    fn new() -> Self {
        Vec::new()
    }
}
impl<T> New for Set<T> {
    fn new() -> Self {
        Set::new()
    }
}
impl<K, V> New for Map<K, V> {
    fn new() -> Self {
        Map::new()
    }
}
impl<K, V> New for std::collections::BTreeMap<K, V> {
    fn new() -> Self {
        std::collections::BTreeMap::new()
    }
}
impl<T> New for std::collections::BTreeSet<T> {
    fn new() -> Self {
        std::collections::BTreeSet::new()
    }
}
impl<T: Ord> New for std::collections::BinaryHeap<T> {
    fn new() -> Self {
        std::collections::BinaryHeap::new()
    }
}
impl New for String {
    fn new() -> Self {
        String::new()
    }
}
impl<T> New for Option<T> {
    fn new() -> Self {
        None
    }
}
impl New for Empty {
    fn new() -> Self {
        Empty
    }
}

#[derive(Copy, Clone)]
pub struct Empty;
impl Empty {
    pub const fn marker<T>() -> std::marker::PhantomData<T> {
        std::marker::PhantomData
    }

    pub fn init<T: New>() -> T {
        T::new()
    }
}

impl Iterator for Empty {
    type Item = ();

    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

impl<T> From<Empty> for std::iter::Empty<T> {
    fn from(_: Empty) -> Self {
        std::iter::empty()
    }
}

impl<T> From<Empty> for Vec<T> {
    fn from(_: Empty) -> Self {
        Vec::new()
    }
}
impl<T> PartialEq<Vec<T>> for Empty {
    #[inline]
    fn eq(&self, other: &Vec<T>) -> bool {
        other.is_empty()
    }
}
impl<T> From<Empty> for Deque<T> {
    #[inline]
    fn from(_: Empty) -> Self {
        Deque::new()
    }
}
impl<K, V> From<Empty> for Map<K, V> {
    #[inline]
    fn from(_: Empty) -> Self {
        Map::new()
    }
}
impl<T> From<Empty> for Set<T> {
    #[inline]
    fn from(_: Empty) -> Self {
        Set::new()
    }
}
impl From<Empty> for String {
    #[inline]
    fn from(_: Empty) -> Self {
        String::new()
    }
}
