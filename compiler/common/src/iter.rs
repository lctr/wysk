pub use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{self, Hash};

use crate::Mappable;

use indexmap::{IndexMap, IndexSet};

/// A thin wrapper around an `IndexMap`.
pub struct Map<K, V>(IndexMap<K, V>);

impl<K, V> Map<K, V>
where
    K: Eq + hash::Hash,
{
    pub fn new() -> Self {
        Self(IndexMap::new())
    }

    pub fn with_capacity(n: usize) -> Self {
        Map(IndexMap::with_capacity(n))
    }

    pub fn new_without(&self, key: &K) -> Self
    where
        K: Clone + Eq + hash::Hash,
        V: Clone,
    {
        self.0
            .iter()
            .filter_map(|(k, v)| {
                if k != key {
                    Some((k.clone(), v.clone()))
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> indexmap::map::Iter<K, V> {
        self.0.iter()
    }

    pub fn into_iter(self) -> indexmap::map::IntoIter<K, V> {
        self.0.into_iter()
    }

    pub fn iter_mut(&mut self) -> indexmap::map::IterMut<K, V> {
        self.0.iter_mut()
    }
}

impl<K, V> Clone for Map<K, V>
where
    K: Clone + Eq + hash::Hash,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<K, V> std::fmt::Debug for Map<K, V>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        IndexMap::fmt(&self.0, f)
    }
}

impl<K, V> std::ops::Deref for Map<K, V> {
    type Target = IndexMap<K, V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K, V> std::ops::DerefMut for Map<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<K, V, I> From<I> for Map<K, V>
where
    IndexMap<K, V>: From<I>,
{
    fn from(i: I) -> Self {
        Map(IndexMap::from(i))
    }
}

impl<K, V> FromIterator<(K, V)> for Map<K, V>
where
    K: Eq + hash::Hash,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Self(IndexMap::from_iter(iter))
    }
}

impl<K, V> IntoIterator for Map<K, V>
where
    K: Eq + hash::Hash,
{
    type Item = (K, V);

    type IntoIter = indexmap::map::IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        Map::into_iter(self)
    }
}

/// A thin wrapper around an `IndexSet`.
pub struct Set<K>(IndexSet<K>);

impl<K> Set<K> {
    pub fn new() -> Self {
        Self(IndexSet::new())
    }

    pub fn with_capacity(n: usize) -> Self {
        Self(IndexSet::with_capacity(n))
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> indexmap::set::Iter<K> {
        self.0.iter()
    }
    pub fn into_iter(self) -> indexmap::set::IntoIter<K> {
        self.0.into_iter()
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

    type IntoIter = indexmap::set::IntoIter<K>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// A thin wrapper around a `VecDeque`.
pub struct Deque<T>(pub VecDeque<T>);

impl<T> Deque<T> {
    pub fn new() -> Deque<T> {
        Deque(VecDeque::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn front(&self) -> Option<&T> {
        self.0.front()
    }

    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.0.front_mut()
    }

    pub fn back(&self) -> Option<&T> {
        self.0.back()
    }

    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.0.back_mut()
    }

    pub fn push_front(&mut self, value: T) {
        self.0.push_front(value)
    }

    pub fn push_back(&mut self, value: T) {
        self.0.push_back(value)
    }

    pub fn pop_front(&mut self) -> Option<T> {
        self.0.pop_front()
    }

    pub fn pop_back(&mut self) -> Option<T> {
        self.0.pop_back()
    }

    pub fn rotate_left(&mut self, mid: usize) {
        self.0.rotate_left(mid)
    }

    pub fn rotate_right(&mut self, mid: usize) {
        self.0.rotate_right(mid)
    }

    pub fn contains(&self, item: &T) -> bool
    where
        T: PartialEq,
    {
        self.0.contains(item)
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.0.get(index)
    }

    pub fn iter(&self) -> std::collections::vec_deque::Iter<T> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> std::collections::vec_deque::IterMut<T> {
        self.0.iter_mut()
    }

    pub fn reverse(&mut self) {
        let mut temp = Self::new();
        while let Some(t) = self.pop_back() {
            temp.push_back(t)
        }
        *self = temp;
    }
}

impl<T> Clone for Deque<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> std::fmt::Debug for Deque<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()
    }
}

impl<T> PartialEq for Deque<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<T> Eq for Deque<T> where T: Eq {}

impl<T> hash::Hash for Deque<T>
where
    T: hash::Hash,
{
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T> Default for Deque<T> {
    fn default() -> Self {
        Deque::new()
    }
}

impl<'de, T> serde::Deserialize<'de> for Deque<T>
where
    T: serde::Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        <VecDeque<T> as serde::Deserialize>::deserialize(deserializer).map(Deque)
    }
}

impl<T> serde::Serialize for Deque<T>
where
    T: serde::Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<T> Mappable<T> for Deque<T> {
    type M<A> = Deque<A>;

    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(T) -> Y,
    {
        Deque(self.0.into_iter().map(f).collect())
    }
}

impl<T, I> From<I> for Deque<T>
where
    VecDeque<T>: From<I>,
{
    fn from(i: I) -> Self {
        Self(VecDeque::from(i))
    }
}

impl<T> FromIterator<T> for Deque<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Deque(VecDeque::from_iter(iter))
    }
}

impl<T> IntoIterator for Deque<T> {
    type Item = T;

    type IntoIter = std::collections::vec_deque::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Deque<T> {
    type Item = &'a T;

    type IntoIter = std::collections::vec_deque::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<T> Extend<T> for Deque<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.0.extend(iter)
    }
}

impl<T> std::ops::Index<usize> for Deque<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl<T> std::ops::IndexMut<usize> for Deque<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

pub fn unzip_vec<X, Y>(pairs: Vec<(X, Y)>) -> (Vec<X>, Vec<Y>) {
    pairs
        .into_iter()
        .fold((vec![], vec![]), |(mut xs, mut ys), (x, y)| {
            xs.push(x);
            ys.push(y);
            (xs, ys)
        })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Link<T>(pub Box<[T; 2]>);

impl<T> Link<T> {
    pub fn new(left: T, right: T) -> Self {
        Link(Box::new([left, right]))
    }

    pub fn from_pair((left, right): (T, T)) -> Self {
        Link(Box::new([left, right]))
    }

    pub fn left(&self) -> &T {
        &self.0.as_ref()[0]
    }

    pub fn right(&self) -> &T {
        &self.0.as_ref()[1]
    }

    pub fn array(&self) -> &[T; 2] {
        self.0.as_ref()
    }

    pub fn tuple(&self) -> (&T, &T) {
        let [a, b] = self.as_ref();
        (a, b)
    }

    pub fn to_pair(self) -> (T, T) {
        let [a, b] = *self.0;
        (a, b)
    }

    pub fn as_mut(&mut self) -> &mut [T; 2] {
        self.0.as_mut()
    }
}

impl<T> From<(T, T)> for Link<T> {
    fn from((left, right): (T, T)) -> Self {
        Link::new(left, right)
    }
}

impl<T> From<[T; 2]> for Link<T> {
    fn from(ts: [T; 2]) -> Self {
        Link(Box::new(ts))
    }
}

impl<T> IntoIterator for Link<T> {
    type Item = T;

    type IntoIter = std::array::IntoIter<T, 2>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T> std::ops::Deref for Link<T> {
    type Target = [T; 2];

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl<T> std::ops::DerefMut for Link<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut()
    }
}

impl<T> AsRef<[T; 2]> for Link<T> {
    fn as_ref(&self) -> &[T; 2] {
        self.0.as_ref()
    }
}

/// An infinite iterator over numeric values. Used to generate fresh values
/// corresponding to new states. Functionally equivalent to `std::ops::Range`
/// iterator with no upper-bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Counter(Count);
type Count = usize;
impl Counter {
    pub const fn new() -> Self {
        Self(0)
    }
    pub fn new_from(n: impl Into<Count>) -> Self {
        Self(n.into())
    }
    pub const fn count(&self) -> Count {
        self.0
    }

    /// Returns a new `Counter` with the internal count value incremented.
    pub const fn tick(&self) -> Self {
        Self(self.0 + 1)
    }

    /// Returns a new `Counter` with the internal count value incremented by the
    /// given offset/count value `n`.
    pub const fn tick_by(&self, n: Count) -> Self {
        Self(self.0 + n)
    }

    /// Increments the internal count value, returning the old value prior to
    /// incrementing. To get the value *after* incrementing, use `incremented`.
    pub fn increment(&mut self) -> Count {
        let count = self.0;
        self.0 += 1;
        count
    }

    /// Increments the internal count value by the given offset `n`, returning
    /// the value held *before* incrementing. To return the value *after*
    /// incrementing, use `incremented_by`.
    pub fn increment_by(&mut self, n: Count) -> Count {
        let count = self.0;
        self.0 += n;
        count
    }

    /// Increments the internal count by 1 and returns the new inner count
    /// value.
    #[inline]
    pub fn incremented(&mut self) -> Count {
        self.0 += 1;
        self.0
    }

    /// Increments the internal count by the given count `n` and returns the new
    /// inner count value.
    #[inline]
    pub fn incremented_by(&mut self, n: Count) -> Count {
        self.0 += n;
        self.0
    }

    pub fn map<Y>(&self, mut f: impl FnMut(Count) -> Y) -> Y {
        f(self.0)
    }

    pub fn as_range(self) -> std::ops::RangeFrom<usize> {
        self.0..
    }
}

impl Iterator for Counter {
    type Item = Count;

    fn next(&mut self) -> Option<Self::Item> {
        self.0 += 1;
        Some(self.0)
    }
}

impl From<usize> for Counter {
    fn from(n: usize) -> Self {
        Self(n)
    }
}

impl From<u32> for Counter {
    fn from(n: u32) -> Self {
        Self(n as usize)
    }
}

impl<N: Into<Counter>> From<std::ops::RangeFrom<N>> for Counter {
    fn from(r: std::ops::RangeFrom<N>) -> Self {
        r.start.into()
    }
}

impl std::ops::RangeBounds<Count> for Counter {
    fn start_bound(&self) -> std::ops::Bound<&Count> {
        std::ops::Bound::Included(&self.0)
    }

    fn end_bound(&self) -> std::ops::Bound<&Count> {
        std::ops::Bound::Unbounded
    }
}

impl std::ops::Add for Counter {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl std::ops::AddAssign for Counter {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0
    }
}

/// Supertrait for types that may be stored in hashsets or in hashmaps as keys.
pub trait Hashable: Eq + hash::Hash
where
    Self: Sized,
{
    #[inline]
    fn hash_with(self, state: &mut impl hash::Hasher) {
        self.hash(state);
    }

    #[inline]
    fn pair_with<V>(self, v: V) -> (Self, V) {
        (self, v)
    }

    #[inline]
    fn hashset_from(items: impl IntoIterator<Item = Self>) -> HashSet<Self> {
        items.into_iter().collect::<HashSet<_>>()
    }

    #[inline]
    fn set_from(items: impl IntoIterator<Item = Self>) -> Set<Self> {
        items.into_iter().collect::<Set<_>>()
    }

    #[inline]
    fn hashmap_from<V>(entries: impl IntoIterator<Item = (Self, V)>) -> HashMap<Self, V> {
        entries.into_iter().collect::<HashMap<_, _>>()
    }

    #[inline]
    fn map_from<V>(entries: impl IntoIterator<Item = (Self, V)>) -> Map<Self, V> {
        entries.into_iter().collect::<Map<_, _>>()
    }

    #[inline]
    fn envr_from<V>(entries: impl IntoIterator<Item = (Self, V)>) -> Envr<Self, V> {
        Envr {
            store: entries.into_iter().collect(),
        }
    }
}

impl<T> Hashable for T where T: Eq + hash::Hash {}

#[derive(Clone)]
pub struct Envr<K, V> {
    pub store: HashMap<K, V>,
}

impl<K, V> Mappable<V> for Envr<K, V>
where
    K: Eq + Hash,
{
    type M<A> = Envr<K, A>;

    fn fmap<F, Y>(self, mut f: F) -> Self::M<Y>
    where
        F: FnMut(V) -> Y,
    {
        self.into_iter().map(|(k, v)| (k, f(v))).collect()
    }
}

impl<K, V> Envr<K, V>
where
    K: Eq + Hash,
{
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            store: HashMap::with_capacity(capacity),
        }
    }

    pub fn len(&self) -> usize {
        self.store.len()
    }

    pub fn has_key(&self, k: &K) -> bool {
        self.store.contains_key(k)
    }

    pub fn has_value(&self, v: &V) -> bool
    where
        V: PartialEq,
    {
        for (_, w) in self.iter() {
            if v == w {
                return true;
            }
        }
        false
    }

    /// Returns a clone with the entry for the given key removed. If the key did
    /// not exist, then this is equivalent to cloning.
    pub fn cloned_without(&self, k: &K) -> Self
    where
        K: Copy,
        V: Clone,
    {
        self.store
            .iter()
            .filter_map(|(id, v)| {
                if id != k {
                    Some((*id, v.clone()))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Returns an `Envr` containing key-value (reference) pairs found in *both*
    /// `Envr`s.
    pub fn intersect(&self, rhs: &Self) -> Envr<&K, &V>
    where
        V: PartialEq,
    {
        self.iter()
            .filter_map(|(k, v)| {
                rhs.get_key_value(k)
                    .and_then(|(_, v2)| if v == v2 { Some((k, v)) } else { None })
            })
            .fold(
                Envr::with_capacity(self.len().min(rhs.len())),
                |mut inter, (k, v)| {
                    inter.insert(k, v);
                    inter
                },
            )
    }

    /// Returns an `Envr` containing key-value (reference) pairs found in `Self`
    /// as well as in `other`. Since this is a `left` union, if a key exists in
    /// both `Envr`s, the left one (i.e., the one in `Self`) will take
    /// precedence.
    pub fn left_union<'a>(&'a self, other: &'a Self) -> Envr<&'a K, &'a V> {
        other.iter().chain(self.iter()).fold(
            Envr::with_capacity(self.len() + other.len()),
            |mut a, (k, v)| {
                a.insert(k, v);
                a
            },
        )
    }

    /// Returns an `Envr` containing key-value (reference) pairs found in `Self`
    /// as well as in `other`. Since this is a `right` union, if a key exists in
    /// both `Envr`s, the right one (i.e., the one in `other`) will take
    /// precedence.
    pub fn right_union<'a>(&'a self, other: &'a Self) -> Envr<&'a K, &'a V> {
        self.iter().chain(other.iter()).fold(
            Envr::with_capacity(self.len() + other.len()),
            |mut a, (k, v)| {
                a.insert(k, v);
                a
            },
        )
    }

    pub fn difference<'a>(&'a self, other: &'a Self) -> Envr<&'a K, &'a V> {
        self.iter().fold(Envr::new(), |mut a, (k, v)| {
            if !other.has_key(k) {
                a.insert(k, v);
            }
            a
        })
    }

    #[inline]
    pub fn iter(&self) -> std::collections::hash_map::Iter<'_, K, V> {
        self.store.iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> std::collections::hash_map::IterMut<'_, K, V> {
        self.store.iter_mut()
    }

    #[inline]
    pub fn into_iter(self) -> std::collections::hash_map::IntoIter<K, V> {
        self.store.into_iter()
    }

    #[inline]
    pub fn keys(&self) -> std::collections::hash_map::Keys<'_, K, V> {
        self.store.keys()
    }

    #[inline]
    pub fn values(&self) -> std::collections::hash_map::Values<'_, K, V> {
        self.store.values()
    }

    #[inline]
    pub fn entry(&mut self, k: K) -> std::collections::hash_map::Entry<'_, K, V> {
        self.store.entry(k)
    }
}

impl<K: Eq + Hash, V> Extend<(K, V)> for Envr<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        self.store.extend(iter)
    }
}

impl<K: Eq + Hash, V, I> From<I> for Envr<K, V>
where
    I: IntoIterator<Item = (K, V)>,
{
    fn from(iter: I) -> Self {
        Envr {
            store: iter.into_iter().collect::<HashMap<_, _>>(),
        }
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for Envr<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Envr {
            store: iter.into_iter().collect::<HashMap<_, _>>(),
        }
    }
}

impl<K, V> AsRef<HashMap<K, V>> for Envr<K, V> {
    fn as_ref(&self) -> &HashMap<K, V> {
        &self.store
    }
}

impl<K, V> std::ops::Deref for Envr<K, V> {
    type Target = HashMap<K, V>;

    fn deref(&self) -> &Self::Target {
        &self.store
    }
}

impl<K, V> std::ops::DerefMut for Envr<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.store
    }
}

impl<K, V> std::ops::Index<K> for Envr<K, V>
where
    HashMap<K, V>: std::ops::Index<K>,
{
    type Output = <HashMap<K, V> as std::ops::Index<K>>::Output;

    fn index(&self, index: K) -> &Self::Output {
        &self.store[index]
    }
}

impl<K, V> std::ops::IndexMut<K> for Envr<K, V>
where
    HashMap<K, V>: std::ops::IndexMut<K>,
{
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        &mut self.store[index]
    }
}

impl<K, V> std::fmt::Debug for Envr<K, V>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Envr").field("store", &self.store).finish()
    }
}

pub fn intersect_slices<'a, X: PartialEq>(left: &'a [X], right: &'a [X]) -> Vec<&'a X> {
    // given two collections X and Y, the intersection Z is the set of elements
    // such that for all z in Z, z is in X and z is in Y, hence it follows that
    // the cardinality |Z| of the intersection Z will be bounded above by the
    // minimum of the cardinalities |X| and |Y|, i.e.,
    //
    //      |intersection(X, Y)| <= min { |X|, |Y| }
    //
    // if X and Y are disjoint, then |Z| = 0. this allows us to optimize the
    // number of allocations down to a *maximum* of two: first we allocate for
    // the upper bound of the intersection, then upon completion, we shrink the
    // vector's capacity to fit. it is clear that, in the event the two
    // collections are *not* disjoint, we will only perform the initial
    // allocation.
    let mut inter = Vec::with_capacity(left.len().min(right.len()));
    for x in left {
        if right.contains(x) {
            inter.push(x)
        }
    }
    inter.shrink_to_fit();
    inter
}
