pub use std::collections::{HashMap as Map, HashSet as Set, VecDeque as Deque};
use std::hash::{self, Hash};

use crate::Mappable;

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
    fn associate<V>(self, v: V) -> (Self, V) {
        (self, v)
    }

    #[inline]
    fn hashset_from(items: impl IntoIterator<Item = Self>) -> Set<Self> {
        items.into_iter().collect::<Set<_>>()
    }

    #[inline]
    fn hashmap_from<V>(entries: impl IntoIterator<Item = (Self, V)>) -> Map<Self, V> {
        entries.into_iter().collect::<Map<_, _>>()
    }

    #[inline]
    fn envr_from<V>(entries: impl IntoIterator<Item = (Self, V)>) -> Envr<Self, V> {
        Envr {
            store: entries.into_iter().collect(),
        }
    }

    #[inline]
    fn hashmap_from_filtered_keys<V>(
        pairs: impl IntoIterator<Item = (Option<Self>, V)>,
    ) -> Map<Self, V> {
        pairs
            .into_iter()
            .filter_map(|(k, v)| k.map(|k| (k, v)))
            .collect()
    }

    #[inline]
    fn hashmap_from_filtered<V>(
        pairs: impl IntoIterator<Item = Option<(Self, V)>>,
    ) -> Map<Self, V> {
        pairs.into_iter().filter_map(|x| x).collect()
    }

    #[inline]
    fn hashmap_from_filtered_values<V>(
        pairs: impl IntoIterator<Item = (Self, Option<V>)>,
    ) -> Map<Self, V> {
        pairs
            .into_iter()
            .filter_map(|(k, v)| v.map(|v| (k, v)))
            .collect()
    }

    #[inline]
    fn hashmap_from_filtered_pairs<V>(
        pairs: impl IntoIterator<Item = (Option<Self>, Option<V>)>,
    ) -> Map<Self, V> {
        pairs
            .into_iter()
            .filter_map(|(k, v)| k.and_then(|k| v.map(|v| (k, v))))
            .collect()
    }
}

impl<T> Hashable for T where T: Eq + hash::Hash {}

#[derive(Clone)]
pub struct Envr<K, V> {
    pub store: Map<K, V>,
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
        Self { store: Map::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            store: Map::with_capacity(capacity),
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
            store: iter.into_iter().collect::<Map<_, _>>(),
        }
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for Envr<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Envr {
            store: iter.into_iter().collect::<Map<_, _>>(),
        }
    }
}

impl<K, V> AsRef<Map<K, V>> for Envr<K, V> {
    fn as_ref(&self) -> &Map<K, V> {
        &self.store
    }
}

impl<K, V> std::ops::Deref for Envr<K, V> {
    type Target = Map<K, V>;

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
    Map<K, V>: std::ops::Index<K>,
{
    type Output = <Map<K, V> as std::ops::Index<K>>::Output;

    fn index(&self, index: K) -> &Self::Output {
        &self.store[index]
    }
}

impl<K, V> std::ops::IndexMut<K> for Envr<K, V>
where
    Map<K, V>: std::ops::IndexMut<K>,
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
        use crate::pretty::Dictionary;
        if f.alternate() {
            write!(f, "Envr {:#?}", self.as_ref())
        } else {
            write!(f, "Envr {:?}", &Dictionary(self.as_ref()))
        }
    }
}

impl<K, V> std::fmt::Display for Envr<K, V>
where
    K: std::fmt::Display,
    V: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Envr {}", crate::pretty::Dictionary(self.as_ref()))
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
