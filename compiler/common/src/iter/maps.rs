pub use std::collections::HashMap;
use std::hash;

use indexmap::map;
pub use indexmap::IndexMap;

use super::sets::Set;

pub type MapIter<'a, K, V> = map::Iter<'a, K, V>;
pub type MapIterMut<'a, K, V> = map::IterMut<'a, K, V>;
pub type MapIntoIter<K, V> = map::IntoIter<K, V>;

/// A thin wrapper around an `IndexMap`.
pub struct Map<K, V>(IndexMap<K, V>);

impl<K, V> Default for Map<K, V> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<K, V> Map<K, V>
where
    K: Eq + hash::Hash,
{
    pub fn new() -> Self {
        Default::default()
    }

    #[inline]
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

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn iter(&self) -> map::Iter<K, V> {
        self.0.iter()
    }

    pub fn into_iter(self) -> map::IntoIter<K, V> {
        self.0.into_iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> map::IterMut<K, V> {
        self.0.iter_mut()
    }

    #[inline]
    pub fn inner(&self) -> &IndexMap<K, V> {
        &self.0
    }

    #[inline]
    pub fn inner_mut(&mut self) -> &mut IndexMap<K, V> {
        &mut self.0
    }

    #[inline]
    pub fn into_inner(self) -> IndexMap<K, V> {
        self.0
    }

    #[inline]
    pub fn get(&self, key: &K) -> Option<&V> {
        self.0.get(key)
    }

    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.0.insert(key, value)
    }

    pub fn key_set(&self) -> Set<&K> {
        self.keys().collect()
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

    type IntoIter = map::IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        Map::into_iter(self)
    }
}

impl<K, V> std::ops::Index<&K> for Map<K, V>
where
    K: Eq + hash::Hash,
{
    type Output = V;

    fn index(&self, index: &K) -> &Self::Output {
        self.get(index).expect("Map: nonexistent key used as index")
    }
}

#[test]
fn test_indexmap_idx() {
    #[derive(Clone, PartialEq, Eq, Hash)]
    struct It<X>(X);

    let mut map = Map::new();
    map.insert(It('z'), 16);
    map.insert(It('y'), 51);
    assert_eq!(&map[&It('z')], &16);
    assert_eq!(&map[&It('y')], &51);
}
