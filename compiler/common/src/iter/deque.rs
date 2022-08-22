pub use std::collections::VecDeque;
use std::hash;

/// A thin wrapper around a `VecDeque`.
pub struct Deque<T>(pub VecDeque<T>);

impl<T> Deque<T> {
    pub fn new() -> Deque<T> {
        Deque(VecDeque::new())
    }

    #[inline]
    pub fn make_contiguous(&mut self) -> &mut [T] {
        self.0.make_contiguous()
    }

    #[inline]
    pub fn as_slices(&self) -> (&[T], &[T]) {
        self.0.as_slices()
    }

    #[inline]
    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        self.0.as_mut_slices()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[inline]
    pub fn front(&self) -> Option<&T> {
        self.0.front()
    }

    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.0.front_mut()
    }

    #[inline]
    pub fn back(&self) -> Option<&T> {
        self.0.back()
    }

    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.0.back_mut()
    }

    #[inline]
    pub fn push_front(&mut self, value: T) {
        self.0.push_front(value)
    }

    #[inline]
    pub fn push_back(&mut self, value: T) {
        self.0.push_back(value)
    }

    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        self.0.pop_front()
    }

    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        self.0.pop_back()
    }

    #[inline]
    pub fn rotate_left(&mut self, mid: usize) {
        self.0.rotate_left(mid)
    }

    #[inline]
    pub fn rotate_right(&mut self, mid: usize) {
        self.0.rotate_right(mid)
    }

    #[inline]
    pub fn contains(&self, item: &T) -> bool
    where
        T: PartialEq,
    {
        self.0.contains(item)
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.0.get(index)
    }

    #[inline]
    pub fn iter(&self) -> std::collections::vec_deque::Iter<T> {
        self.0.iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> std::collections::vec_deque::IterMut<T> {
        self.0.iter_mut()
    }

    #[inline]
    pub fn into_iter(self) -> std::collections::vec_deque::IntoIter<T> {
        self.0.into_iter()
    }

    #[inline]
    pub fn clear(&mut self) {
        self.0.clear()
    }

    pub fn reverse(&mut self) {
        let mut temp = Self::new();
        while let Some(t) = self.pop_back() {
            temp.push_back(t)
        }
        *self = temp;
    }

    pub fn inner(&self) -> &VecDeque<T> {
        &self.0
    }
    pub fn inner_mut(&mut self) -> &mut VecDeque<T> {
        &mut self.0
    }
    pub fn into_inner(self) -> VecDeque<T> {
        self.0
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
        Deque::into_iter(self)
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

#[macro_export]
macro_rules! deque {
    () => {
        $crate::__force_expr_frag!(
            $crate::iter::deque::Deque::new()
        )
    };
    ($($e:expr),+ $(,)?) => {{
        $crate::__force_expr_frag!(
            $crate::iter::deque::Deque::from_iter([$($e),+])
        )
    }};
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_deque_macro() {
        assert_eq!(deque!(1, 2, 3).into_inner(), VecDeque::from_iter([1, 2, 3]));
        assert_eq!(deque![], Deque::<()>::new())
    }
}
