use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Link<T>(pub Box<[T; 2]>);

impl<T> Link<T> {
    pub fn new(left: T, right: T) -> Self {
        Link(Box::new([left, right]))
    }

    pub fn from_parts((left, right): (T, T)) -> Self {
        Link(Box::new([left, right]))
    }

    pub fn left(&self) -> &T {
        &self.0.as_ref()[0]
    }

    pub fn left_mut(&mut self) -> &mut T {
        &mut self.as_mut()[0]
    }

    pub fn right(&self) -> &T {
        &self.0.as_ref()[1]
    }

    pub fn right_mut(&mut self) -> &mut T {
        &mut self.as_mut()[1]
    }

    pub fn array(&self) -> &[T; 2] {
        self.0.as_ref()
    }

    pub fn as_slice(&self) -> &[T] {
        &(self.0.as_ref()[..])
    }

    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.0.as_ref().iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.0.as_mut().iter_mut()
    }

    pub fn tuple(&self) -> (&T, &T) {
        let [a, b] = self.as_ref();
        (a, b)
    }

    pub fn parts(self) -> (T, T) {
        let [a, b] = *self.0;
        (a, b)
    }

    pub fn as_mut(&mut self) -> &mut [T; 2] {
        self.0.as_mut()
    }

    pub fn flip(&mut self) {
        let [l, r] = self.as_mut();
        std::mem::swap(l, r)
    }

    pub fn map_both<F, U>(self, mut f: F) -> Link<U>
    where
        F: FnMut(T) -> U,
    {
        let (l, r) = self.parts();
        Link::new(f(l), f(r))
    }

    pub fn map_both_ref<F, U>(&self, mut f: F) -> Link<U>
    where
        F: FnMut(&T) -> U,
    {
        Link::new(f(self.left()), f(self.right()))
    }

    pub fn map_both_mut<F, U>(&mut self, mut f: F) -> Link<U>
    where
        F: FnMut(&mut T) -> U,
    {
        Link::new(f(self.left_mut()), f(self.right_mut()))
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
        self.0.as_mut()
    }
}

impl<T> AsRef<[T; 2]> for Link<T> {
    fn as_ref(&self) -> &[T; 2] {
        self.0.as_ref()
    }
}

impl<T> std::ops::Index<usize> for Link<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        if index % 2 == 0 {
            self.left()
        } else {
            self.right()
        }
    }
}

impl<T> std::ops::Index<(usize, usize)> for Link<Link<T>> {
    type Output = T;

    fn index(&self, (a, b): (usize, usize)) -> &Self::Output {
        &(&self[a])[b]
    }
}
