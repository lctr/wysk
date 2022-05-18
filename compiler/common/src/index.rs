use std::hash::Hash;

/// The `Pointer` trait exposes a basic interface for dealing with `usize`
/// newtypes.
pub trait Pointer: Copy + Eq + Hash + std::fmt::Debug + 'static {
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

impl Pointer for usize {
    #[inline]
    fn new(n: usize) -> Self {
        n
    }

    #[inline]
    fn as_usize(self) -> usize {
        self
    }
}

impl Pointer for u32 {
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

impl<P: Pointer, T> std::ops::Index<P> for Vector<P, T> {
    type Output = T;

    fn index(&self, index: P) -> &Self::Output {
        &self.vec[index.as_usize()]
    }
}

impl<P: Pointer, T> std::ops::IndexMut<P> for Vector<P, T> {
    fn index_mut(&mut self, index: P) -> &mut Self::Output {
        &mut self.vec[index.as_usize()]
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Vector<P: Pointer, T> {
    pub vec: Vec<T>,
    _ptr: std::marker::PhantomData<fn(&P)>,
}

impl<P: Pointer, T> std::fmt::Debug for Vector<P, T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.vec, f)
    }
}

impl<P: Pointer, T> Vector<P, T> {
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

// This is safe to do since Vector<P, T> being `Send` only depends on `T` being
// `Send`, i.e., the `_ptr` (PhantomData) field is ignored.
unsafe impl<P: Pointer, T> Send for Vector<P, T> where T: Send {}
