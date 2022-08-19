use std::collections::{BTreeSet, BinaryHeap, LinkedList};

use crate::{either::Either, iter::link::Link, iter::sets::Set, Deque, Map};

/// Defunctionalization type.
///
/// When mapping over generic types recursively, it's likely that
/// infinite types will be constructed by the compiler leading to a
/// stack overflow; this is because Rust will ascribe a fresh type for
/// each invocation of a given closure as it's passed through
/// recursively. Instead, we can wrap our closure in a `Func` and pass
/// in mutable to it to "functorial" methods, thus circumventing the
/// need to generate a new unique closure type at every call site!
///
/// The ergonomics aren't as *clean* as passing in a simple closure --
/// but it works ;)
pub enum Func<'a, F> {
    New(F),
    Cont(&'a mut Func<'a, F>),
}

impl<'a, F> Func<'a, F> {
    pub fn apply<A, B>(&mut self, arg: A) -> B
    where
        F: FnMut(A) -> B,
    {
        match self {
            Func::New(f) => f(arg),
            Func::Cont(f) => f.apply(arg),
        }
    }

    pub fn call<A, B>(self, arg: A) -> B
    where
        F: FnMut(A) -> B,
    {
        match self {
            Func::New(mut f) => f(arg),
            Func::Cont(f) => f.apply(arg),
        }
    }

    pub fn from_closure<A, B>(f: F) -> Self
    where
        F: FnMut(A) -> B,
    {
        Func::New(f)
    }

    pub fn identity<X>() -> Func<'a, impl FnMut(X) -> X> {
        Func::New(|x: X| x)
    }
}

impl<F, A, B> From<(F, [(A, B); 0])> for Func<'_, F>
where
    F: FnMut(A) -> B,
{
    fn from((f, _): (F, [(A, B); 0])) -> Self {
        Func::New(f)
    }
}

impl<F> std::ops::Deref for Func<'_, F> {
    type Target = F;

    fn deref(&self) -> &Self::Target {
        match self {
            Func::New(f) => f,
            Func::Cont(f) => &**f,
        }
    }
}

impl<F> std::ops::DerefMut for Func<'_, F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Func::New(f) => f,
            Func::Cont(f) => *f,
        }
    }
}

pub trait Functor<A, B> {
    type Wrapper: Functor<B, A>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B;

    fn mapped<F>(self, f: F) -> Self::Wrapper
    where
        Self: Sized,
        F: FnMut(A) -> B,
    {
        let mut f = Func::New(f);
        self.fmap(&mut f)
    }
}

impl<A, B> Functor<A, B> for Option<A> {
    type Wrapper = Option<B>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B,
    {
        self.map(|a| f.apply(a))
    }
}

impl<A, B> Functor<A, B> for Vec<A> {
    type Wrapper = Vec<B>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B,
    {
        self.into_iter().map(|a| f.apply(a)).collect()
    }
}

impl<A, B> Functor<A, B> for Box<A> {
    type Wrapper = Box<B>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B,
    {
        Box::new(f.apply(*self))
    }
}

impl<A, B> Functor<A, B> for Deque<A> {
    type Wrapper = Deque<B>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B,
    {
        self.into_iter().map(|a| f.apply(a)).collect()
    }
}

impl<A, B> Functor<A, B> for Set<A>
where
    A: Eq + std::hash::Hash,
    B: Eq + std::hash::Hash,
{
    type Wrapper = Set<B>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B,
    {
        self.into_iter().map(|a| f.apply(a)).collect()
    }
}

impl<A, B> Functor<A, B> for std::collections::hash_set::HashSet<A>
where
    A: Eq + std::hash::Hash,
    B: Eq + std::hash::Hash,
{
    type Wrapper = std::collections::hash_set::HashSet<B>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B,
    {
        self.into_iter().map(|a| f.apply(a)).collect()
    }
}

impl<A, B> Functor<A, B> for BTreeSet<A>
where
    A: Ord,
    B: Ord,
{
    type Wrapper = BTreeSet<B>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B,
    {
        self.into_iter().map(|a| f.apply(a)).collect()
    }
}

impl<A, B> Functor<A, B> for BinaryHeap<A>
where
    A: Ord,
    B: Ord,
{
    type Wrapper = BinaryHeap<B>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B,
    {
        self.into_iter().map(|a| f.apply(a)).collect()
    }
}

impl<A, B, C> Functor<A, C> for Either<A, B> {
    type Wrapper = Either<C, B>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> C,
    {
        match self {
            Either::Left(a) => Either::Left(f.apply(a)),
            Either::Right(b) => Either::Right(b),
        }
    }
}

impl<A, B> Functor<A, B> for Link<A> {
    type Wrapper = Link<B>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B,
    {
        let (a, b) = self.parts();
        Link::new(f.apply(a), f.apply(b))
    }
}

impl<A, B> Functor<A, B> for LinkedList<A> {
    type Wrapper = LinkedList<B>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B,
    {
        self.into_iter().map(|a| f.apply(a)).collect()
    }
}

impl<A, B, const N: usize> Functor<A, B> for [A; N] {
    type Wrapper = [B; N];

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B,
    {
        use std::mem;
        let mut arr: [B; N] = unsafe { mem::zeroed() };
        let mut i = 0;
        for a in self {
            arr[i] = f.apply(a);
            i += 1;
        }
        arr
    }
}

pub trait MapFst<A, B> {
    type WrapFst: MapFst<B, A>;
    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(A) -> B;
}

pub trait MapSnd<A, B> {
    type WrapSnd: MapSnd<B, A>;
    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(A) -> B;
}

pub trait MapThrd<A, B> {
    type WrapThrd: MapThrd<B, A>;
    fn map_thrd<F>(self, f: &mut Func<'_, F>) -> Self::WrapThrd
    where
        F: FnMut(A) -> B;
}

impl<A, B, C> MapFst<A, C> for (A, B) {
    type WrapFst = (C, B);

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(A) -> C,
    {
        let (a, b) = self;
        (f.apply(a), b)
    }
}

impl<A, B, C> MapSnd<B, C> for (A, B) {
    type WrapSnd = (A, C);

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(B) -> C,
    {
        let (a, b) = self;
        (a, f.apply(b))
    }
}

impl<A, B, C, D> MapFst<A, D> for (A, B, C) {
    type WrapFst = (D, B, C);

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(A) -> D,
    {
        let (a, b, c) = self;
        (f.apply(a), b, c)
    }
}

impl<A, B, C, D> MapSnd<B, D> for (A, B, C) {
    type WrapSnd = (A, D, C);

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(B) -> D,
    {
        let (a, b, c) = self;
        (a, f.apply(b), c)
    }
}

impl<A, B, C, D> MapThrd<C, D> for (A, B, C) {
    type WrapThrd = (A, B, D);

    fn map_thrd<F>(self, f: &mut Func<'_, F>) -> Self::WrapThrd
    where
        F: FnMut(C) -> D,
    {
        let (a, b, c) = self;
        (a, b, f.apply(c))
    }
}

impl<T, X, U> MapFst<X, U> for Option<T>
where
    T: MapFst<X, U>,
{
    type WrapFst = Option<T::WrapFst>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(X) -> U,
    {
        self.map(|t| t.map_fst(f))
    }
}

impl<T, Y, U> MapSnd<Y, U> for Option<T>
where
    T: MapSnd<Y, U>,
{
    type WrapSnd = Option<T::WrapSnd>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(Y) -> U,
    {
        self.map(|t| t.map_snd(f))
    }
}

impl<T, Z, U> MapThrd<Z, U> for Option<T>
where
    T: MapThrd<Z, U>,
{
    type WrapThrd = Option<T::WrapThrd>;

    fn map_thrd<F>(self, f: &mut Func<'_, F>) -> Self::WrapThrd
    where
        F: FnMut(Z) -> U,
    {
        self.map(|t| t.map_thrd(f))
    }
}

impl<T, X, U> MapFst<X, U> for Vec<T>
where
    T: MapFst<X, U>,
{
    type WrapFst = Vec<T::WrapFst>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(X) -> U,
    {
        self.into_iter().map(|t| t.map_fst(f)).collect()
    }
}

impl<T, Y, U> MapSnd<Y, U> for Vec<T>
where
    T: MapSnd<Y, U>,
{
    type WrapSnd = Vec<T::WrapSnd>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(Y) -> U,
    {
        self.into_iter().map(|t| t.map_snd(f)).collect()
    }
}

impl<T, Z, U> MapThrd<Z, U> for Vec<T>
where
    T: MapThrd<Z, U>,
{
    type WrapThrd = Vec<T::WrapThrd>;

    fn map_thrd<F>(self, f: &mut Func<'_, F>) -> Self::WrapThrd
    where
        F: FnMut(Z) -> U,
    {
        self.into_iter().map(|t| t.map_thrd(f)).collect()
    }
}

impl<X, E, U> MapFst<X, U> for Result<X, E> {
    type WrapFst = Result<U, E>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(X) -> U,
    {
        self.map(|x| f.apply(x))
    }
}

impl<X, E, U> MapSnd<E, U> for Result<X, E> {
    type WrapSnd = Result<X, U>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(E) -> U,
    {
        self.map_err(|e| f.apply(e))
    }
}

impl<A, B, U> MapFst<A, U> for Either<A, B> {
    type WrapFst = Either<U, B>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(A) -> U,
    {
        match self {
            Either::Left(a) => Either::Left(f.apply(a)),
            Either::Right(b) => Either::Right(b),
        }
    }
}

impl<A, B, U> MapSnd<B, U> for Either<A, B> {
    type WrapSnd = Either<A, U>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(B) -> U,
    {
        match self {
            Either::Left(a) => Either::Left(a),
            Either::Right(b) => Either::Right(f.apply(b)),
        }
    }
}

impl<K, V, U> MapFst<K, U> for std::collections::HashMap<K, V>
where
    K: Eq + std::hash::Hash,
    U: Eq + std::hash::Hash,
{
    type WrapFst = std::collections::HashMap<U, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(K) -> U,
    {
        self.into_iter().map(|kv| kv.map_fst(f)).collect()
    }
}

impl<K, V, U> MapSnd<V, U> for std::collections::HashMap<K, V>
where
    K: Eq + std::hash::Hash,
{
    type WrapSnd = std::collections::HashMap<K, U>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> U,
    {
        self.into_iter().map(|kv| kv.map_snd(f)).collect()
    }
}

impl<K, U> MapFst<K, U> for std::collections::HashSet<K>
where
    K: Eq + std::hash::Hash,
    U: Eq + std::hash::Hash,
{
    type WrapFst = std::collections::HashSet<U>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(K) -> U,
    {
        self.into_iter().map(|k| f.apply(k)).collect()
    }
}

impl<K, V, U> MapFst<K, U> for Map<K, V>
where
    K: Eq + std::hash::Hash,
    U: Eq + std::hash::Hash,
{
    type WrapFst = Map<U, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(K) -> U,
    {
        self.into_iter().map(|(k, v)| (f.apply(k), v)).collect()
    }
}

impl<K, V, U> MapSnd<V, U> for Map<K, V>
where
    K: Eq + std::hash::Hash,
{
    type WrapSnd = Map<K, U>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> U,
    {
        self.into_iter().map(|(k, v)| (k, f.apply(v))).collect()
    }
}

impl<K, U> MapFst<K, U> for Set<K>
where
    K: Eq + std::hash::Hash,
    U: Eq + std::hash::Hash,
{
    type WrapFst = Set<U>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(K) -> U,
    {
        self.into_iter().map(|k| f.apply(k)).collect()
    }
}

pub type Wrap1<X, A, B> = <X as MapFst<A, B>>::WrapFst;
pub type Wrap2<X, A, B> = <X as MapSnd<A, B>>::WrapSnd;
pub type BiWrap<X, A, B, C, D> = <<X as MapFst<A, B>>::WrapFst as MapSnd<C, D>>::WrapSnd;

pub trait Bifunctor<A, B, C, D>: MapFst<A, B> + MapSnd<C, D>
where
    // <Self as MapFst<A, B>>::WrapFst: MapSnd<C, D>,
    Wrap1<Self, A, B>: MapSnd<C, D>,
{
    fn bimap<F: FnMut(A) -> B, G: FnMut(C) -> D>(
        self,
        f: &mut Func<'_, F>,
        g: &mut Func<'_, G>,
    ) -> BiWrap<Self, A, B, C, D>
    where
        Self: Sized,
    {
        self.map_fst(f).map_snd(g)
    }
}

impl<X, A, B, C, D> Bifunctor<A, B, C, D> for X
where
    X: MapFst<A, B> + MapSnd<C, D>,
    Wrap1<Self, A, B>: MapSnd<C, D>,
{
}

/// A simple trait allowing for reverse composition using method
/// chaining that can be implemented for all types. Note that the
/// by-value method requires the receiver to be `Sized`.
pub trait PipeF {
    #[inline]
    fn pipe<X>(self, f: impl FnOnce(Self) -> X) -> X
    where
        Self: Sized,
    {
        f(self)
    }

    #[inline]
    fn pipe_ref<X>(&self, f: impl FnOnce(&Self) -> X) -> X {
        f(self)
    }

    #[inline]
    fn pipe_mut<X>(&mut self, f: impl FnOnce(&mut Self) -> X) -> X {
        f(self)
    }

    #[inline]
    fn pipe2<X, Y>(self, f: impl FnOnce(Self, X) -> Y + 'static) -> Box<dyn FnOnce(X) -> Y>
    where
        Self: Sized + 'static,
    {
        Box::new(move |x: X| f(self, x))
    }

    #[inline]
    fn flip<'a, X, Y, F>(&'a self, f: F) -> Box<dyn FnOnce(X) -> Y + 'a>
    where
        Self: Sized + 'a,
        F: FnOnce(X, &Self) -> Y + 'a,
    {
        Box::new(move |x: X| f(x, self))
    }

    fn flp<F, X>(&self, f: F) -> F
    where
        for<'a> F: FnOnce(X, &Self),
    {
        f
    }
}

impl<T> PipeF for T {}

pub fn flip<'a, F, X, Y, Z>(f: F) -> Func<'a, impl FnOnce(Y, X) -> Z>
where
    F: 'a + FnOnce(X, Y) -> Z,
{
    Func::New(|y: Y, x: X| f(x, y))
}

pub fn identity<X>(x: X) -> X {
    x
}

pub fn uncurry<'a, G, H, X, Y, Z>(mut g: G) -> Func<'a, impl FnMut(X, Y) -> Z>
where
    G: FnMut(X) -> H,
    H: FnMut(Y) -> Z,
{
    Func::New(move |x: X, y: Y| g(x)(y))
}

impl<X> Default for Func<'_, fn(X) -> X> {
    fn default() -> Self {
        Func::New(identity)
    }
}

pub struct Curry<F>(F);
impl<F> Curry<F> {
    pub fn apply<G, X, Y, Z>(self, x: X) -> G
    where
        F: FnOnce(X) -> G,
        G: FnOnce(Y) -> Z,
    {
        (self.0)(x)
    }

    pub fn apply_mut<G, X, Y, Z>(self, x: X) -> G
    where
        F: FnMut(X) -> G,
        G: FnMut(Y) -> Z,
    {
        let Curry(mut f) = self;
        f(x)
    }

    pub fn uncurry<G, X, Y, Z>(self) -> impl FnOnce(X, Y) -> Z
    where
        F: FnOnce(X) -> G,
        G: FnOnce(Y) -> Z,
    {
        move |x: X, y: Y| self.apply(x)(y)
    }

    pub fn uncurry_mut<G, X, Y, Z>(self) -> impl FnMut(X, Y) -> Z
    where
        F: FnMut(X) -> G,
        G: FnMut(Y) -> Z,
    {
        let Curry(mut f) = self;
        move |x: X, y: Y| f(x)(y)
    }
}

impl<F: Clone> Clone for Curry<F> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<F: Copy> Copy for Curry<F> {}

impl<F> std::ops::Deref for Curry<F> {
    type Target = F;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F> std::ops::DerefMut for Curry<F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<F> AsRef<F> for Curry<F> {
    fn as_ref(&self) -> &F {
        &self.0
    }
}

impl<F> AsMut<F> for Curry<F> {
    fn as_mut(&mut self) -> &mut F {
        &mut self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_func() {
        let f = Func::New(|x| x);
        let y = f(8);
        assert!(y == 8);

        // let f = |x, y| (x, y);
        // let g = flip(f);
        // let g = g(1, 'z');
        // assert_eq!(g, ('z', 1))
    }
}
