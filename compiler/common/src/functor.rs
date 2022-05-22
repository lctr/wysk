pub use std::collections::{HashMap as Map, HashSet as Set, VecDeque as Deque};
use std::hash::Hash;

pub trait Mappable<X> {
    type M<A>: Mappable<A>;
    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y;
}

impl<X> Mappable<X> for Vec<X> {
    type M<Y> = Vec<Y>;
    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        self.into_iter().map(f).collect()
    }
}

impl<X> Mappable<X> for Deque<X> {
    type M<Y> = Deque<Y>;

    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        self.into_iter().map(f).collect()
    }
}

impl<K: Eq + std::hash::Hash, X> Mappable<X> for Map<K, X> {
    type M<A> = Map<K, A>;

    fn fmap<F, Y>(self, mut f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        self.into_iter().map(|(k, x)| (k, f(x))).collect()
    }
}

impl<'x, X> Mappable<&'x X> for &'x [X] {
    type M<A> = Vec<A>;

    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(&'x X) -> Y,
    {
        self.into_iter().map(f).collect()
    }
}

impl<X> Mappable<X> for Option<X> {
    type M<A> = Option<A>;

    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        self.map(f)
    }
}

impl<X, E> Mappable<X> for Result<X, E> {
    type M<A> = Result<A, E>;

    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        self.map(f)
    }
}

impl<X, const N: usize> Mappable<X> for [X; N] {
    type M<A> = [A; N];

    fn fmap<F, Y>(self, f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        let mut array: [Y; N] = unsafe { std::mem::zeroed() };
        for (i, y) in self.into_iter().map(f).enumerate() {
            array[i] = y;
        }
        array
    }
}

impl<X> Mappable<X> for Box<X> {
    type M<A> = Box<A>;

    fn fmap<F, Y>(self, mut f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        Box::new(f(*self))
    }
}

impl<U, V, X> Mappable<X> for (U, V)
where
    U: Mappable<X>,
    V: Mappable<X>,
{
    type M<A> = (U::M<A>, V::M<A>);

    fn fmap<F, Y>(self, mut f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        let (u, v) = self;
        (u.fmap(|x| f(x)), v.fmap(|x| f(x)))
    }
}

impl<X> Mappable<X> for (X,) {
    type M<A> = (A,);

    fn fmap<F, Y>(self, mut f: F) -> Self::M<Y>
    where
        F: FnMut(X) -> Y,
    {
        let (x,) = self;
        (f(x),)
    }
}

pub fn map_vec<X, Y>(vec: Vec<X>, f: impl FnMut(X) -> Y) -> Vec<Y> {
    vec.fmap(f)
}

pub fn map_deque<X, Y>(deque: Deque<X>, f: impl FnMut(X) -> Y) -> Deque<Y> {
    deque.fmap(f)
}

pub fn map_set<X, Y>(set: Set<X>, f: impl FnMut(X) -> Y) -> Set<Y>
where
    X: Eq + Hash,
    Y: Eq + Hash,
{
    set.into_iter().map(f).collect()
}

pub fn map_iterator<Y, I: IntoIterator, J>(iter: I, f: impl FnMut(I::Item) -> Y) -> J
where
    J: FromIterator<Y>,
{
    iter.into_iter().map(f).collect()
}

// class Bifunctor p where
//   bimap :: (a -> b) -> (c -> d) -> p a c -> p b d
//   first :: (a -> b) -> p a c -> p b c
//   second :: (b -> c) -> p a b -> p a c
pub trait Bifunctor<X, Y>
where
    Self: Sized,
{
    type Bi<U, V>: Bifunctor<U, V>;
    fn map_fst<A>(self, f: impl FnMut(X) -> A) -> Self::Bi<A, Y>;
    fn map_snd<B>(self, f: impl FnMut(Y) -> B) -> Self::Bi<X, B>;
    fn bimap<A, B>(self, f: impl FnMut(X) -> A, g: impl FnMut(Y) -> B) -> Self::Bi<A, B>;
    fn chain_ltr<A, B>(
        self,
        fst: impl FnMut(X) -> A,
        snd: impl FnMut(Y) -> B,
    ) -> <<Self as Bifunctor<X, Y>>::Bi<A, Y> as Bifunctor<A, Y>>::Bi<A, B> {
        /*
             expected associated type `<Self as Bifunctor<X, Y>>::Bi<A, B>`
        found associated type `<<Self as Bifunctor<X, Y>>::Bi<A, Y> as Bifunctor<A, Y>>::Bi<A, B>`

             */
        self.map_fst(fst).map_snd(snd)
    }
    fn chain_rtl<A, B>(
        self,
        fst: impl FnMut(X) -> A,
        snd: impl FnMut(Y) -> B,
    ) -> <<Self as Bifunctor<X, Y>>::Bi<X, B> as Bifunctor<X, B>>::Bi<A, B> {
        self.map_snd(snd).map_fst(fst)
    }
}

impl<X, Y> Bifunctor<X, Y> for (X, Y) {
    type Bi<U, V> = (U, V);

    fn map_fst<A>(self, mut f: impl FnMut(X) -> A) -> Self::Bi<A, Y> {
        let (x, y) = self;
        (f(x), y)
    }

    fn map_snd<B>(self, mut f: impl FnMut(Y) -> B) -> Self::Bi<X, B> {
        let (x, y) = self;
        (x, f(y))
    }

    fn bimap<A, B>(
        self,
        mut fst: impl FnMut(X) -> A,
        mut snd: impl FnMut(Y) -> B,
    ) -> Self::Bi<A, B> {
        let (x, y) = self;
        (fst(x), snd(y))
    }
}

impl<X, Y> Bifunctor<X, Y> for Result<X, Y> {
    type Bi<U, V> = Result<U, V>;

    fn map_fst<A>(self, f: impl FnMut(X) -> A) -> Self::Bi<A, Y> {
        self.map(f)
    }

    fn map_snd<B>(self, f: impl FnMut(Y) -> B) -> Self::Bi<X, B> {
        self.map_err(f)
    }

    fn bimap<A, B>(self, fst: impl FnMut(X) -> A, snd: impl FnMut(Y) -> B) -> Self::Bi<A, B> {
        self.map(fst).map_err(snd)
    }
}

impl<X, Y, Z> Bifunctor<X, Y> for Vec<Z>
where
    Z: Bifunctor<X, Y>,
{
    type Bi<U, V> = Vec<Z::Bi<U, V>>;

    fn map_fst<A>(self, mut f: impl FnMut(X) -> A) -> Self::Bi<A, Y> {
        self.into_iter()
            .map(|z| z.map_fst(|x| f(x)))
            .collect::<Vec<_>>()
    }

    fn map_snd<B>(self, mut f: impl FnMut(Y) -> B) -> Self::Bi<X, B> {
        self.into_iter()
            .map(|z| z.map_snd(|y| f(y)))
            .collect::<Vec<_>>()
    }

    fn bimap<A, B>(self, mut f: impl FnMut(X) -> A, mut g: impl FnMut(Y) -> B) -> Self::Bi<A, B> {
        self.into_iter()
            .map(|z| z.bimap(|x| f(x), |y| g(y)))
            .collect()
    }
}

impl<X, Y, Z> Bifunctor<X, Y> for Deque<Z>
where
    Z: Bifunctor<X, Y>,
{
    type Bi<U, V> = Deque<Z::Bi<U, V>>;

    fn map_fst<A>(self, mut f: impl FnMut(X) -> A) -> Self::Bi<A, Y> {
        self.into_iter()
            .map(|z| z.map_fst(|x| f(x)))
            .collect::<Deque<_>>()
    }

    fn map_snd<B>(self, mut f: impl FnMut(Y) -> B) -> Self::Bi<X, B> {
        self.into_iter()
            .map(|z| z.map_snd(|y| f(y)))
            .collect::<Deque<_>>()
    }

    fn bimap<A, B>(self, mut f: impl FnMut(X) -> A, mut g: impl FnMut(Y) -> B) -> Self::Bi<A, B> {
        self.into_iter()
            .map(|z| z.bimap(|x| f(x), |y| g(y)))
            .collect::<Deque<_>>()
    }
}

pub struct Fmap<X, F> {
    item: X,
    f: F,
}

impl<X, F, T> Fmap<X, F>
where
    F: FnMut(X) -> T,
{
    pub fn new(item: X, f: F) -> Self {
        Fmap { item, f }
    }

    pub fn apply(mut self) -> T {
        (self.f)(self.item)
    }

    pub fn clone_item(&self) -> X
    where
        X: Clone,
    {
        self.item.clone()
    }

    pub fn repeat(self, n: usize) -> Vec<T>
    where
        X: Clone,
    {
        let Fmap { item, mut f } = self;
        (0..n).map(|_| f(item.clone())).collect()
    }

    pub fn map<S>(self, mut g: impl FnMut(T) -> S) -> Fmap<X, impl FnMut(X) -> S> {
        let Fmap { item, mut f } = self;
        Fmap {
            item,
            f: move |x: X| g(f(x)),
        }
    }

    pub fn then<S>(self, g: impl FnMut(T) -> S) -> Fmap<T, impl FnMut(T) -> S> {
        Fmap {
            item: self.apply(),
            f: g,
        }
    }
    pub fn iterate(self, mut g: impl FnMut(&X) -> Option<X>) -> Fmap<X, F> {
        let Fmap { item, f } = self;
        let mut item = item;
        while let Some(x) = g(&item) {
            item = x;
        }
        Fmap { item, f }
    }
}

pub trait Transform {
    type Domain;
    type Codomain;
    fn apply(self) -> Self::Codomain;
    fn then<G, S>(self, g: G) -> Fmap<Self::Codomain, G>
    where
        Self: Sized,
        G: FnMut(Self::Codomain) -> S,
    {
        Fmap {
            item: self.apply(),
            f: g,
        }
    }
}

impl<X, F, T> Transform for Fmap<X, F>
where
    F: FnMut(X) -> T,
{
    type Domain = X;
    type Codomain = T;

    fn apply(self) -> Self::Codomain {
        Fmap::apply(self)
    }
}

pub type Transformation<X, Y> = Box<dyn Transform<Domain = X, Codomain = Y>>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_map() {
        let times_2 = Fmap::new(1, |n| n * 2);
        let times_10 = times_2.map(|g| g * 10);
        let res = times_10.apply();
        assert_eq!(res, 20);
        let counter = Fmap::new(0, |n| n);
        let mut state = 0;
        let iterated = counter.iterate(|n| {
            if *n < 10 {
                state += 30;
                Some(n + 1)
            } else {
                None
            }
        });
        let ten = iterated.apply();
        assert_eq!(ten, 10);
        assert_eq!(state, 300);
    }
}
