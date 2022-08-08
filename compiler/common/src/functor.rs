pub use std::collections::{HashMap as Map, HashSet as Set, VecDeque as Deque};

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
    Fresh(F),
    Cont(&'a mut Func<'a, F>),
}

impl<'a, F> Func<'a, F> {
    pub fn apply<A, B>(&mut self, arg: A) -> B
    where
        F: FnMut(A) -> B,
    {
        match self {
            Func::Fresh(f) => f(arg),
            Func::Cont(f) => f.apply(arg),
        }
    }
}

pub trait Functor<A, B> {
    type Wrapper: Functor<B, A>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(A) -> B;
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

// maybe delete later lol
// pub trait Mappable<X> {
//     type M<A>: Mappable<A>;
//     fn fmap<F, Y>(self, f: F) -> Self::M<Y>
//     where
//         F: FnMut(X) -> Y;
// }

// impl<X> Mappable<X> for Vec<X> {
//     type M<Y> = Vec<Y>;
//     fn fmap<F, Y>(self, f: F) -> Self::M<Y>
//     where
//         F: FnMut(X) -> Y,
//     {
//         self.into_iter().map(f).collect()
//     }
// }

// impl<X> Mappable<X> for Deque<X> {
//     type M<Y> = Deque<Y>;

//     fn fmap<F, Y>(self, f: F) -> Self::M<Y>
//     where
//         F: FnMut(X) -> Y,
//     {
//         self.into_iter().map(f).collect()
//     }
// }

// impl<K: Eq + std::hash::Hash, X> Mappable<X> for Map<K, X> {
//     type M<A> = Map<K, A>;

//     fn fmap<F, Y>(self, mut f: F) -> Self::M<Y>
//     where
//         F: FnMut(X) -> Y,
//     {
//         self.into_iter().map(|(k, x)| (k, f(x))).collect()
//     }
// }

// impl<'x, X> Mappable<&'x X> for &'x [X] {
//     type M<A> = Vec<A>;

//     fn fmap<F, Y>(self, f: F) -> Self::M<Y>
//     where
//         F: FnMut(&'x X) -> Y,
//     {
//         self.into_iter().map(f).collect()
//     }
// }

// impl<X> Mappable<X> for Option<X> {
//     type M<A> = Option<A>;

//     fn fmap<F, Y>(self, f: F) -> Self::M<Y>
//     where
//         F: FnMut(X) -> Y,
//     {
//         self.map(f)
//     }
// }

// impl<X, E> Mappable<X> for Result<X, E> {
//     type M<A> = Result<A, E>;

//     fn fmap<F, Y>(self, f: F) -> Self::M<Y>
//     where
//         F: FnMut(X) -> Y,
//     {
//         self.map(f)
//     }
// }

// impl<X, const N: usize> Mappable<X> for [X; N] {
//     type M<A> = [A; N];

//     fn fmap<F, Y>(self, f: F) -> Self::M<Y>
//     where
//         F: FnMut(X) -> Y,
//     {
//         let mut array: [Y; N] = unsafe { std::mem::zeroed() };
//         for (i, y) in self.into_iter().map(f).enumerate() {
//             array[i] = y;
//         }
//         array
//     }
// }

// impl<X> Mappable<X> for Box<X> {
//     type M<A> = Box<A>;

//     fn fmap<F, Y>(self, mut f: F) -> Self::M<Y>
//     where
//         F: FnMut(X) -> Y,
//     {
//         Box::new(f(*self))
//     }
// }

// impl<U, V, X> Mappable<X> for (U, V)
// where
//     U: Mappable<X>,
//     V: Mappable<X>,
// {
//     type M<A> = (U::M<A>, V::M<A>);

//     fn fmap<F, Y>(self, mut f: F) -> Self::M<Y>
//     where
//         F: FnMut(X) -> Y,
//     {
//         let (u, v) = self;
//         (u.fmap(|x| f(x)), v.fmap(|x| f(x)))
//     }
// }

// impl<X> Mappable<X> for () {
//     type M<A> = ();

//     fn fmap<F, Y>(self, _f: F) -> Self::M<Y>
//     where
//         F: FnMut(X) -> Y,
//     {
//         ()
//     }
// }

// impl<X> Mappable<X> for (X,) {
//     type M<A> = (A,);

//     fn fmap<F, Y>(self, mut f: F) -> Self::M<Y>
//     where
//         F: FnMut(X) -> Y,
//     {
//         let (x,) = self;
//         (f(x),)
//     }
// }

#[cfg(test)]
mod tests {}
