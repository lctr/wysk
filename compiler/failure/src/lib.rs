pub type Outcome<X, E> = Result<X, Failure<E>>;

#[derive(Debug)]
pub enum Failure<E> {
    Io(std::io::Error),
    Err(E),
}

pub fn normalize_io_err<E>(error: Failure<std::io::Error>) -> Failure<E> {
    match error {
        Failure::Io(e) | Failure::Err(e) => Failure::Io(e),
    }
}

pub struct It<X>(pub(crate) X);
impl<X> From<X> for It<X> {
    fn from(x: X) -> Self {
        Self(x)
    }
}

impl<X> AsRef<X> for It<X> {
    fn as_ref(&self) -> &X {
        &self.0
    }
}

impl<X> std::ops::Deref for It<X> {
    type Target = X;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<X> std::ops::DerefMut for It<X> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<X: Copy> Copy for It<X> {}

impl<X: Clone> Clone for It<X> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<X: PartialEq> PartialEq for It<X> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<X: Eq> Eq for It<X> {}

impl<X: std::hash::Hash> std::hash::Hash for It<X> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<X: Default> Default for It<X> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<X: std::fmt::Debug> std::fmt::Debug for It<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        X::fmt(&self.0, f)
    }
}

impl<X: std::fmt::Display> std::fmt::Display for It<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        X::fmt(&self.0, f)
    }
}

impl<E> std::fmt::Display for Failure<E>
where
    E: std::error::Error,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Failure::Io(err) => write!(f, "IO error: {}", err),
            Failure::Err(e) => write!(f, "{}", e),
        }
    }
}

impl<E> From<std::io::Error> for Failure<E> {
    fn from(ioerr: std::io::Error) -> Self {
        Failure::Io(ioerr)
    }
}

impl<E> From<Failure<Failure<E>>> for Failure<E> {
    fn from(e: Failure<Failure<E>>) -> Self {
        match e {
            Failure::Io(e) => Failure::Io(e),
            Failure::Err(e) => e,
        }
    }
}

impl<E> std::error::Error for Failure<E> where E: std::error::Error {}

#[macro_export]
macro_rules! fails {
    (impl for $ty:ty $(| $val:ty)?) => {
        impl From<$ty> for $crate::Failure<$ty $(, $val)?> {
            fn from(it: $ty) -> Self {
                $crate::Failure::Err(it)
            }
        }
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
