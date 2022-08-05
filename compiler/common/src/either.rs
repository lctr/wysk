use crate::variant_preds;

pub enum Either<L, R> {
    Left(L),
    Right(R),
}

variant_preds! {
    |L, R| Either[L, R]
    | is_left => Left(_)
    | is_right => Right(_)
}

impl<L, R> Either<L, R> {
    pub fn map_left<X>(self, mut f: impl FnMut(L) -> X) -> Either<X, R> {
        match self {
            Either::Left(l) => Either::Left(f(l)),
            Either::Right(r) => Either::Right(r),
        }
    }

    pub fn map_left_ref<X>(&self, mut f: impl FnMut(&L) -> X) -> Either<X, &R> {
        match self {
            Either::Left(l) => Either::Left(f(l)),
            Either::Right(r) => Either::Right(r),
        }
    }

    pub fn map_right<Y>(self, mut f: impl FnMut(R) -> Y) -> Either<L, Y> {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f(r)),
        }
    }

    pub fn map_right_ref<Y>(&self, mut f: impl FnMut(&R) -> Y) -> Either<&L, Y> {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f(r)),
        }
    }

    pub fn map<A, B>(self, mut f: impl FnMut(L) -> A, mut g: impl FnMut(R) -> B) -> Either<A, B> {
        match self {
            Either::Left(l) => Either::Left(f(l)),
            Either::Right(r) => Either::Right(g(r)),
        }
    }

    pub fn as_left(self) -> Option<L> {
        match self {
            Either::Left(l) => Some(l),
            Either::Right(_) => None,
        }
    }

    pub fn as_right(self) -> Option<R> {
        match self {
            Either::Left(_) => None,
            Either::Right(r) => Some(r),
        }
    }

    pub fn test_left(&self, mut f: impl FnMut(&L) -> bool) -> bool {
        match self {
            Either::Left(l) => f(l),
            Either::Right(_) => false,
        }
    }

    pub fn test_right(&self, mut f: impl FnMut(&R) -> bool) -> bool {
        match self {
            Either::Left(_) => false,
            Either::Right(r) => f(r),
        }
    }

    pub fn get_left(&self) -> Option<&L> {
        match self {
            Either::Left(l) => Some(l),
            Either::Right(_) => None,
        }
    }

    pub fn get_left_mut(&mut self) -> Option<&mut L> {
        match self {
            Either::Left(l) => Some(l),
            Either::Right(_) => None,
        }
    }

    pub fn get_right(&self) -> Option<&R> {
        match self {
            Either::Left(_) => None,
            Either::Right(r) => Some(r),
        }
    }

    pub fn get_right_mut(&mut self) -> Option<&mut R> {
        match self {
            Either::Left(_) => None,
            Either::Right(r) => Some(r),
        }
    }

    pub fn as_result(self) -> Result<L, R> {
        match self {
            Either::Left(l) => Ok(l),
            Either::Right(r) => Err(r),
        }
    }

    pub fn transpose(self) -> Either<R, L> {
        match self {
            Either::Left(l) => Either::Right(l),
            Either::Right(r) => Either::Left(r),
        }
    }

    pub fn as_ref(&self) -> Either<&L, &R> {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(r),
        }
    }

    pub fn left_cloned(&self) -> Either<L, &R>
    where
        L: Clone,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => Either::Right(r),
        }
    }

    pub fn right_cloned(&self) -> Either<&L, R>
    where
        R: Clone,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(r.clone()),
        }
    }

    pub fn left_copied(&self) -> Either<L, &R>
    where
        L: Copy,
    {
        match self {
            Either::Left(l) => Either::Left(*l),
            Either::Right(r) => Either::Right(r),
        }
    }

    pub fn right_copied(&self) -> Either<&L, R>
    where
        R: Copy,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(*r),
        }
    }

    pub fn copied(&self) -> Either<L, R>
    where
        L: Copy,
        R: Copy,
    {
        match self {
            Either::Left(l) => Either::Left(*l),
            Either::Right(r) => Either::Right(*r),
        }
    }

    pub fn join<X>(self, mut f: impl FnMut(L) -> X, mut g: impl FnMut(R) -> X) -> X {
        match self {
            Either::Left(l) => f(l),
            Either::Right(r) => g(r),
        }
    }
}

impl<L, R> std::fmt::Debug for Either<L, R>
where
    L: std::fmt::Debug,
    R: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Left(arg0) => f.debug_tuple("Left").field(arg0).finish(),
            Self::Right(arg0) => f.debug_tuple("Right").field(arg0).finish(),
        }
    }
}

impl<L, R> std::fmt::Display for Either<L, R>
where
    L: std::fmt::Display,
    R: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Either::Left(l) => L::fmt(l, f),
            Either::Right(r) => R::fmt(r, f),
        }
    }
}

impl<L, R> Clone for Either<L, R>
where
    L: Clone,
    R: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::Left(arg0) => Self::Left(arg0.clone()),
            Self::Right(arg0) => Self::Right(arg0.clone()),
        }
    }
}

impl<L, R> Copy for Either<L, R>
where
    L: Copy,
    R: Copy,
{
}

impl<L, R> PartialEq for Either<L, R>
where
    L: PartialEq,
    R: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Left(l0), Self::Left(r0)) => l0 == r0,
            (Self::Right(l0), Self::Right(r0)) => l0 == r0,
            _ => false,
        }
    }
}

impl<L, R> Eq for Either<L, R>
where
    L: Eq,
    R: Eq,
{
}

impl<L, R> PartialOrd for Either<L, R>
where
    L: PartialOrd,
    R: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Either::Left(l1), Either::Left(l2)) => l1.partial_cmp(l2),
            (Either::Right(r1), Either::Right(r2)) => r1.partial_cmp(r2),
            _ => None,
        }
    }
}

impl<L, R> std::hash::Hash for Either<L, R>
where
    L: std::hash::Hash,
    R: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Either::Left(l) => l.hash(state),
            Either::Right(r) => r.hash(state),
        }
    }
}

// Should be safe since it depends on both `L` and `R` being `Send`
unsafe impl<L, R> Send for Either<L, R>
where
    L: Send,
    R: Send,
{
}

// Should be safe since it depends on both `L` and `R` being `Sync`
unsafe impl<L, R> Sync for Either<L, R>
where
    L: Sync,
    R: Sync,
{
}

impl<L, R> From<Either<L, R>> for Result<L, R> {
    fn from(it: Either<L, R>) -> Self {
        it.as_result()
    }
}

impl<L, R> From<Result<L, R>> for Either<L, R> {
    fn from(res: Result<L, R>) -> Self {
        match res {
            Ok(l) => Self::Left(l),
            Err(r) => Self::Right(r),
        }
    }
}

impl<L> From<Option<L>> for Either<L, ()> {
    fn from(maybe: Option<L>) -> Self {
        if let Some(l) = maybe {
            Self::Left(l)
        } else {
            Self::Right(())
        }
    }
}

impl<L> From<Either<L, ()>> for Option<L> {
    fn from(ei: Either<L, ()>) -> Self {
        match ei {
            Either::Left(l) => Some(l),
            Either::Right(_) => None,
        }
    }
}

impl<L, R> From<Either<Either<L, R>, Either<L, R>>> for Either<L, R> {
    fn from(either: Either<Either<L, R>, Either<L, R>>) -> Self {
        match either {
            Either::Left(ei) | Either::Right(ei) => match ei {
                Either::Left(l) => Self::Left(l),
                Either::Right(r) => Self::Right(r),
            },
        }
    }
}

impl<L, R> From<Either<L, Either<L, R>>> for Either<L, R> {
    fn from(either: Either<L, Either<L, R>>) -> Self {
        match either {
            Either::Left(l) | Either::Right(Either::Left(l)) => Self::Left(l),
            Either::Right(Either::Right(r)) => Self::Right(r),
        }
    }
}

impl<X> From<Either<X, Vec<X>>> for Vec<X> {
    fn from(ei: Either<X, Vec<X>>) -> Self {
        match ei {
            Either::Left(x) => vec![x],
            Either::Right(xs) => xs,
        }
    }
}
