use crate::{
    ranges::{Position, Region, Span},
    BytePos, Col, Row,
};

#[derive(Clone, Copy)]
pub struct Spanned<T>(pub T, pub Span);

impl<T> Spanned<T> {
    pub fn new(item: T, span: Span) -> Self {
        Self(item, span)
    }

    #[inline]
    pub fn take_item(self) -> T {
        self.0
    }

    #[inline]
    pub fn item(&self) -> &T {
        &self.0
    }

    #[inline]
    pub fn span(&self) -> Span {
        self.1
    }

    pub fn span_mut(&mut self) -> &mut Span {
        &mut self.1
    }

    #[inline]
    pub fn start(&self) -> BytePos {
        self.1.start()
    }

    #[inline]
    pub fn end(&self) -> BytePos {
        self.1.end()
    }

    pub fn shift_right(&mut self, offset: BytePos) {
        if offset.is_dummy() {
            panic!(
                "tried to shift spanned item span `{}` right by dummy bytepos offset `{offset}`",
                self.span()
            )
        }
        *self.span_mut() += offset;
    }

    pub fn mapf<F, U>(self, f: &mut wy_common::functor::Func<F>) -> Spanned<U>
    where
        F: FnMut(T) -> U,
    {
        Spanned(f.apply(self.0), self.1)
    }

    #[inline]
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> Spanned<U> {
        Spanned(f(self.0), self.1)
    }

    /// Given a span, returns a new span containing the minimum `Pos` as the
    /// starting point and the maximum `Pos` as the ending point.
    pub fn union(&self, other: &Span) -> Spanned<&T> {
        let Spanned(t, Span(a1, a2)) = self;
        let Span(b1, b2) = other;
        let mut ss = [a1, a2, b1, b2];
        ss.sort();
        let [start, _, _, end] = ss;
        Spanned(t, Span(*start, *end))
    }

    pub fn item_eq(&self, other: &Self) -> bool
    where
        T: PartialEq,
    {
        self.item() == other.item()
    }

    pub fn span_eq(&self, other: &Self) -> bool {
        self.span() == other.span()
    }

    pub fn total_eq(&self, other: &Self) -> bool
    where
        T: PartialEq,
    {
        self.item_eq(other) && self.span_eq(other)
    }
}

impl<T> Spanned<&T> {
    pub fn clone_item(self) -> Spanned<T>
    where
        T: Clone,
    {
        let Spanned(t, span) = self;
        Spanned(t.clone(), span)
    }

    pub fn copy_item(self) -> Spanned<T>
    where
        T: Copy,
    {
        let Spanned(t, span) = self;
        Spanned(*t, span)
    }
}

impl<X> Spanned<Option<X>> {
    pub fn transpose(self) -> Option<Spanned<X>> {
        let Spanned(x, span) = self;
        x.map(|x2| Spanned(x2, span))
    }

    pub fn transpose_ref(&self) -> Option<Spanned<&X>> {
        let Spanned(x, span) = self;
        x.as_ref().map(|x2| Spanned(x2, *span))
    }
}

impl<X> From<Spanned<Option<X>>> for Option<Spanned<X>> {
    fn from(sp: Spanned<Option<X>>) -> Self {
        sp.transpose()
    }
}

impl<T, E> Spanned<Result<T, E>> {
    pub fn as_result(self) -> Result<Spanned<T>, E> {
        match self {
            Spanned(Ok(t), span) => Ok(Spanned(t, span)),
            Spanned(Err(e), _span) => Err(e),
        }
    }
    pub fn ok(self) -> Result<Spanned<T>, Spanned<E>> {
        match self {
            Spanned(Ok(t), span) => Ok(Spanned(t, span)),
            Spanned(Err(e), span) => Err(Spanned(e, span)),
        }
    }
    pub fn ok_or<A>(self, mut f: impl FnMut(E, Span) -> A) -> Result<Spanned<T>, A> {
        let Spanned(result, span) = self;
        match result {
            Ok(res) => Ok(Spanned(res, span)),
            Err(e) => Err(f(e, span)),
        }
    }
    pub fn flat_map<U>(self, mut f: impl FnMut(T) -> Result<U, E>) -> Result<Spanned<U>, E> {
        self.0.and_then(|t| f(t).map(|u| Spanned(u, self.1)))
    }
}

impl<T, E> TryFrom<Spanned<Result<T, E>>> for Spanned<T> {
    type Error = Spanned<E>;

    fn try_from(value: Spanned<Result<T, E>>) -> Result<Self, Self::Error> {
        value.ok()
    }
}

impl<T> Eq for Spanned<T> where T: Eq {}

impl<T> std::cmp::PartialEq for Spanned<T>
where
    T: PartialEq,
{
    /// Only the item data is compared; to compare spans, either
    /// `span_eq` or `total_eq` must be used.
    fn eq(&self, other: &Self) -> bool {
        self.item() == other.item()
    }
}

impl<T> PartialEq<T> for Spanned<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &T) -> bool {
        self.item() == other
    }
}

impl<T> std::cmp::PartialOrd for Spanned<T>
where
    T: PartialEq,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.span().partial_cmp(&other.span())
    }
}

impl<T> PartialOrd<T> for Spanned<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &T) -> Option<std::cmp::Ordering> {
        self.item().partial_cmp(other)
    }
}

impl<T> std::hash::Hash for Spanned<T>
where
    T: std::hash::Hash,
{
    /// Note: only the carried items are hashed, spans themselves are ignored
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        // self.1.hash(state);
    }
}

impl<T> std::fmt::Debug for Spanned<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} @ {}:{}", self.item(), self.start(), self.end())
    }
}

impl<T> std::fmt::Display for Spanned<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} @ {}:{}", self.item(), self.start(), self.end())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Located<T>(pub T, pub Region);

impl<T> std::fmt::Display for Located<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Located({}, {} - {})",
            &self.0,
            self.location().start,
            self.location().end
        )
    }
}

impl<T> Located<T> {
    pub fn new(item: T, location: Region) -> Self {
        Self(item, location)
    }

    #[inline]
    pub fn as_tuple(self) -> (T, Region) {
        (self.0, self.1)
    }
    #[inline]
    pub fn take_item(self) -> T {
        self.0
    }

    #[inline]
    pub fn item(&self) -> &T {
        &self.0
    }

    pub fn item_mut(&mut self) -> &mut T {
        &mut self.0
    }

    #[inline]
    pub fn location(&self) -> Region {
        self.1
    }

    pub fn mapf<F, U>(self, f: &mut wy_common::functor::Func<F>) -> Located<U>
    where
        F: FnMut(T) -> U,
    {
        Located(f.apply(self.0), self.1)
    }

    #[inline]
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> Located<U> {
        Located(f(self.0), self.1)
    }

    #[inline]
    pub fn map_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Located<U> {
        Located(f(&self.0), self.1)
    }

    pub fn union(self, other: Region) -> Self {
        let Located(t, location) = self;
        Located(t, location.union(&other))
    }

    #[inline]
    pub fn replace_item(&mut self, new_item: T) -> T {
        std::mem::replace(&mut self.0, new_item)
    }

    pub fn join_vec(self, other: Self) -> Located<Vec<T>> {
        let (item_1, loc_1) = self.as_tuple();
        let (item_2, loc_2) = other.as_tuple();
        Located(vec![item_1, item_2], loc_1.union(&loc_2))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Positioned<X>(pub X, pub Position);

impl<X> Copy for Positioned<X> where X: Copy {}

impl<X> Positioned<X> {
    pub fn new(item: X, position: Position) -> Self {
        Positioned(item, position)
    }
    pub fn parts(self) -> (X, Position) {
        (self.0, self.1)
    }
    pub fn position(&self) -> Position {
        self.1
    }
    pub fn take_item(self) -> X {
        self.0
    }
    pub fn item(&self) -> &X {
        &self.0
    }
    pub fn item_mut(&mut self) -> &mut X {
        &mut self.0
    }
    pub fn replace_item(&mut self, new_item: X) -> X {
        std::mem::replace(&mut self.0, new_item)
    }
    pub fn span(&self) -> Span {
        self.1.span
    }
    pub fn location(&self) -> Region {
        self.1.region
    }
    pub fn byte_start(&self) -> BytePos {
        self.1.span.0
    }
    pub fn byte_end(&self) -> BytePos {
        self.1.span.1
    }
    pub fn byte_diff(&self) -> usize {
        self.1.byte_diff()
    }
    pub fn row_diff(&self) -> usize {
        self.1.row_diff()
    }
    pub fn col_diff(&self) -> usize {
        self.1.col_diff()
    }
    pub fn byte_range(&self) -> std::ops::Range<BytePos> {
        self.span().byte_range()
    }
    pub fn row_range(&self) -> std::ops::Range<Row> {
        self.location().row_range()
    }
    pub fn col_range(&self) -> std::ops::Range<Col> {
        self.location().col_range()
    }
    pub fn is_empty(&self) -> bool {
        self.1.is_empty()
    }
    /// Note: this takes the union of the *positions* and doesn't touch the
    /// inner item contained.
    pub fn union(&self, other: &Positioned<X>) -> Position {
        self.1.union(&other.1)
    }

    pub fn mapf<F, U>(self, f: &mut wy_common::functor::Func<F>) -> Positioned<U>
    where
        F: FnMut(X) -> U,
    {
        Positioned(f.apply(self.0), self.1)
    }
}

impl<X, E> Positioned<Result<X, E>> {
    pub fn as_result(self) -> Result<Positioned<X>, E> {
        self.0.map(|x| Positioned(x, self.1))
    }
    pub fn ok(self) -> Result<Positioned<X>, Positioned<E>> {
        self.0
            .map(|x| Positioned(x, self.1))
            .map_err(|e| Positioned(e, self.1))
    }
    pub fn ok_or<A>(self, mut f: impl FnMut(E, Position) -> A) -> Result<Positioned<X>, A> {
        self.0
            .map(|x| Positioned(x, self.1))
            .map_err(|e| f(e, self.1))
    }
    pub fn flat_map<Y>(self, mut f: impl FnMut(X) -> Result<Y, E>) -> Result<Positioned<Y>, E> {
        self.0.and_then(|x| f(x).map(|y| Positioned(y, self.1)))
    }
    pub fn map_err<A>(self, f: impl FnMut(E) -> A) -> Result<Positioned<X>, A> {
        self.0.map(|x| Positioned(x, self.1)).map_err(f)
    }
    pub fn is_ok(&self) -> bool {
        self.0.is_ok()
    }
    pub fn is_err(&self) -> bool {
        self.0.is_err()
    }
    pub fn contains_item(&self, item: &X) -> bool
    where
        X: PartialEq,
    {
        matches!(self.0.as_ref(), Ok(x) if x == item)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_shift_span_by_bytepos() {
        let span0 = Span(BytePos::new(0), BytePos::new(15));
        let offset = BytePos::new(4);
        let mut spanned0 = Spanned("foo", span0);

        spanned0.shift_right(offset);
        assert_eq!(
            spanned0,
            Spanned("foo", Span(BytePos::new(4), BytePos::new(19)))
        )
    }
}
