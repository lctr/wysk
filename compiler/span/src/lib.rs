use wy_common::newtype;

newtype! {
    { u32 in Row | Show Usize Deref (+=) (-) }
    { u32 in Col | Show Usize Deref (+=) (-) }
    { u32 in Pos | Show Usize Deref (+=) (-)
        (+= char |rhs| rhs.len_utf8() as u32)
    }
}

impl<'t> std::ops::Index<Row> for std::str::Lines<'t> {
    type Output = str;

    fn index(&self, index: Row) -> &Self::Output {
        let row = index.as_usize();
        for (r, s) in self.clone().enumerate() {
            if r == row {
                return s;
            }
        }
        ""
    }
}

pub trait Dummy
where
    Self: Sized + PartialEq,
{
    const DUMMY: Self;
    fn dummy() -> Self {
        Self::DUMMY
    }
    fn is_dummy(&self) -> bool {
        self == &Self::DUMMY
    }
    fn partial_dummy(&self) -> bool;
}

pub trait WithSpan {
    fn get_pos(&self) -> Pos;

    fn as_index(&self) -> usize {
        self.get_pos().as_usize()
    }

    fn spanned<F, X>(&mut self, mut f: F) -> Spanned<X>
    where
        F: FnMut(&mut Self) -> X,
    {
        let start = self.get_pos();
        let ret = f(self);
        let end = self.get_pos();
        Spanned(ret, Span(start, end))
    }
}

pub trait WithLoc {
    fn get_loc(&self) -> Loc;
    fn get_row(&self) -> Row {
        WithLoc::get_loc(self).row
    }
    fn get_col(&self) -> Col {
        WithLoc::get_loc(self).col
    }
    fn with_loc<F, X>(&mut self, mut f: F) -> Located<X>
    where
        F: FnMut(&mut Self) -> X,
    {
        let start = WithLoc::get_loc(self);
        let x = f(self);
        let end = WithLoc::get_loc(self);
        Located(x, Location { start, end })
    }
}

impl Dummy for Row {
    const DUMMY: Self = Self::ZERO;

    fn partial_dummy(&self) -> bool {
        self.is_zero()
    }
}

impl Dummy for Col {
    const DUMMY: Self = Self::MAX;

    fn partial_dummy(&self) -> bool {
        self.is_dummy()
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span(pub Pos, pub Pos);

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.0, self.1)
    }
}

impl Span {
    pub fn new(start: impl Into<Pos>, end: impl Into<Pos>) -> Self {
        Self(start.into(), end.into())
    }

    pub fn tuple(self) -> (Pos, Pos) {
        (self.0, self.1)
    }

    pub fn len(&self) -> usize {
        (self.1 - self.0).as_usize()
    }

    pub fn start(&self) -> Pos {
        self.0
    }

    pub fn end(&self) -> Pos {
        self.1
    }

    pub fn begin<X: WithSpan>(start: Pos) -> impl FnMut(X) -> Span {
        move |x: X| Span(start, x.get_pos())
    }

    /// Returns a `Span` as a `Range<usize>`; used to index string slices using
    /// the byte positions within a span. Namely, a span `Span(a, b)` must be
    /// converted into a range `a'..b'` (where `a'` and `b'` are the `usize`
    /// values corresponding to the byte positions held by `a` and `b`,
    /// respectively) in order to index a subslice from an `&str`.
    pub fn range(&self) -> std::ops::Range<usize> {
        (self.start().as_usize())..(self.end().as_usize())
    }

    pub fn union(&self, other: Span) -> Self {
        let mut poss = [self.0, self.1, other.0, other.1];
        poss.sort_unstable();
        Span(poss[0], poss[3])
    }

    /// Given a `Span` and some character `c`, returns a new `Span` with the
    /// same starting point and a new endpoint resulting from subtracting the
    /// UTF8 length of `c` from the `Span`s end. If the `Span` does not range
    /// over enough bytes (e.g., the resulting span would have the same start
    /// and end), the same `Span` is returned unchanged.
    ///
    /// This should generally be avoided except in the case of cleaning up
    /// source code comments with trailing/unnecessary boundary character(s).
    pub fn shrink_right(self, c: char) -> Self {
        let Span(start @ Pos(a), Pos(b)) = self;
        let len = c.len_utf8() as u32;
        if a.abs_diff(b) > len
        /* && b > len */
        {
            let diff = b - len;
            if a < diff {
                return Span(start, Pos(diff));
            }
        }
        self
    }

    /// Analogous to the `Span::shink_right` method, but instead of subtracting
    /// the number of bytes from the `Span`'s endpoint, the number of bytes are
    /// *added* to the *starting* point of the `Span`.
    ///
    /// This should generally be avoided except in the case of cleaning up
    /// source code comments with trailing/unnecessary boundary character(s).
    pub fn shrink_left(self, c: char) -> Self {
        let Span(Pos(a), end @ Pos(b)) = self;
        let len = c.len_utf8() as u32;
        if a.abs_diff(b) > len
        /* && a + len < b */
        {
            let sum = a + len;
            if sum < b {
                return Span(Pos(sum), end);
            }
        };
        self
    }
}

impl Dummy for Span {
    const DUMMY: Self = Self(Pos::ZERO, Pos::ZERO);

    fn is_dummy(&self) -> bool {
        self.0.is_dummy() && self.1.is_dummy() || (self.0 >= self.1)
    }

    fn partial_dummy(&self) -> bool {
        self.0.is_dummy() || self.1.is_dummy()
    }
}

#[derive(Clone, Copy, Debug, Hash)]
pub struct Spanned<T>(pub T, pub Span);

impl<T> Spanned<T> {
    pub fn new(item: T, span: Span) -> Self {
        Self(item, span)
    }

    pub fn as_tuple(self) -> (T, Span) {
        (self.0, self.1)
    }

    #[inline]
    pub fn item(self) -> T {
        self.0
    }

    #[inline]
    pub fn span(&self) -> Span {
        self.1
    }

    pub fn map<U, F: FnMut(T) -> U>(self, mut f: F) -> Spanned<U> {
        Spanned(f(self.0), self.1)
    }

    /// Given a span, returns a new span containing the minimum `Pos` as the
    /// starting point and the maximum `Pos` as the ending point.
    pub fn union(&self, other: Span) -> Self
    where
        T: Clone,
    {
        let Spanned(t, Span(a1, a2)) = self.clone();
        let Span(b1, b2) = other;
        let mut ss = [a1, a2, b1, b2];
        ss.sort();
        Spanned(t, Span(ss[0], ss[3]))
    }
}

impl<T> Eq for Spanned<T> where T: Eq {}

impl<T> std::cmp::PartialEq for Spanned<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.span() == other.span()
    }
}

impl<T> std::cmp::PartialOrd for Spanned<T>
where
    T: PartialEq,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.1.partial_cmp(&other.1)
    }
}

impl Pos {
    pub fn dummy() -> Pos {
        Pos::ZERO
    }

    pub fn is_dummy(&self) -> bool {
        self.is_zero()
    }

    /// Returns the number of bytes spanned by a UTF8 encoded character.
    pub fn len_utf8(c: char) -> Self {
        Self(c.len_utf8() as u32)
    }

    pub fn as_u32(self) -> u32 {
        *self
    }

    pub fn strlen<S: AsRef<str>>(string: S) -> Self {
        Self(string.as_ref().len() as u32)
    }
}

impl WithSpan for Pos {
    fn get_pos(&self) -> Pos {
        *self
    }
}

impl WithLoc for Loc {
    fn get_loc(&self) -> Loc {
        *self
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Loc {
    pub row: Row,
    pub col: Col,
}

impl Default for Loc {
    fn default() -> Self {
        Self {
            row: Row::ONE,
            col: Col::ZERO,
        }
    }
}

impl std::fmt::Display for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_dummy() {
            write!(f, "(?:?)")
        } else {
            write!(f, "{}:{}", self.row, self.col)
        }
    }
}

impl std::fmt::Debug for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line {}, column {}", self.row.0, self.col.0)
    }
}

impl Loc {
    pub fn new() -> Self {
        Self::default()
    }

    /// Increments the `col` field by 1 and, for the char given,
    /// returns a `BytePos` containing the number of bytes in the utf8
    /// encoding of that character.
    pub fn incr_column(&mut self, ch: char) -> Pos {
        let len = ch.len_utf8() as u32;
        self.col += Col::ONE;
        Pos(len)
    }

    /// Resets the column value in the `col` to 0. This occurs when
    /// encountering a line-feed character `\n` during lexing.
    pub fn reset_col(&mut self) {
        self.col = Col::ZERO;
    }

    /// Increments the `row` fields by 1, resetting the `col`
    /// field to `0`. Like with `incr_column`, this returns the number
    /// of bytes read.
    pub fn incr_row(&mut self) -> Pos {
        // self.pos += 1;
        self.row += Row::ONE;
        self.reset_col();
        Pos('\n'.len_utf8() as u32)
    }

    /// Since we always begin on a `row` value of 1, we can easily tell whether
    /// a given `Span` is invalid based on whether `row` has a 0 value.
    ///
    /// Additionally, a `dummy` column value is defined as the highest column
    /// value attainable by the `Col`'s inner type, i.e., `u32::MAX`.
    pub fn is_dummy(&self) -> bool {
        self.row.is_dummy() || self.col.is_dummy()
    }

    /// Utility method for comparing `Location` structs
    pub fn row_eq(&self, rhs: &Self) -> bool {
        self.row == rhs.row
    }

    pub fn col_eq(&self, rhs: &Self) -> bool {
        self.col == rhs.col
    }

    /// First, we say a [`Loc`] `x` *contains* a [`Loc`] `y` if
    ///
    ///     x.row == y.row || (x.row < y.row && x.col < y.col)
    ///
    /// i.e, any of the following hold:
    ///
    /// * `y` is on the same row (= line) as `x`
    /// * both `row` and `col` values of `y` are greater than that of `x`
    pub fn contains(&self, rhs: &Self) -> bool {
        self.row == rhs.row || (self.row < rhs.row && self.col < rhs.col)
    }

    pub fn rows_between(&self, rhs: &Self) -> u32 {
        self.row.abs_diff(rhs.row.0)
    }

    pub fn cols_between(&self, rhs: &Self) -> u32 {
        self.col.abs_diff(rhs.col.0)
    }
}

impl Dummy for Loc {
    /// Dummy `Position` for situations in which the only requirement
    /// is the existence of a `Position`. Useful as an intermediate value.
    ///
    /// Note: dummy values can be identified by having a `row` value
    /// of `Row::ZERO` or a `col` value of `u32::MAX`, while `Position`
    /// has a default (and starting) `row` value of `Row::ONE`.
    const DUMMY: Self = Self {
        row: Row::ZERO,
        col: Col::MAX,
    };

    fn partial_dummy(&self) -> bool {
        self.row.is_dummy() || self.col.is_dummy()
    }
}

/// Essentially a `Span`, but instead of holding byte positions, it holds `Loc`
/// values to form a "rectangular" range, where the `start` corresponds to the
/// top left corner, and the `end` corresponds to the bottom right. Note that
/// the `row` values of the contained `Loc` values may coincide, effectively
/// describing a line (with the same analogously applying to respective `col`
/// values).
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    pub start: Loc,
    pub end: Loc,
}

impl Location {
    /// Given another `Location`, will return a new `Location` such that the
    /// starting `Loc` contains the minimum `row` and `col` values, and the
    /// ending `Loc` contains the maximum `row` and `col` values.
    pub fn union(&self, other: &Self) -> Self {
        let mut rows =
            [self.start.row, self.end.row, other.start.row, other.end.row];
        let mut cols =
            [self.start.col, self.end.col, other.start.col, other.end.col];
        rows.sort();
        cols.sort();
        Location {
            start: Loc {
                row: rows[0],
                col: cols[0],
            },
            end: Loc {
                row: rows[3],
                col: cols[3],
            },
        }
    }

    /// Returns the number of rows between the starting `Loc` and the ending
    /// `Loc`. Note: this does NOT take sign into account.
    pub fn rows(&self) -> u32 {
        self.start.row.abs_diff(self.end.row.0)
    }

    /// Returns the number of columns between the starting `Loc` and the ending
    /// `Loc`. Note: this does NOT take sign into account.
    pub fn cols(&self) -> u32 {
        self.start.col.abs_diff(self.end.col.0)
    }
}

impl Default for Location {
    fn default() -> Self {
        Self {
            start: Loc::default(),
            end: Loc::default(),
        }
    }
}

impl Dummy for Location {
    const DUMMY: Self = Self {
        start: Loc::DUMMY,
        end: Loc::DUMMY,
    };

    fn partial_dummy(&self) -> bool {
        self.start.is_dummy()
            || self.end.is_dummy()
            || self.start.row > self.end.row
            || self.start.col > self.end.col
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Located<T>(pub T, pub Location);

impl<T> Located<T> {
    pub fn new(item: T, location: Location) -> Self {
        Self(item, location)
    }

    pub fn as_tuple(self) -> (T, Location) {
        (self.0, self.1)
    }

    pub fn item(self) -> T {
        self.0
    }

    pub fn location(&self) -> Location {
        self.1
    }

    pub fn map<U, F>(self, mut f: F) -> Located<U>
    where
        F: FnMut(T) -> U,
    {
        Located(f(self.0), self.1)
    }

    pub fn union(self, other: Location) -> Self {
        let Located(t, location) = self;
        Located(t, location.union(&other))
    }
}

// #[cfg(test)]
// mod tests {
//     #[test]
//     fn it_works() {
//         let result = 2 + 2;
//         assert_eq!(result, 4);
//     }
// }
