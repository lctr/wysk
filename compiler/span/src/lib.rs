use wy_common::newtype;

newtype! {
    { u32 in Row | New Show Usize Deref (+=) (-)
        (+ usize |rhs| rhs as u32)
        (- usize |rhs| rhs as u32)
    }
    { u32 in Col | New Show Usize Deref (+=) (-)
        (+ usize |rhs| rhs as u32)
        (- usize |rhs| rhs as u32)
    }
    { u32 in BytePos | Show Usize Deref (+=) (-)
        (+= char |rhs| rhs.len_utf8() as u32)
        (+ &str |rhs| rhs.len() as u32)
    }
}

impl BytePos {
    pub fn str_range(s: &str) -> std::ops::Range<Self> {
        Self(0)..Self(s.len() as u32)
    }

    pub fn str_bounds(s: &str) -> (Self, Self) {
        (Self::ZERO, Self(s.len() as u32))
    }

    pub fn from_char(c: char) -> Self {
        Self(c.len_utf8() as u32)
    }
}

impl Row {
    /// Returns the number of digits in the contained numeric value. Used
    /// primarily in error reporting for text alignnment purposes.
    pub fn strlen(&self) -> u32 {
        let mut n = self.0;
        let mut ct = 1;
        while n > 0 {
            n /= 10;
            ct += 1;
        }
        ct
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

/// Public interface for identifying invalid (tracking-related) values.
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

/// Public interface for dealing with `Span`s.
pub trait WithSpan {
    fn get_pos(&self) -> BytePos;

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

    fn while_pos<X>(
        &mut self,
        mut pred: impl FnMut(BytePos) -> bool,
        mut f: impl FnMut(&mut Self) -> X,
    ) -> Vec<Spanned<X>> {
        std::iter::from_fn(|| {
            if pred(self.get_pos()) {
                Some(self.spanned(|this| f(this)))
            } else {
                None
            }
        })
        .collect()
    }
}

pub trait WithLoc {
    fn get_coord(&self) -> Coord;
    fn get_row(&self) -> Row {
        WithLoc::get_coord(self).row
    }
    fn get_col(&self) -> Col {
        WithLoc::get_coord(self).col
    }
    fn located<X>(&mut self, mut f: impl FnMut(&mut Self) -> X) -> Located<X> {
        let start = WithLoc::get_coord(self);
        let x = f(self);
        let end = WithLoc::get_coord(self);
        Located(x, Location { start, end })
    }
    fn while_loc<X>(
        &mut self,
        mut pred: impl FnMut(Coord) -> bool,
        mut f: impl FnMut(&mut Self) -> X,
    ) -> Vec<Located<X>> {
        std::iter::from_fn(|| {
            if pred(self.get_coord()) {
                Some(self.located(|this| f(this)))
            } else {
                None
            }
        })
        .collect()
    }
    fn while_row<X>(
        &mut self,
        mut pred: impl FnMut(Row) -> bool,
        mut f: impl FnMut(&mut Self) -> X,
    ) -> Vec<Located<X>> {
        std::iter::from_fn(|| {
            if pred(self.get_row()) {
                Some(self.located(|this| f(this)))
            } else {
                None
            }
        })
        .collect()
    }
    fn while_col<X>(
        &mut self,
        mut pred: impl FnMut(Col) -> bool,
        mut f: impl FnMut(&mut Self) -> X,
    ) -> Vec<Located<X>> {
        std::iter::from_fn(|| {
            if pred(self.get_col()) {
                Some(self.located(|this| f(this)))
            } else {
                None
            }
        })
        .collect()
    }
}

pub trait WithPosition: WithSpan + WithLoc {
    fn get_position(&self) -> Position;
    fn get_span(&self) -> Span {
        self.get_position().span()
    }
    fn get_location(&self) -> Location {
        self.get_position().location()
    }
    fn positioned<X>(&mut self, mut f: impl FnMut(&mut Self) -> X) -> Positioned<X> {
        let pos_a = WithSpan::get_pos(self);
        let start = WithLoc::get_coord(self);
        let x = f(self);
        let pos_b = WithSpan::get_pos(self);
        let end = WithLoc::get_coord(self);
        Positioned(
            x,
            Position {
                span: Span(pos_a, pos_b),
                location: Location { start, end },
            },
        )
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

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span(pub BytePos, pub BytePos);

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.0, self.1)
    }
}

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Span({}, {})", self.0, self.1)
    }
}

impl Span {
    pub fn new(start: impl Into<BytePos>, end: impl Into<BytePos>) -> Self {
        Self(start.into(), end.into())
    }

    pub fn from_pair((start, end): (impl Into<BytePos>, impl Into<BytePos>)) -> Self {
        Self(start.into(), end.into())
    }

    pub fn from_str(s: &impl AsRef<str>) -> Self {
        let (a, b) = BytePos::str_bounds(s.as_ref());
        Self(a, b)
    }

    pub fn tuple(self) -> (BytePos, BytePos) {
        (self.0, self.1)
    }

    pub fn len(&self) -> usize {
        (self.1 - self.0).as_usize()
    }

    pub fn is_empty(&self) -> bool {
        self.0 == self.1
    }

    pub fn start(&self) -> BytePos {
        self.0
    }

    pub fn end(&self) -> BytePos {
        self.1
    }

    pub fn begin<X: WithSpan>(start: BytePos) -> impl FnMut(X) -> Span {
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

    pub fn byte_range(&self) -> std::ops::Range<BytePos> {
        self.0..self.1
    }

    pub fn union(&self, other: &Span) -> Self {
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
        let Span(start @ BytePos(a), BytePos(b)) = self;
        let len = c.len_utf8() as u32;
        if a.abs_diff(b) > len
        /* && b > len */
        {
            let diff = b - len;
            if a < diff {
                return Span(start, BytePos(diff));
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
        let Span(BytePos(a), end @ BytePos(b)) = self;
        let len = c.len_utf8() as u32;
        if a.abs_diff(b) > len
        /* && a + len < b */
        {
            let sum = a + len;
            if sum < b {
                return Span(BytePos(sum), end);
            }
        };
        self
    }

    /// Grows the total width of the span by reducing the *starting point* by
    /// according to the number bytes provided.
    pub fn grow_left(self, bytes: &[u8]) -> Self {
        let Span(BytePos(start), end) = self;
        let len = bytes.len() as u32;
        if len < start {
            return Span(BytePos(start - len), end);
        }
        self
    }

    pub fn grow_right(self, bytes: &[u8]) -> Self {
        let Span(start, BytePos(end)) = self;
        Span(start, BytePos(bytes.len() as u32 + end))
    }

    pub fn in_str(&self, s: &str) -> Box<str> {
        std::ops::Index::index(&Str(s), *self).into()
    }
}

impl Dummy for Span {
    const DUMMY: Self = Self(BytePos::ZERO, BytePos::ZERO);

    fn is_dummy(&self) -> bool {
        self.0.is_dummy() && self.1.is_dummy() || self.is_empty()
    }

    fn partial_dummy(&self) -> bool {
        self.0.is_dummy() || self.1.is_dummy()
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Str<'a>(pub &'a str);

impl<'a> Str<'a> {
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn bytelen(&self) -> BytePos {
        BytePos::strlen(self.0)
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl std::ops::Index<Span> for Str<'_> {
    type Output = str;

    fn index(&self, index: Span) -> &Self::Output {
        let start = index.start().as_usize();
        let end = index.end().as_usize();
        let lim = self.0.len();
        if start == end || start >= lim || end >= lim {
            ""
        } else if start > end {
            &self.0[end..start]
        } else {
            &self.0[start..end]
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Spanned<T>(pub T, pub Span);

impl<T> Spanned<T> {
    pub fn new(item: T, span: Span) -> Self {
        Self(item, span)
    }

    pub fn as_tuple(self) -> (T, Span) {
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

    #[inline]
    pub fn span(&self) -> Span {
        self.1
    }

    #[inline]
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> Spanned<U> {
        Spanned(f(self.0), self.1)
    }

    pub fn map_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Spanned<U> {
        Spanned(f(&self.0), self.1)
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
}

impl<T> Spanned<&T> {
    pub fn cloned(self) -> Spanned<T>
    where
        T: Clone,
    {
        let Spanned(t, span) = self;
        Spanned(t.clone(), span)
    }

    pub fn copied(self) -> Spanned<T>
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

impl<T> std::hash::Hash for Spanned<T>
where
    T: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl BytePos {
    pub fn dummy() -> BytePos {
        BytePos::ZERO
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

impl WithSpan for BytePos {
    fn get_pos(&self) -> BytePos {
        *self
    }
}

impl WithLoc for Coord {
    fn get_coord(&self) -> Coord {
        *self
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Coord {
    pub row: Row,
    pub col: Col,
}

impl Default for Coord {
    fn default() -> Self {
        Self {
            row: Row::ONE,
            col: Col::ZERO,
        }
    }
}

impl std::fmt::Display for Coord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_dummy() {
            write!(f, "(?:?)")
        } else {
            write!(f, "{}:{}", self.row, self.col)
        }
    }
}

impl std::fmt::Debug for Coord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line {}, column {}", self.row.0, self.col.0)
    }
}

impl Coord {
    pub fn new() -> Self {
        Self::default()
    }

    /// Increments the `col` field by 1 and, for the char given,
    /// returns a `BytePos` containing the number of bytes in the utf8
    /// encoding of that character.
    pub fn incr_column(&mut self, ch: char) -> BytePos {
        let len = ch.len_utf8() as u32;
        self.col += Col::ONE;
        BytePos(len)
    }

    /// Resets the column value in the `col` to 0. This occurs when
    /// encountering a line-feed character `\n` during lexing.
    pub fn reset_col(&mut self) {
        self.col = Col::ZERO;
    }

    /// Increments the `row` fields by 1, resetting the `col`
    /// field to `0`. Like with `incr_column`, this returns the number
    /// of bytes read.
    pub fn incr_row(&mut self) -> BytePos {
        // self.pos += 1;
        self.row += Row::ONE;
        self.reset_col();
        BytePos('\n'.len_utf8() as u32)
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
    /// ```rust,ignore
    /// x.row == y.row || (x.row < y.row && x.col < y.col)
    /// ```
    /// i.e, any of the following hold:
    ///
    /// * `y` is on the same row (= line) as `x`
    /// * both `row` and `col` values of `y` are greater than that of `x`
    pub fn contains(&self, rhs: &Self) -> bool {
        self.row == rhs.row || (self.row < rhs.row && self.col < rhs.col)
    }

    #[inline]
    pub fn row_diff(&self, rhs: &Self) -> usize {
        self.row.abs_diff(rhs.row.0) as usize
    }

    #[inline]
    pub fn cols_between(&self, rhs: &Self) -> usize {
        self.col.abs_diff(rhs.col.0) as usize
    }

    pub fn sol(&self, line_offset: usize) -> bool {
        self.col.as_usize() == line_offset
    }
}

impl Dummy for Coord {
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
    pub start: Coord,
    pub end: Coord,
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Location({}, {})", &self.start, &self.end)
    }
}

impl Location {
    /// Given another `Location`, will return a new `Location` such that the
    /// starting `Loc` contains the minimum `row` and `col` values, and the
    /// ending `Loc` contains the maximum `row` and `col` values.
    pub fn union(&self, other: &Self) -> Self {
        let mut rows = [self.start.row, self.end.row, other.start.row, other.end.row];
        let mut cols = [self.start.col, self.end.col, other.start.col, other.end.col];
        rows.sort();
        cols.sort();
        let [row_start, _, _, row_end] = rows;
        let [col_start, _, _, col_end] = cols;
        Location {
            start: Coord {
                row: row_start,
                col: col_start,
            },
            end: Coord {
                row: row_end,
                col: col_end,
            },
        }
    }

    /// Returns the number of rows between the starting `Loc` and the ending
    /// `Loc`. Note: this does NOT take sign into account.
    #[inline]
    pub fn row_diff(&self) -> usize {
        self.start.row.abs_diff(self.end.row.0) as usize
    }

    /// Returns the number of columns between the starting `Loc` and the ending
    /// `Loc`. Note: this does NOT take sign into account.
    #[inline]
    pub fn col_diff(&self) -> usize {
        self.start.col.abs_diff(self.end.col.0) as usize
    }

    #[inline]
    pub fn row_range(&self) -> std::ops::Range<Row> {
        self.start.row..self.end.row
    }

    #[inline]
    pub fn col_range(&self) -> std::ops::Range<Col> {
        self.start.col..self.end.col
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

impl Default for Location {
    fn default() -> Self {
        Self {
            start: Coord::default(),
            end: Coord::default(),
        }
    }
}

impl Dummy for Location {
    const DUMMY: Self = Self {
        start: Coord::DUMMY,
        end: Coord::DUMMY,
    };

    fn is_dummy(&self) -> bool {
        self.start.is_dummy() || self.end.is_dummy() || self.is_empty()
    }

    fn partial_dummy(&self) -> bool {
        self.start.is_dummy()
            || self.end.is_dummy()
            || self.start.row > self.end.row
            || self.start.col > self.end.col
    }
}

impl std::ops::Index<Location> for String {
    type Output = str;

    fn index(&self, index: Location) -> &Self::Output {
        let s = self.char_indices();
        let mut start = 0;
        let mut end = 0;
        for (p, c) in s {
            if p < index.start.col.as_usize() {
                start += c.len_utf8();
            } else if p == index.start.col.as_usize() {
                end = start + c.len_utf8();
            } else if p < index.end.col.as_usize() {
                end += c.len_utf8()
            } else {
                break;
            }
        }
        &self.as_str()[start..end]
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Located<T>(pub T, pub Location);

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
    pub fn new(item: T, location: Location) -> Self {
        Self(item, location)
    }

    #[inline]
    pub fn as_tuple(self) -> (T, Location) {
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
    pub fn location(&self) -> Location {
        self.1
    }

    #[inline]
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> Located<U> {
        Located(f(self.0), self.1)
    }

    #[inline]
    pub fn map_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Located<U> {
        Located(f(&self.0), self.1)
    }

    pub fn union(self, other: Location) -> Self {
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
impl<T> Located<Vec<T>> {
    pub fn veclen(&self) -> usize {
        self.0.len()
    }
    pub fn as_slice(&self) -> &[T] {
        self.0.as_slice()
    }
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.0.as_mut_slice()
    }
    pub fn items_iter(&self) -> std::slice::Iter<'_, T> {
        self.0.iter()
    }

    pub fn items_iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.0.iter_mut()
    }

    pub fn push(&mut self, located: Located<T>) {
        let (item, loc) = located.as_tuple();
        self.1 = self.1.union(&loc);
        self.0.push(item);
    }

    pub fn extend(&mut self, iter: impl IntoIterator<Item = Located<T>>) {
        iter.into_iter().for_each(|Located(item, loc)| {
            self.0.push(item);
            self.1 = self.1.union(&loc);
        })
    }

    pub fn reverse(&mut self) {
        self.0.reverse()
    }
}

impl<X, E> Located<Result<X, E>> {
    pub fn as_result(self) -> Result<Located<X>, E> {
        self.0.map(|x| Located(x, self.1))
    }
    pub fn ok(self) -> Result<Located<X>, Located<E>> {
        self.0
            .map(|x| Located(x, self.1))
            .map_err(|e| Located(e, self.1))
    }
    pub fn ok_or<A>(self, mut f: impl FnMut(E, Location) -> A) -> Result<Located<X>, A> {
        self.0.map(|x| Located(x, self.1)).map_err(|e| f(e, self.1))
    }
    pub fn flat_map<Y>(self, mut f: impl FnMut(X) -> Result<Y, E>) -> Result<Located<Y>, E> {
        self.0.and_then(|x| f(x).map(|y| Located(y, self.1)))
    }
    pub fn is_ok(&self) -> bool {
        self.0.is_ok()
    }
    pub fn is_err(&self) -> bool {
        self.0.is_err()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Position {
    span: Span,
    location: Location,
}

impl Position {
    pub fn from_pairs([(pos0, start), (pos1, end)]: [(BytePos, Coord); 2]) -> Self {
        Position {
            span: Span(pos0, pos1),
            location: Location { start, end },
        }
    }
    pub fn new(span: Span, location: Location) -> Position {
        Position { span, location }
    }

    pub fn parts(self) -> (Span, Location) {
        let Position { span, location } = self;
        (span, location)
    }

    pub fn span(&self) -> Span {
        self.span
    }

    #[inline]
    pub fn location(&self) -> Location {
        self.location
    }

    #[inline]
    pub fn coord_start(&self) -> Coord {
        self.location.start
    }
    #[inline]
    pub fn coord_end(&self) -> Coord {
        self.location.end
    }
    #[inline]
    pub fn row_start(&self) -> Row {
        self.location.start.row
    }
    #[inline]
    pub fn row_end(&self) -> Row {
        self.location.end.row
    }
    #[inline]
    pub fn multiline(&self) -> bool {
        self.location.start.row < self.location.end.row
    }
    #[inline]
    pub fn byte_start(&self) -> BytePos {
        self.span.start()
    }
    #[inline]
    pub fn byte_end(&self) -> BytePos {
        self.span.end()
    }
    #[inline]
    pub fn byte_diff(&self) -> usize {
        (self.byte_end() - self.byte_start()).as_usize()
    }
    #[inline]
    pub fn row_diff(&self) -> usize {
        (self.row_end() - self.row_start()).as_usize()
    }
    #[inline]
    pub fn col_diff(&self) -> usize {
        (self.location.start.col - self.location.end.col).as_usize()
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.span.is_empty() || self.location.is_empty()
    }
    pub fn union(&self, other: &Position) -> Position {
        Position {
            span: self.span.union(&other.span),
            location: self.location.union(&other.location),
        }
    }
}

impl Dummy for Position {
    const DUMMY: Self = Self {
        span: Span::DUMMY,
        location: Location::DUMMY,
    };

    fn is_dummy(&self) -> bool {
        self.span.is_dummy() || self.location.is_dummy() || self.is_empty()
    }

    fn partial_dummy(&self) -> bool {
        self.span.partial_dummy()
            || self.location.partial_dummy()
            || self.span.is_empty()
            || self.location.is_empty()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Positioned<X>(X, Position);

impl<X> Copy for Positioned<X> where X: Copy {}

impl<X> Positioned<X> {
    pub fn new(item: X, position: Position) -> Self {
        Positioned(item, position)
    }
    pub fn parts(self) -> (X, Position) {
        (self.0, self.1)
    }

    pub fn from_pairs(item: X, [(pos0, start), (pos1, end)]: [(BytePos, Coord); 2]) -> Self {
        Positioned(
            item,
            Position {
                span: Span(pos0, pos1),
                location: Location { start, end },
            },
        )
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
    pub fn location(&self) -> Location {
        self.1.location
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
impl<T> Positioned<Vec<T>> {
    pub fn veclen(&self) -> usize {
        self.0.len()
    }
    pub fn as_slice(&self) -> &[T] {
        self.0.as_slice()
    }
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.0.as_mut_slice()
    }
    pub fn items_iter(&self) -> std::slice::Iter<'_, T> {
        self.0.iter()
    }

    pub fn items_iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.0.iter_mut()
    }

    pub fn push(&mut self, positioned: Positioned<T>) {
        let (item, loc) = positioned.parts();
        self.1 = self.1.union(&loc);
        self.0.push(item);
    }

    pub fn extend(&mut self, iter: impl IntoIterator<Item = Positioned<T>>) {
        iter.into_iter().for_each(|Positioned(item, loc)| {
            self.0.push(item);
            self.1 = self.1.union(&loc);
        })
    }

    pub fn reverse(&mut self) {
        self.0.reverse()
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
