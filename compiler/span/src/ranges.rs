use serde::{Deserialize, Serialize};

use crate::col::Col;
use crate::coord::Coord;
use crate::pos::BytePos;
use crate::row::Row;

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Span(pub BytePos, pub BytePos);

impl Span {
    /// Returns a `Span` ranging over an entire string, starting from
    /// 0 and ending in the string's length.
    pub fn of_str(s: impl AsRef<str>) -> Self {
        let (a, b) = BytePos::str_bounds(s.as_ref());
        Self(a, b)
    }

    /// Returns `true` if the starting point is equal to the end point.
    pub fn is_empty(&self) -> bool {
        self.0 == self.1
    }

    /// Returns the absolute difference between the start and end
    /// point. Note that this method works identically for invalid
    /// (backwards) spans as it does for regular spans with starting
    /// points less-than or equal to the endpoints.
    pub fn len(&self) -> usize {
        self.1.abs_diff(self.0) as usize
    }

    pub fn contains(&self, other: Span) -> bool {
        self.start() <= other.start() && self.end() >= other.end()
    }

    pub fn contained_in<S: AsRef<str>>(&self, s: S) -> bool {
        let len = s.as_ref().len();
        self.start().as_usize() < len && self.end().as_usize() < len
    }

    #[inline]
    pub fn start(&self) -> BytePos {
        self.0
    }

    #[inline]
    pub fn end(&self) -> BytePos {
        self.1
    }

    /// Returns `true` if the starting point is greater than the end
    /// point, otherwise returns `false`.
    pub fn is_backwards(&self) -> bool {
        self.start() > self.end()
    }

    pub fn usize_pair(self) -> (usize, usize) {
        (self.start().as_usize(), self.end().as_usize())
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

    /// Reduces the width of a given span by decreasing the end point
    /// by the `utf-8 length` of a character while leaving the
    /// starting point untouched, i.e., given a `Span` and some
    /// character `c`, returns a new `Span` with the same starting
    /// point and a new endpoint resulting from subtracting the UTF8
    /// length of `c` from the `Span`s end. If the `Span` does not
    /// range over enough bytes (e.g., the resulting span would have
    /// the same start and end), the same `Span` is returned
    /// unchanged.
    ///
    /// This should generally be avoided except in the case of
    /// cleaning up source code comments with trailing/unnecessary
    /// boundary character(s).
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

    /// Reduces the width of a span by increasing the starting point
    /// by the `utf-8 length` of a character while leaving the end
    /// point untouched; analogous to the `Span::shink_right` method,
    /// but instead of subtracting the number of bytes from the
    /// `Span`'s endpoint, the number of bytes are *added* to the
    /// *starting* point of the `Span`.
    ///
    /// This should generally be avoided except in the case of
    /// cleaning up source code comments with trailing/unnecessary
    /// boundary character(s).
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

    /// Grows the width of the span from the right, increasing the end
    /// position by the number of bytes provided while leaving the
    /// starting point untouched.
    pub fn grow_right(self, bytes: &[u8]) -> Self {
        let Span(start, BytePos(end)) = self;
        debug_assert!(end as usize + bytes.len() < u32::MAX as usize);

        Span(start, BytePos(bytes.len() as u32 + end))
    }

    pub fn safe_str_slice(self, s: &str) -> &str {
        let start = self.start().as_usize();
        let end = self.end().as_usize();
        let lim = s.len();
        if start == end || start >= lim || end >= lim {
            ""
        } else if start > end {
            &s[end..start]
        } else {
            &s[start..end]
        }
    }

    /// If the `Span` is contained within the given string slice, then
    /// this returns a new `Span` whose end point has been decreased by the
    /// number of bytes corresponding to whitespace characters within
    /// the substring of the provided string slice for the original `Span`.
    ///
    /// If the `Span` is not contained within the provided string
    /// slice, then the `Span` returned will be identical to the original.
    pub fn trim_end(self, s: &str) -> Self {
        if self.contained_in(s) {
            let s = &s[self];
            let diff = s.len() - s.trim_end().len();
            Span(self.start(), BytePos(self.end().as_u32() - (diff as u32)))
        } else {
            self
        }
    }

    /// If the `Span` is contained within the given string slice, then
    /// this returns a new `Span` with a starting point that has been
    /// increased by the number of bytes that correspond to whitespace
    /// in the subslice corresponding to the original's `Span` within
    /// the given string slice.     
    ///
    /// If the `Span` is not contained within the provided string
    /// slice, then the `Span` returned will be identical to the
    /// original.
    pub fn trim_start(self, s: &str) -> Self {
        if self.contained_in(s) {
            let s = &s[self];
            let diff = s.len() - s.trim_start().len();
            Span(BytePos(self.start().as_u32() + diff as u32), self.end())
        } else {
            self
        }
    }

    /// If the `Span` is contained within the given string slice, then
    /// this returns a new `Span` with a starting point that has been
    /// increased by the number of bytes that correspond to whitespace
    /// in the subslice corresponding to the original's `Span` within
    /// the given string slice.     
    ///
    /// If the `Span` is not contained within the provided string
    /// slice, then the `Span` returned will be identical to the
    /// original.
    pub fn trim(self, s: &str) -> Self {
        self.trim_start(s).trim_end(s)
    }
}

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

impl From<Span> for std::ops::Range<usize> {
    fn from(span: Span) -> Self {
        span.range()
    }
}

impl From<std::ops::Range<usize>> for Span {
    fn from(range: std::ops::Range<usize>) -> Self {
        debug_assert!({
            let max = u32::MAX as usize;
            range.start < max && range.end < max
        });
        Span(BytePos(range.start as u32), BytePos(range.end as u32))
    }
}

impl std::ops::Add for Span {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        debug_assert!({
            let max = u32::MAX as usize;
            self.start().as_usize() + rhs.start().as_usize() < max
                && self.end().as_usize() + rhs.start().as_usize() < max
        });
        Span(self.start() + rhs.start(), self.end() + rhs.start())
    }
}

impl std::ops::Add<BytePos> for Span {
    type Output = Self;

    fn add(self, rhs: BytePos) -> Self::Output {
        debug_assert!(!rhs.is_dummy());
        Span(self.start() + rhs, self.end() + rhs)
    }
}

impl std::ops::AddAssign<BytePos> for Span {
    fn add_assign(&mut self, rhs: BytePos) {
        debug_assert!(!rhs.is_dummy());
        let Span(lo, hi) = self;
        *lo += rhs;
        *hi += rhs;
    }
}

impl std::ops::Sub for Span {
    type Output = Self;

    /// Shift a span to the left by subtracting the starting point
    /// of the subtrahend from the start and endpoint of this span so
    /// that `Span(a, b) - Span(c, d) = Spn(a - c, b - c)`.
    fn sub(self, rhs: Self) -> Self::Output {
        assert!(self.contains(rhs));
        Span(self.start() - rhs.start(), self.end() - rhs.start())
    }
}

impl std::ops::Index<Span> for str {
    type Output = str;

    fn index(&self, index: Span) -> &Self::Output {
        &self[index.range()]
    }
}

/// Essentially a `Span`, but instead of holding byte positions, it
/// holds `Coord` values to form a "rectangular" `Region`, where the
/// `start` corresponds to the top left corner, and the `end`
/// corresponds to the bottom right. Note that the `row` values of the
/// contained `Coord` values may coincide, effectively describing a line
/// (with the same analogously applying to respective `col` values).
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Region {
    pub start: Coord,
    pub end: Coord,
}

impl std::fmt::Display for Region {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}-{}:{}",
            &self.start.row, &self.start.col, &self.end.row, &self.end.col
        )
    }
}

impl Region {
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
        Region {
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
        self.start.row.abs_diff(self.end.row) as usize
    }

    /// Returns the number of columns between the starting `Loc` and the ending
    /// `Loc`. Note: this does NOT take sign into account.
    #[inline]
    pub fn col_diff(&self) -> usize {
        self.start.col.abs_diff(self.end.col) as usize
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

impl Default for Region {
    fn default() -> Self {
        Self {
            start: Coord::default(),
            end: Coord::default(),
        }
    }
}

impl std::ops::Index<Region> for String {
    type Output = str;

    fn index(&self, index: Region) -> &Self::Output {
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

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CoordSpan {
    pub coord: Coord,
    pub span: Span,
}

impl CoordSpan {
    pub fn row(&self) -> Row {
        self.coord.row
    }
    pub fn col(&self) -> Col {
        self.coord.col
    }
    pub fn coord(&self) -> Coord {
        self.coord
    }
    pub fn start(&self) -> BytePos {
        self.span.start()
    }
    pub fn end(&self) -> BytePos {
        self.span.end()
    }
    pub fn span(&self) -> Span {
        self.span
    }
    pub fn len(&self) -> usize {
        self.span.len()
    }
    pub fn is_empty(&self) -> bool {
        self.span.is_empty()
    }
    pub fn range(&self) -> std::ops::Range<usize> {
        self.span.range()
    }
}

impl PartialEq<Coord> for CoordSpan {
    fn eq(&self, other: &Coord) -> bool {
        self.coord == *other
    }
}

impl std::ops::Index<CoordSpan> for str {
    type Output = str;

    fn index(&self, index: CoordSpan) -> &Self::Output {
        debug_assert!(index.span().contained_in(self));
        &self[index.span()]
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Position {
    pub span: Span,
    pub region: Region,
}

impl Position {
    pub fn new(span: Span, region: Region) -> Position {
        Position { span, region }
    }

    pub fn parts(self) -> (Span, Region) {
        let Position { span, region } = self;
        (span, region)
    }

    pub fn span(&self) -> Span {
        self.span
    }

    #[inline]
    pub fn location(&self) -> Region {
        self.region
    }

    #[inline]
    pub fn coord_start(&self) -> Coord {
        self.region.start
    }
    #[inline]
    pub fn coord_end(&self) -> Coord {
        self.region.end
    }
    #[inline]
    pub fn row_start(&self) -> Row {
        self.region.start.row
    }
    #[inline]
    pub fn row_end(&self) -> Row {
        self.region.end.row
    }
    #[inline]
    pub fn is_multiline(&self) -> bool {
        self.region.start.row < self.region.end.row
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
        (self.region.start.col - self.region.end.col).as_usize()
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.span.is_empty() || self.region.is_empty()
    }
    pub fn union(&self, other: &Position) -> Position {
        Position {
            span: self.span.union(&other.span),
            region: self.region.union(&other.region),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trim_span() {
        let text = "hello  there  now";
        let span = Span(BytePos::strlen("hello"), BytePos::strlen("hello  there  "));
        assert!(&text[span] == "  there  ");
        let actual = span.trim(text);
        let expected = Span(BytePos::strlen("hello  "), BytePos::strlen("hello  there"));
        assert_eq!(actual, expected)
    }
}
