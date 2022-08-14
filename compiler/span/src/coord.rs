use serde::{Deserialize, Serialize};

use crate::{BytePos, Col, Row};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
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
        self.row.is_zero() || self.col.is_max()
    }

    /// Utility method for comparing `Location` structs
    pub fn row_eq(&self, rhs: &Self) -> bool {
        self.row == rhs.row
    }

    pub fn col_eq(&self, rhs: &Self) -> bool {
        self.col == rhs.col
    }

    pub fn contains(&self, rhs: &Self) -> bool {
        self.row < rhs.row && self.col < rhs.col
    }

    #[inline]
    pub fn row_diff(&self, rhs: &Self) -> usize {
        self.row.abs_diff(rhs.row) as usize
    }

    #[inline]
    pub fn cols_between(&self, rhs: &Self) -> usize {
        self.col.abs_diff(rhs.col) as usize
    }

    pub fn sol(&self, line_offset: usize) -> bool {
        self.col.as_usize() == line_offset
    }
}
