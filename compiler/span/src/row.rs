use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Row(pub(crate) u32);

/// `Row` values begin at `1`, with a `Row` value of `0` reserved for
/// dummy values.
impl Default for Row {
    fn default() -> Self {
        Self(1)
    }
}

impl Row {
    pub const MAX: Self = Self(u32::MAX);
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    pub fn new(n: u32) -> Self {
        Row(n)
    }

    pub fn as_u32(&self) -> u32 {
        self.0
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }

    /// Rows begin at `1`. If a `Row` is `0`, then it is a dummy value.
    pub fn is_one(&self) -> bool {
        self.0 == 1
    }

    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }

    pub fn abs_diff(self, other: Self) -> u32 {
        self.0.abs_diff(other.0)
    }

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

impl std::fmt::Debug for Row {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Row({})", &self.0)
    }
}

impl std::fmt::Display for Row {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self.0)
    }
}

impl std::ops::Add for Row {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        // debug_assert!();
        Row(self.0 + rhs.0)
    }
}

impl std::ops::Add<u32> for Row {
    type Output = Self;

    fn add(self, rhs: u32) -> Self::Output {
        Row(self.0 + rhs)
    }
}
impl std::ops::Add<usize> for Row {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        debug_assert!(self.as_usize() + rhs < u32::MAX as usize);
        Row(self.0 + rhs as u32)
    }
}
impl std::ops::AddAssign for Row {
    fn add_assign(&mut self, rhs: Self) {
        debug_assert!(self.as_usize() + rhs.as_usize() < u32::MAX as usize);
        self.0 += rhs.0;
    }
}
impl std::ops::Sub for Row {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        assert!(self.0 >= rhs.0);
        Row(self.0 - rhs.0)
    }
}
impl std::ops::Sub<u32> for Row {
    type Output = Self;

    fn sub(self, rhs: u32) -> Self::Output {
        debug_assert!(self.0 >= rhs);
        Row(self.0 - rhs)
    }
}
impl std::ops::Sub<usize> for Row {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        debug_assert!(self.as_usize() >= rhs);
        Row(self.0 - rhs as u32)
    }
}

impl PartialEq<usize> for Row {
    fn eq(&self, other: &usize) -> bool {
        self.as_usize() == *other
    }
}

impl PartialEq<Row> for usize {
    fn eq(&self, other: &Row) -> bool {
        *self == other.as_usize()
    }
}

impl PartialEq<u32> for Row {
    fn eq(&self, other: &u32) -> bool {
        self.0 == *other
    }
}

impl PartialEq<Row> for u32 {
    fn eq(&self, other: &Row) -> bool {
        *self == other.0
    }
}

impl PartialOrd<usize> for Row {
    fn partial_cmp(&self, other: &usize) -> Option<std::cmp::Ordering> {
        self.as_usize().partial_cmp(other)
    }
}

impl PartialOrd<Row> for usize {
    fn partial_cmp(&self, other: &Row) -> Option<std::cmp::Ordering> {
        other.as_usize().partial_cmp(self)
    }
}

impl PartialOrd<u32> for Row {
    fn partial_cmp(&self, other: &u32) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(other)
    }
}

impl PartialOrd<Row> for u32 {
    fn partial_cmp(&self, other: &Row) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&other.0)
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
