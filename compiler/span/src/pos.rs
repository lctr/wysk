use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize)]
pub struct BytePos(pub u32);

impl BytePos {
    pub const MAX: Self = Self(u32::MAX);
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    pub fn new(n: u32) -> Self {
        BytePos(n)
    }

    pub fn as_u32(self) -> u32 {
        self.0
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }

    pub fn is_dummy(&self) -> bool {
        *self == Self::MAX
    }

    #[inline]
    pub fn abs_diff(self, other: Self) -> u32 {
        self.0.abs_diff(other.0)
    }

    /// Returns the number of bytes spanned by a UTF8 encoded character.
    pub fn len_utf8(c: char) -> Self {
        Self(c.len_utf8() as u32)
    }

    pub fn strlen<S: AsRef<str>>(string: S) -> Self {
        Self(string.as_ref().len() as u32)
    }

    pub fn is_char_boundary<S: AsRef<str>>(&self, s: S) -> bool {
        let idx = self.as_usize();
        s.as_ref().char_indices().any(|(n, _)| idx == n)
    }

    pub fn str_range(s: &str) -> std::ops::Range<Self> {
        Self(0)..Self(s.len() as u32)
    }

    pub fn str_bounds(s: &str) -> (Self, Self) {
        (Self::ZERO, Self(s.len() as u32))
    }

    pub fn range_from(&self) -> std::ops::RangeFrom<usize> {
        self.as_usize()..
    }

    pub fn range_to(&self) -> std::ops::RangeTo<usize> {
        ..(self.as_usize())
    }

    pub fn from_char(c: char) -> Self {
        Self(c.len_utf8() as u32)
    }
}

impl std::ops::Add for BytePos {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        assert!({
            let max = u32::MAX as usize;
            self.as_usize() + rhs.as_usize() < max
        });
        BytePos(self.0 + rhs.0)
    }
}

impl std::ops::AddAssign for BytePos {
    fn add_assign(&mut self, rhs: Self) {
        debug_assert!(self.as_usize() + rhs.as_usize() < u32::MAX as usize);
        self.0 += rhs.0;
    }
}

impl std::ops::AddAssign<char> for BytePos {
    fn add_assign(&mut self, rhs: char) {
        debug_assert!(self.as_usize() + rhs.len_utf8() < u32::MAX as usize);
        self.0 += rhs.len_utf8() as u32;
    }
}

impl std::ops::Add<u32> for BytePos {
    type Output = Self;

    fn add(self, rhs: u32) -> Self::Output {
        debug_assert!(self.as_usize() + (rhs as usize) < u32::MAX as usize);
        BytePos(self.0 + rhs)
    }
}

impl std::ops::Add<&str> for BytePos {
    type Output = Self;
    fn add(self, rhs: &str) -> Self::Output {
        debug_assert!(self.as_usize() + rhs.len() < u32::MAX as usize);
        BytePos(self.0 + rhs.len() as u32)
    }
}

impl std::ops::Sub for BytePos {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        assert!(self.0 >= rhs.0);
        BytePos(self.0 - rhs.0)
    }
}

impl std::ops::SubAssign<char> for BytePos {
    fn sub_assign(&mut self, rhs: char) {
        let len = rhs.len_utf8() as u32;
        debug_assert!(self.0 >= len);
        self.0 -= len;
    }
}

impl PartialEq<usize> for BytePos {
    fn eq(&self, other: &usize) -> bool {
        self.as_usize() == *other
    }
}

impl PartialEq<BytePos> for usize {
    fn eq(&self, other: &BytePos) -> bool {
        *self == other.as_usize()
    }
}

impl PartialEq<u32> for BytePos {
    fn eq(&self, other: &u32) -> bool {
        self.0 == *other
    }
}

impl PartialEq<BytePos> for u32 {
    fn eq(&self, other: &BytePos) -> bool {
        *self == other.0
    }
}

impl PartialOrd<usize> for BytePos {
    fn partial_cmp(&self, other: &usize) -> Option<std::cmp::Ordering> {
        self.as_usize().partial_cmp(other)
    }
}

impl PartialOrd<BytePos> for usize {
    fn partial_cmp(&self, other: &BytePos) -> Option<std::cmp::Ordering> {
        other.as_usize().partial_cmp(self)
    }
}

impl PartialOrd<u32> for BytePos {
    fn partial_cmp(&self, other: &u32) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(other)
    }
}

impl PartialOrd<BytePos> for u32 {
    fn partial_cmp(&self, other: &BytePos) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&other.0)
    }
}

impl std::fmt::Display for BytePos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "byte {}", &self.0)
    }
}

impl std::fmt::Debug for BytePos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BytePos({})", &self.0)
    }
}
