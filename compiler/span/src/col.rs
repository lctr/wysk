use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize)]
pub struct Col(pub(crate) u32);

impl Col {
    pub const MAX: Self = Self(u32::MAX);
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    pub fn new(n: u32) -> Self {
        Col(n)
    }

    pub fn as_u32(&self) -> u32 {
        self.0
    }

    #[inline]
    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }

    pub fn abs_diff(self, other: Self) -> u32 {
        self.0.abs_diff(other.0)
    }

    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }

    pub fn is_max(&self) -> bool {
        self.0 == u32::MAX
    }

    /// Returns a string slice of the `nth` grapheme of a given string
    /// slice by generating a sequence of all character boundaries of
    /// the slice and then taking the substring bound between the `n`th
    /// and `n+1`th char boundaries.
    pub fn of_str<'a>(&self, s: &'a str) -> &'a str {
        let m = self.as_usize();
        let w = s.len();
        if m > w {
            return "";
        };
        let mut bds = (0..w)
            .filter(|n| s.is_char_boundary(*n))
            .enumerate()
            .filter_map(|(i, b)| if i == m || i == m + 1 { Some(b) } else { None });
        match (bds.next(), bds.next()) {
            (Some(a), Some(b)) => &s[a..b],
            (Some(a), None) => &s[a..],
            (None, _) => "",
        }
    }

    pub fn byte(s: impl AsRef<str>) -> Col {
        s.as_ref()
            .char_indices()
            .last()
            .map(|(n, _)| Col(n as u32))
            .unwrap_or_else(|| Col::ZERO)
    }

    pub fn of_chars(s: impl AsRef<str>) -> Col {
        Col(s.as_ref().chars().count() as u32)
    }
}

impl std::fmt::Debug for Col {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Col({})", &self.0)
    }
}

impl std::fmt::Display for Col {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self.0)
    }
}

impl std::ops::Add for Col {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Col(self.0 + rhs.0)
    }
}

impl std::ops::Add<u32> for Col {
    type Output = Self;

    fn add(self, rhs: u32) -> Self::Output {
        Col(self.0 + rhs)
    }
}
impl std::ops::Add<usize> for Col {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        debug_assert!(self.as_usize() + rhs < u32::MAX as usize);
        Col(self.0 + rhs as u32)
    }
}
impl std::ops::AddAssign for Col {
    fn add_assign(&mut self, rhs: Self) {
        debug_assert!(self.as_usize() + rhs.as_usize() < u32::MAX as usize);
        self.0 += rhs.0;
    }
}

impl std::ops::AddAssign<char> for Col {
    fn add_assign(&mut self, rhs: char) {
        if matches!(rhs, '\n' | '\r') {
            self.0 = 0;
        } else {
            self.0 += 1;
        }
    }
}

impl std::ops::Sub for Col {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        assert!(self.0 >= rhs.0);
        Col(self.0 - rhs.0)
    }
}
impl std::ops::Sub<u32> for Col {
    type Output = Self;

    fn sub(self, rhs: u32) -> Self::Output {
        debug_assert!(self.0 >= rhs);
        Col(self.0 - rhs)
    }
}
impl std::ops::Sub<usize> for Col {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        debug_assert!(self.as_usize() >= rhs);
        Col(self.0 - rhs as u32)
    }
}

impl PartialEq<usize> for Col {
    fn eq(&self, other: &usize) -> bool {
        self.as_usize() == *other
    }
}

impl PartialEq<Col> for usize {
    fn eq(&self, other: &Col) -> bool {
        *self == other.as_usize()
    }
}

impl PartialEq<u32> for Col {
    fn eq(&self, other: &u32) -> bool {
        self.0 == *other
    }
}

impl PartialEq<Col> for u32 {
    fn eq(&self, other: &Col) -> bool {
        *self == other.0
    }
}

impl PartialOrd<usize> for Col {
    fn partial_cmp(&self, other: &usize) -> Option<std::cmp::Ordering> {
        self.as_usize().partial_cmp(other)
    }
}

impl PartialOrd<Col> for usize {
    fn partial_cmp(&self, other: &Col) -> Option<std::cmp::Ordering> {
        other.as_usize().partial_cmp(self)
    }
}

impl PartialOrd<u32> for Col {
    fn partial_cmp(&self, other: &u32) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(other)
    }
}

impl PartialOrd<Col> for u32 {
    fn partial_cmp(&self, other: &Col) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&other.0)
    }
}
