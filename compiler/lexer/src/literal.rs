use std::num::{ParseFloatError, ParseIntError};

use serde::{Deserialize, Serialize};
use wy_common::strenum;
use wy_intern::symbol::{self, Symbol};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Base {
    /// Base 2 (binary) integers. By default parsed as `u32`.
    Bin,
    /// Base 8 (octal) integers. By default parsed as `u32`.
    Oct,
    /// Base 16 (hexadecimal) integers. By default parsed as `u32`.
    Hex,
    /// Default base (10) for floats and integers.
    Dec,
}

impl Base {
    pub fn radix(&self) -> u32 {
        match self {
            Base::Bin => 2,
            Base::Oct => 8,
            Base::Hex => 16,
            Base::Dec => 10,
        }
    }
}

#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum IntPrefix {
    Bin = b'b',
    Oct = b'o',
    Hex = b'x',
}

impl IntPrefix {
    pub fn char(&self) -> char {
        *self as u8 as char
    }

    pub fn prefix(&self) -> &str {
        match self {
            IntPrefix::Bin => "0b",
            IntPrefix::Oct => "0o",
            IntPrefix::Hex => "0x",
        }
    }

    pub fn radix(&self) -> u32 {
        match self {
            IntPrefix::Bin => 2,
            IntPrefix::Oct => 8,
            IntPrefix::Hex => 10,
        }
    }

    pub fn base(&self) -> Base {
        match self {
            IntPrefix::Bin => Base::Bin,
            IntPrefix::Oct => Base::Oct,
            IntPrefix::Hex => Base::Hex,
        }
    }

    pub fn from_char(c: &char) -> Option<Self> {
        match c {
            &('b' | 'B') => Some(Self::Bin),
            &('x' | 'X') => Some(Self::Hex),
            &('o' | 'O') => Some(Self::Oct),
            _ => None,
        }
    }

    pub fn is_int_prefix(c: char) -> bool {
        matches!(c, 'b' | 'B' | 'o' | 'O' | 'x' | 'X')
    }
}

strenum! { NumSuffix is_num_suffix ::
    // unsigned, up to compiler to decide size
    U "u"
    U8 "u8"
    U16 "u16"
    U32 "u32"
    U64 "u64"
    // signed, up to compiler to decide size
    I "i"
    I8 "i8"
    I16 "i16"
    I32 "i32"
    I64 "i64"
    // single precision floating point
    F "f"
    // double precision floating point
    D "d"
}

impl NumSuffix {
    pub fn begins_num_suffix(ch: &char) -> bool {
        matches!(*ch, 'u' | 'i' | 'f' | 'd')
    }

    pub fn word_size(ch: &char) -> bool {
        matches!(*ch, 'u' | 'i')
    }
}

/// Literals directly parsed during the lexing process. Note that we don't
/// represent negative integers with `Literal`s, as all integers are initially
/// parsed as nonnegatives -- a negative number is represented by the AST as a
/// "negation" node containing a numeric literal.
#[derive(Copy, Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Literal {
    Byte(u8),
    Int(u32),
    Nat(u64),
    // maybe replace with an interned string symbol and parse later?
    Float(f32),
    Double(f64),
    Char(char),
    Str(Symbol),
    /// No need to intern empty strings
    EmptyStr,
}

impl Eq for Literal {}

impl std::hash::Hash for Literal {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
    }
}

impl Literal {
    pub const ZERO_INT: Self = Self::Int(0);
    pub const ZERO_NAT: Self = Self::Nat(0);
    pub const ZERO_FLT: Self = Self::Float(0.0);
    pub const ZERO_DBL: Self = Self::Double(0.0);

    #[inline]
    pub fn parse_byte(src: &str, base: Base) -> Result<u8, ParseIntError> {
        u8::from_str_radix(src, base.radix())
    }

    #[inline]
    pub fn parse_int(src: &str, base: Base) -> Result<u32, ParseIntError> {
        u32::from_str_radix(src, base.radix())
    }

    #[inline]
    pub fn parse_nat(src: &str, base: Base) -> Result<u64, ParseIntError> {
        u64::from_str_radix(src, base.radix())
    }

    #[inline]
    pub fn parse_float(src: &str) -> Result<f32, ParseFloatError> {
        src.parse::<f32>()
    }

    #[inline]
    pub fn parse_double(src: &str) -> Result<f64, ParseFloatError> {
        src.parse::<f64>()
    }

    #[inline]
    pub fn from_u8(b: u8) -> Self {
        Self::Byte(b)
    }

    #[inline]
    pub fn from_u32(n: u32) -> Self {
        Self::Int(n)
    }

    #[inline]
    pub fn from_u64(n: u64) -> Self {
        Self::Nat(n)
    }

    #[inline]
    pub fn from_f32(q: f32) -> Self {
        Self::Float(q)
    }

    #[inline]
    pub fn from_f64(d: f64) -> Self {
        Self::Double(d)
    }

    #[inline]
    pub fn from_char(c: char) -> Self {
        Self::Char(c)
    }

    #[inline]
    pub fn from_str(s: impl AsRef<str>) -> Self {
        if s.as_ref().is_empty() {
            Self::EmptyStr
        } else {
            Self::Str(symbol::intern_once(s.as_ref()))
        }
    }
}

impl From<&str> for Literal {
    fn from(s: &str) -> Self {
        Self::from_str(s)
    }
}

impl From<char> for Literal {
    fn from(c: char) -> Self {
        Self::from_char(c)
    }
}

impl From<f64> for Literal {
    fn from(dbl: f64) -> Self {
        Self::from_f64(dbl)
    }
}

impl From<f32> for Literal {
    fn from(flt: f32) -> Self {
        Self::from_f32(flt)
    }
}

impl From<u64> for Literal {
    fn from(n: u64) -> Self {
        Self::from_u64(n)
    }
}

#[cfg(target_pointer_width = "32")]
impl From<usize> for Literal {
    fn from(n: usize) -> Self {
        Literal::Nat(n as u32)
    }
}

#[cfg(target_pointer_width = "64")]
impl From<usize> for Literal {
    fn from(n: usize) -> Self {
        Literal::Nat(n as u64)
    }
}

impl From<u32> for Literal {
    fn from(n: u32) -> Self {
        Self::Int(n)
    }
}
// impl From<isize> for Literal {}
impl From<u8> for Literal {
    fn from(byte: u8) -> Self {
        Self::Byte(byte)
    }
}

impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Byte(n) => write!(f, "{}", n),
            Literal::Int(n) => write!(f, "{}", n),
            Literal::Nat(n) => write!(f, "{}", n),
            Literal::Float(n) => write!(f, "{}", n),
            Literal::Double(n) => write!(f, "{}", n),
            Literal::Char(c) => write!(f, "'{}'", c),
            Literal::Str(s) => write!(f, "\"{}\"", s),
            Literal::EmptyStr => write!(f, "\"\""),
        }
    }
}
