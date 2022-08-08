use serde::{Deserialize, Serialize};
use wy_common::strenum;
use wy_intern::symbol::Symbol;

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
pub enum NumPrefix {
    Bin = b'b',
    Oct = b'o',
    Hex = b'x',
}

impl NumPrefix {
    pub fn char(&self) -> char {
        *self as u8 as char
    }

    pub fn prefix(&self) -> &str {
        match self {
            NumPrefix::Bin => "0b",
            NumPrefix::Oct => "0o",
            NumPrefix::Hex => "0x",
        }
    }

    pub fn radix(&self) -> u32 {
        match self {
            NumPrefix::Bin => 2,
            NumPrefix::Oct => 8,
            NumPrefix::Hex => 10,
        }
    }

    pub fn base(&self) -> Base {
        match self {
            NumPrefix::Bin => Base::Bin,
            NumPrefix::Oct => Base::Oct,
            NumPrefix::Hex => Base::Hex,
        }
    }

    pub fn from_base(base: Base) -> Option<Self> {
        match base {
            Base::Bin => Some(NumPrefix::Bin),
            Base::Oct => Some(NumPrefix::Oct),
            Base::Hex => Some(NumPrefix::Hex),
            Base::Dec => None,
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

    pub fn to_rust_suffix(&self) -> &str {
        match self {
            NumSuffix::U => "usize",
            NumSuffix::U8 => "u8",
            NumSuffix::U16 => "u16",
            NumSuffix::U32 => "u32",
            NumSuffix::U64 => "u64",
            NumSuffix::I => "isize",
            NumSuffix::I8 => "i8",
            NumSuffix::I16 => "i16",
            NumSuffix::I32 => "i32",
            NumSuffix::I64 => "i64",
            NumSuffix::F => "f32",
            NumSuffix::D => "f64",
        }
    }
}

/// Note that we don't represent negative integers with `Literal`s, as
/// all integers are initially read as nonnegatives -- a negative
/// number is represented by the AST as a "negation" node containing a
/// numeric literal.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Literal {
    Integral {
        symbol: Symbol,
        base: Base,
        prefix: Option<NumPrefix>,
        suffix: Option<NumSuffix>,
    },
    Fractional {
        symbol: Symbol,
        base: Base,
        has_exponent: bool,
        suffix: Option<NumSuffix>,
    },
    Char(char),
    NullChar,
    Str(Symbol),
    EmptyStr,
}

impl Literal {
    pub const DIGIT_ZERO: Self = Self::Integral {
        symbol: wy_intern::sym::DIGIT_0,
        base: Base::Dec,
        prefix: None,
        suffix: None,
    };

    pub fn mk_simple_integer(val: usize) -> Self {
        let symbol = match val {
            0 => wy_intern::sym::DIGIT_0,
            1 => wy_intern::sym::DIGIT_1,
            2 => wy_intern::sym::DIGIT_2,
            3 => wy_intern::sym::DIGIT_3,
            4 => wy_intern::sym::DIGIT_4,
            5 => wy_intern::sym::DIGIT_5,
            6 => wy_intern::sym::DIGIT_6,
            7 => wy_intern::sym::DIGIT_7,
            8 => wy_intern::sym::DIGIT_8,
            9 => wy_intern::sym::DIGIT_9,
            n => wy_intern::intern_once(format!("{n}")),
        };
        Self::Integral {
            symbol,
            base: Base::Dec,
            prefix: None,
            suffix: None,
        }
    }

    pub fn try_simple_digit_byte(&self) -> Option<u8> {
        match self {
            Self::Integral { symbol, .. } if symbol.is_digit() => {
                symbol.as_str().parse::<u8>().ok()
            }
            _ => None,
        }
    }
}

impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Integral {
                symbol,
                base: _,
                prefix,
                suffix,
            } => write!(
                f,
                "{}{symbol}{}",
                if let Some(pre) = prefix {
                    pre.prefix()
                } else {
                    ""
                },
                if let Some(suf) = suffix {
                    suf.as_str()
                } else {
                    ""
                }
            ),
            Literal::Fractional {
                symbol,
                base: _,
                has_exponent: _,
                suffix,
            } => write!(
                f,
                "{symbol}{}",
                if let Some(suf) = suffix {
                    suf.as_str()
                } else {
                    ""
                }
            ),
            Literal::Char(c) => write!(f, "{c:?}"),
            Literal::NullChar => write!(f, "'\\0'"),
            Literal::Str(s) => write!(f, "\"{}\"", s.as_str()),
            Literal::EmptyStr => write!(f, "\"\""),
        }
    }
}
