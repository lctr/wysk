use serde::{Deserialize, Serialize};

pub use wy_intern::symbol::{Symbol, Symbolic};

const FRESH_PREFIX: &str = "_#";

#[derive(Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Ident {
    Upper(Symbol),
    Lower(Symbol),
    Infix(Symbol),
    Label(Symbol),
    /// Represent internally generated variables distinguishable from `Lower`
    /// variants, either for type variables or for parser/compiler generated
    /// variables.
    Fresh(u32),
}

impl std::fmt::Debug for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Upper(arg0) => write!(f, "Upper({})", arg0),
            Self::Lower(arg0) => write!(f, "Lower({})", arg0),
            Self::Infix(arg0) => write!(f, "Infix({})", arg0),
            Self::Label(arg0) => write!(f, "Label({})", arg0),
            Self::Fresh(arg0) => write!(f, "Fresh({})", arg0),
        }
    }
}

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            if self.is_fresh() { "_#" } else { "" },
            self.symbol()
        )
    }
}

impl Symbolic for Ident {
    fn get_symbol(&self) -> Symbol {
        self.symbol()
    }
}

impl Ident {
    pub const MAIN_MOD: Self = Ident::Upper(wy_intern::MAIN_MOD);
    pub const MAIN_FN: Self = Ident::Lower(wy_intern::MAIN_FN);
    pub const COLON: Self = Ident::Infix(wy_intern::COLON);
    pub const ARROW: Self = Ident::Infix(wy_intern::ARROW);
    pub const MINUS: Self = Ident::Infix(wy_intern::MINUS);
    pub const TRUE: Self = Ident::Upper(wy_intern::TRUE);
    pub const FALSE: Self = Ident::Lower(wy_intern::FALSE);

    pub const NAMES: [fn(Symbol) -> Self; 4] = [Self::Upper, Self::Lower, Self::Infix, Self::Label];

    pub fn symbol(&self) -> Symbol {
        match self {
            Self::Upper(s) | Self::Lower(s) | Self::Infix(s) | Self::Label(s) => *s,
            Self::Fresh(n) => Symbol::intern(format!("{FRESH_PREFIX}{n}")),
        }
    }
    pub fn is_upper(&self) -> bool {
        matches!(self, Self::Upper(..))
    }
    pub fn is_lower(&self) -> bool {
        matches!(self, Self::Lower(..))
    }
    pub fn is_infix(&self) -> bool {
        matches!(self, Self::Infix(..))
    }
    pub fn is_label(&self) -> bool {
        matches!(self, Self::Label(..))
    }
    pub fn is_fresh(&self) -> bool {
        matches!(self, Self::Fresh(..))
    }

    /// Returns the integer value held by the `Symbol` from this identifier.
    pub fn as_u32(self) -> u32 {
        self.symbol().as_u32()
    }

    /// Returns the constructor for the given `Ident` variant
    pub fn constructor(&self) -> fn(Symbol) -> Self {
        match self {
            Ident::Upper(_) => Ident::Upper,
            Ident::Lower(_) => Ident::Lower,
            Ident::Infix(_) => Ident::Infix,
            Ident::Label(_) => Ident::Label,
            Ident::Fresh(_) => |s| {
                use std::str::FromStr;
                let s = &s.as_str()[FRESH_PREFIX.len()..];
                Ident::Fresh(u32::from_str(s).unwrap())
            },
        }
    }

    #[inline]
    pub fn is_cons_sign(&self) -> bool {
        self == &Self::COLON
    }

    #[inline]
    pub fn is_arrow(&self) -> bool {
        self == &Self::ARROW
    }

    /// An argument of `0` corresponds to the tuple constructor `(,)`.
    /// Note that the symbols stored for tuple constructors don't
    /// actually include the parentheses and are merely shown for
    /// readability.
    ///
    /// In other words, given a number `extras`, this function will
    /// return the infix identifier with `extras + 1` commas.
    pub fn mk_tuple_commas(extras: usize) -> Self {
        // tuple constructors with 1-10 commas are pre-interned
        let sym = match extras + 1 {
            1 => wy_intern::COMMA_1,
            2 => wy_intern::COMMA_2,
            3 => wy_intern::COMMA_3,
            4 => wy_intern::COMMA_4,
            5 => wy_intern::COMMA_5,
            6 => wy_intern::COMMA_6,
            7 => wy_intern::COMMA_7,
            8 => wy_intern::COMMA_8,
            9 => wy_intern::COMMA_9,
            10 => wy_intern::COMMA_10,
            n => Symbol::from_iter(std::iter::repeat(',').take(n)),
        };
        Self::Infix(sym)
    }

    /// If an identifier's string form consists entirely of commas, then this
    /// returns the number of commas. Otherwise, it returns `None`.
    pub fn comma_count(&self) -> Option<usize> {
        self.symbol().as_str().chars().fold(Some(0), |a, c| {
            a.and_then(|n| if c == ',' { Some(n + 1) } else { None })
        })
    }

    /// Returns a reference to the inner integer value if the identifier is a `Fresh` variant,
    /// otherwise it returns `None`.
    pub fn fresh_val(&self) -> Option<&u32> {
        if let Self::Fresh(n) = self {
            Some(n)
        } else {
            None
        }
    }
}

/// Given an iterator of a type that dereferences to an identifier, returns the highest inner value contained
/// by a `Fresh` variant. If none of the identifiers encountered are `Fresh`
/// variants, then `None` is returned.
pub fn max_fresh_value<I: std::ops::Deref<Target = Ident>>(
    iter: impl IntoIterator<Item = I>,
) -> Option<u32> {
    iter.into_iter()
        .fold(None, |a, c| match (a, c.fresh_val()) {
            (None, v) => v.copied(),
            (Some(a), m @ Some(n)) if *n > a => m.copied(),
            _ => a,
        })
}

pub fn min_fresh_value<I: std::ops::Deref<Target = Ident>>(
    iter: impl IntoIterator<Item = I>,
) -> Option<u32> {
    iter.into_iter()
        .fold(None, |a, c| match (a, c.fresh_val()) {
            (None, v) => v.copied(),
            (Some(a), m @ Some(n)) if *n < a => m.copied(),
            _ => a,
        })
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum IdentKind {
    Upper,
    Lower,
    Infix,
    Label,
    Fresh,
}

impl IdentKind {
    pub fn mk_ident_unchecked(self, s: Symbol) -> Ident {
        match self {
            IdentKind::Upper => Ident::Upper(s),
            IdentKind::Lower => Ident::Lower(s),
            IdentKind::Infix => Ident::Infix(s),
            IdentKind::Label => Ident::Label(s),
            IdentKind::Fresh if s.as_ref().chars().all(|c| c.is_digit(10)) => {
                Ident::Fresh(s.as_str().parse::<u32>().unwrap())
            }
            _ => unreachable!(
                "Fresh identifiers all consist of digit characters, but `{}` does not",
                s
            ),
        }
    }

    pub fn maybe_ident(self, s: Symbol) -> Option<Ident> {
        match self {
            IdentKind::Upper => Some(Ident::Upper(s)),
            IdentKind::Lower => Some(Ident::Lower(s)),
            IdentKind::Infix => Some(Ident::Infix(s)),
            IdentKind::Label => Some(Ident::Label(s)),
            IdentKind::Fresh if s.as_ref().chars().all(|c| c.is_digit(10)) => {
                s.as_str().parse::<u32>().ok().map(Ident::Fresh)
            }
            _ => None,
        }
    }

    pub fn try_to_ident(self, s: Symbol) -> Result<Ident, (Symbol, Self)> {
        match self {
            IdentKind::Upper => Ok(Ident::Upper(s)),
            IdentKind::Lower => Ok(Ident::Lower(s)),
            IdentKind::Infix => Ok(Ident::Infix(s)),
            IdentKind::Label => Ok(Ident::Label(s)),
            IdentKind::Fresh if s.as_ref().chars().all(|c| c.is_digit(10)) => {
                Ok(Ident::Fresh(s.as_str().parse::<u32>().unwrap()))
            }
            kind => Err((s, kind)),
        }
    }
}

pub trait Identifier: Eq {
    fn is_upper(&self) -> bool;
    fn is_lower(&self) -> bool;
    fn is_infix(&self) -> bool;
    fn is_label(&self) -> bool;
    fn is_fresh(&self) -> bool;
    fn get_ident(&self) -> Ident;
    fn ident_constructor(&self) -> fn(Symbol) -> Ident {
        if self.is_upper() {
            Ident::Upper
        } else if self.is_lower() {
            Ident::Lower
        } else if self.is_infix() {
            Ident::Infix
        } else if self.is_label() {
            Ident::Label
        } else {
            |s| Ident::Fresh(s.as_u32())
        }
    }

    fn ident_kind(&self) -> IdentKind {
        if self.is_upper() {
            IdentKind::Upper
        } else if self.is_lower() {
            IdentKind::Lower
        } else if self.is_infix() {
            IdentKind::Infix
        } else if self.is_label() {
            IdentKind::Label
        } else {
            IdentKind::Fresh
        }
    }

    fn map_symbol<X>(&self, f: impl Fn(Symbol) -> X) -> X
    where
        Self: Symbolic,
    {
        self.get_symbol().pure(f)
    }
}

impl Identifier for Ident {
    fn is_upper(&self) -> bool {
        Ident::is_upper(self)
    }
    fn is_lower(&self) -> bool {
        Ident::is_lower(self)
    }
    fn is_infix(&self) -> bool {
        Ident::is_infix(self)
    }
    fn is_label(&self) -> bool {
        Ident::is_label(self)
    }
    fn is_fresh(&self) -> bool {
        Ident::is_fresh(self)
    }
    fn get_ident(&self) -> Ident {
        *self
    }
}
