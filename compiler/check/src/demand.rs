use std::fmt::Write;

use wy_common::variant_preds;

//------ DEMAND / STRICTNESS
///
/// ```text
///        Lazy
///          |
///     Head-strict
///      /       \
///   Call       Product
///      \       /
///     Hyper-strict
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Strictness {
    /// Top of the lattice
    Lazy,
    Strict(Demand),
}

variant_preds! { Strictness
    | is_lazy => Lazy
    | is_strict => Strict (_)
    | is_hyper => Strict(Demand::Hyper)
    | is_head => Strict(Demand::Head)
    | is_call => Strict(Demand::Call(_))
    | is_product => Strict(Demand::Product(_))
}

impl std::fmt::Display for Strictness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Strictness::Lazy => write!(f, "L"),
            Strictness::Strict(s) => write!(f, "{}", s),
        }
    }
}

impl Strictness {
    pub const BOTTOM: Self = Self::Strict(Demand::Hyper);
    pub const TOP: Self = Self::Lazy;

    pub fn lub(self, other: Self) -> Self {
        match (self, other) {
            (a @ Self::Lazy, _) | (_, a @ Self::Lazy) => a,
            (Self::Strict(s1), Self::Strict(s2)) => Self::Strict(s1.lub(s2)),
        }
    }
    pub fn both(self, other: Self) -> Self {
        match (self, other) {
            (Self::Lazy, s) | (s, Self::Lazy) => s,
            (Self::Strict(s1), Self::Strict(s2)) => Self::Strict(s1.both(s2)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Demand {
    /// Hyper-strict; bottom of the strictness lattice
    Hyper,
    /// Head-strict; used for values of all types
    Head,
    /// Call-demand; used for values of function type
    Call(Box<Self>),
    /// Product-demand; used for values of product type
    /// note: the following must **always** hold:
    /// * not all components are `Hyper` (use `Hyper`)
    /// * not all components are `Lazy` (use `Head`)
    Product(Vec<Strictness>),
}

variant_preds! { Demand
    | is_hyper => Hyper
    | is_head => Head
    | is_call => Call (_)
    | is_product => Product (_)
}

impl Demand {
    pub fn make_call(self) -> Self {
        match self {
            Demand::Hyper => Self::Hyper,
            demand => Self::Call(Box::new(demand)),
        }
    }

    pub fn make_product(strictnesses: impl IntoIterator<Item = Strictness>) -> Self {
        let mut iter = strictnesses.into_iter();
        if iter.any(|s| s.is_hyper()) {
            Self::Hyper
        } else if iter.all(|s| s.is_lazy()) {
            Self::Head
        } else {
            Self::Product(iter.collect::<Vec<_>>())
        }
    }

    pub fn lub(self, other: Self) -> Self {
        use Demand::*;
        match (self, other) {
            // Hyper on left takes precedence
            (Hyper, s) => s,

            (d @ Head, _)
            | (d @ (Call(_) | Product(_)), Hyper)
            | (Call(_) | Product(_), d @ Head) => d,

            (Call(s1), Call(s2)) => Call(Box::new(s1.lub(*s2))),

            (Product(s1), Product(s2)) if s1.len() == s2.len() => {
                Self::make_product(s1.into_iter().zip(s2).map(|(s1, s2)| s1.lub(s2)))
            }
            (Call(_), Product(_)) | (Product(_), Call(_) | Product(_)) => Head,
        }
    }

    pub fn both(self, other: Self) -> Self {
        use Demand::*;
        match (self, other) {
            (Head, s) | (s @ Product(_), Head) => s,

            (Product(s1), Product(s2)) if s1.len() == s2.len() => {
                Self::make_product(s1.into_iter().zip(s2).map(|(s1, s2)| s1.both(s2)))
            }

            (Hyper, _)
            | (Call(_), Hyper | Product(_))
            | (Product(_), Hyper | Call(_) | Product(_)) => Hyper,

            (s @ Call(_), Head) => s,

            (Call(s1), Call(s2)) => Call(Box::new(s1.both(*s2))),
        }
    }
}

impl std::fmt::Display for Demand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Demand::Hyper => f.write_char('H'),
            Demand::Head => f.write_char('S'),
            Demand::Call(d) => write!(f, "C({})", d),
            Demand::Product(ss) => {
                write!(f, "S(")?;
                for s in ss {
                    write!(f, "{}", s)?;
                }
                write!(f, ")")
            }
        }
    }
}
