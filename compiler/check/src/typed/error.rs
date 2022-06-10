use wy_syntax::ident::Ident;

use super::constraint::{Constraint, TyCon, Type};

pub type Inferred<X> = Result<X, Error>;

// #[derive(Debug)]
pub enum Error {
    /// Generic unification failure
    NotUnified(Type, Type),
    /// Unable to unify two types with the same constructor due to arities not
    /// matching
    ArityMismatch {
        left: (TyCon, Vec<Type>),
        right: (TyCon, Vec<Type>),
    },
    /// Emitted when a unification term in function position is not callable
    NotFunc(Type),
    /// Emitted when a variable's type is not bound in the environment
    Unbound(Ident),
    /// Emitted when an infinite type would be constructed, e.g., `a ~ [a]`
    Infinite(Type, Type),
    Mismatch(Type, Type),
    NotInSignature(Type),
    Ambiguous(Vec<Constraint>),
    Custom(Box<dyn std::fmt::Display>),
}

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use wy_common::pretty::Many;
        match self {
            Error::NotUnified(x, y) => write!(f, "unable to unify `{}` and `{}`", x, y),
            Error::ArityMismatch {
                left: (con_l, args_l),
                right: (con_r, args_r),
            } => {
                write!(
                    f,
                    "arity mismatch between\n\t\
                    `{} {}` (arity = {}) \nand\n\t\
                    `{} {}` (arity = {})",
                    con_l,
                    Many(&args_l[..], ' '),
                    args_l.len(),
                    con_r,
                    Many(&args_r[..], ' '),
                    args_r.len()
                )
            }
            Error::NotFunc(ty) => write!(f, "expected function type, but found\n\t`{}`\n", ty),
            Error::Unbound(n) => write!(f, "unbound variable `{}`", n),
            Error::Infinite(a, b) => write!(
                f,
                "occurs check: cannot construct the infinite type `{}` ~ `{}`",
                a, b
            ),
            Error::Mismatch(a, b) => write!(f, "type mismatch within\n\t`{}`\nand\n\t`{}`", a, b),
            Error::NotInSignature(ty) => write!(f, "the type `{}` is not in the signature", ty),
            Error::Ambiguous(cs) => {
                write!(f, "ambiguous constraints:\n")?;
                for c in cs {
                    write!(f, "\t{}\n", c)?;
                }
                Ok(())
            }
            Error::Custom(s) => write!(f, "custom error: {}", s),
        }
    }
}
