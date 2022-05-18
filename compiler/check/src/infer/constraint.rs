use wy_common::Set;
use wy_syntax::{
    ident::Ident,
    tipo::{Tv, Type as Type_},
};

use super::subst::{Subst, Substitutable};

pub type Type = Type_<Ident, Tv>;

#[derive(Clone, Debug, PartialEq, Eq)]
/// A `Scheme` represents a *sigma* type or a *type scheme*. It carries a `Type`
/// ("tau") value as well as a list of *type variables*, and represents a type
/// that is potentially quantified over its outermost type variables.
///
/// ---
/// * a __monotype__ `mu` is a type containing no type variables
/// * a __type scheme__ `sigma` may be interpreted in the following
///   syntactically distinct (but semantically equivalent) forms:
///     - `forall a_1 . forall a_2 ... forall a_n tau`
///     - `forall a_1 ... a_n . tau`
///   where `tau` is a *type* and the `a_i`s are *generic type variables*
/// * if `S` is a substitution of types for type variables, written
///   `[tau_1/alpha_1, ..., tau_n/alpha_n]` or simply `[tau_i/alpha_i]_i` and
///   `sigma` is a type-scheme, then `S sigma` is the type-scheme obtained by
///   replacing each *free occurence* of `alpha_i` in `sigma` by `tau_i`,
///   renaming the generic variables of `sigma` if necessary, THEN `S sigma` is
///   called an __instance__ of `sigma`.
/// * a type scheme `sigma = forall a_1 ... a_n . tau` has a __generic
///   instance__ of `sigma' = forall b_1 ... b_n . tau'` if `tau' =
///   [tau_i/a_i] tau` for some types `tau_1, ..., tau_n` and the `b_j` are not
///   free in `sigma` and we write `sigma > sigma'`
///     - *instantiation* acts on __free__ variables
///     - *generic instantiation* acts on __bound__ variables
/// * `sigma > sigma'` implies `S sigma > S sigma'`
/// * free type variables in an assertion are *implicitly* quantified over the
///   whole assertion, while __explicit quantification__ has restricted scope
///
/// TODO: handle recursion using the polymorphic fixed-point operator `fix ::
/// forall a . (a -> a) -> a
pub struct Scheme {
    pub tipo: Type,
    pub poly: Vec<Tv>,
}

impl Scheme {
    pub fn monotype(tipo: Type) -> Self {
        Self { poly: vec![], tipo }
    }
}

impl Substitutable for Scheme {
    fn ftv(&self) -> Set<Tv> {
        self.tipo
            .ftv()
            .difference(&self.poly.iter().copied().collect())
            .copied()
            .collect()
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        Self {
            poly: self.poly.clone(),
            tipo: self
                .tipo
                .apply_once(&subst.clone().remove_many(self.poly.as_slice())),
        }
    }
}

impl std::fmt::Display for Scheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.poly.is_empty() {
            write!(f, "{}", &self.tipo)
        } else {
            write!(f, "forall ")?;
            for tv in &self.poly {
                write!(f, "{} ", tv)?;
            }
            write!(f, ". {}", &self.tipo)
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Constraint {
    Is(Type, Type),
}

impl Substitutable for Constraint {
    fn ftv(&self) -> wy_common::Set<Tv> {
        match self {
            Constraint::Is(t1, t2) => t1.ftv().union(&t2.ftv()).copied().collect(),
        }
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        match self {
            Constraint::Is(t1, t2) => Constraint::Is(t1.apply_once(subst), t2.apply_once(subst)),
        }
    }
}

impl std::fmt::Debug for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self)
    }
}

impl std::fmt::Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constraint::Is(t1, t2) => write!(f, "{} ~ {}", t1, t2),
        }
    }
}
