use wy_syntax::tipo::Tv;

use super::{
    constraint::{Constraint, ConstraintBuilder, Type},
    error::Error,
    subst::{Subst, Substitutable},
};

// pub trait Unify {
//     fn unifier(&self) -> &Unifier;

//     fn unifier_mut(&mut self) -> &mut Unifier;

//     fn unify(&mut self, t1: Type, t2: Type) -> Result<Subst, Error> {
//         self.unifier_mut().unify(t1, t2)
//     }

//     fn unify_zipped(&mut self, xys: impl Iterator<Item = (Type, Type)>) -> Result<Subst, Error> {
//         self.unifier_mut().unify_zipped(xys)
//     }

//     fn unify_many(
//         &mut self,
//         t1s: impl IntoIterator<Item = Type>,
//         t2s: impl IntoIterator<Item = Type>,
//     ) -> Result<Subst, Error> {
//         self.unifier_mut().unify_many(t1s, t2s)
//     }

//     fn bind(&mut self, var: Tv, tipo: Type) -> Result<Subst, Error> {
//         self.unifier_mut().bind(var, tipo)
//     }
// }

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Bound {
    /// When a type variable representative `var` is bound to a type variable
    /// `Type` variant, i.e., `Tv(x) == Type::Var(Tv(x))` for some `x`.
    Trivial(Tv),
    /// A variable binding to a non-trivial type
    NonTrivial(Tv),
}

impl Bound {
    pub fn contains(&self, var: &Tv) -> bool {
        matches!(self, Self::Trivial(tv) | Self::NonTrivial(tv) if tv == var)
    }
}

#[derive(Clone, Debug)]
pub struct Unifier {
    pub subst: Subst,
    pub constraints: Vec<Constraint>,
    pub bound: Vec<Bound>,
}

impl Unifier {
    pub fn new() -> Self {
        Self {
            subst: Subst::new(),
            constraints: vec![],
            bound: vec![],
        }
    }

    pub fn new_with(subst: Subst, constraints: Vec<Constraint>) -> Self {
        Self {
            subst,
            constraints,
            bound: vec![],
        }
    }

    pub fn clear(&mut self) {
        self.subst = Subst::new();
        self.constraints.clear();
        self.bound.clear();
    }

    pub fn clear_subst(&mut self) {
        self.subst.clear()
    }

    pub fn clear_constraints(&mut self) {
        self.constraints.clear()
    }

    pub fn clear_bound(&mut self) {
        self.bound.clear()
    }

    pub fn constraint_builder(&mut self) -> ConstraintBuilder {
        ConstraintBuilder::new()
    }

    pub fn add_constraint(&mut self, constraint: Constraint) {
        if !self.constraints.contains(&constraint) {
            self.constraints.push(constraint);
        }
    }

    pub fn add_constraints<I>(&mut self, constraints: I)
    where
        I: IntoIterator<Item = Constraint>,
    {
        constraints.into_iter().for_each(|constraint| {
            self.add_constraint(constraint);
        })
    }

    pub fn get_subst(&self) -> &Subst {
        &self.subst
    }

    pub fn get_subst_mut(&mut self) -> &mut Subst {
        &mut self.subst
    }

    pub fn unify(&mut self, t1: Type, t2: Type) -> Result<Subst, Error> {
        let empty = Subst::new();
        match (t1, t2) {
            (x, y) if x == y => Ok(empty),
            (Type::Var(var), tipo) | (tipo, Type::Var(var)) => self.bind(var, tipo),
            (Type::Con(cx, xs), Type::Con(cy, ys)) if cx == cy => {
                if xs.len() == ys.len() {
                    self.unify_zipped(xs.into_iter().zip(ys))
                } else {
                    Err(Error::ArityMismatch {
                        left: (cx, xs),
                        right: (cy, ys),
                    })
                }
            }
            (Type::Fun(x1, y1), Type::Fun(x2, y2)) => {
                let s1 = self.unify(*x1, *x2)?;
                let s2 = self.unify(*y1.apply(&s1), *y2.apply(&s1))?;
                Ok(s2.compose(&s1))
            }
            (Type::Tup(xs), Type::Tup(ys)) if xs.len() == ys.len() => {
                self.unify_zipped(xs.into_iter().zip(ys))
            }
            (x, y) => Err(Error::Mismatch(x, y)),
        }
    }

    pub fn unify_zipped(
        &mut self,
        xys: impl Iterator<Item = (Type, Type)>,
    ) -> Result<Subst, Error> {
        xys.fold(Ok(Subst::new()), |a, (tx, ty)| {
            a.and_then(|ref s1| {
                self.unify(tx.apply(s1), ty.apply(s1))
                    .map(|ref s2| s1.compose(s2))
            })
        })
    }

    pub fn unify_many(
        &mut self,
        t1s: impl IntoIterator<Item = Type>,
        t2s: impl IntoIterator<Item = Type>,
    ) -> Result<Subst, Error> {
        t1s.into_iter()
            .zip(t2s.into_iter())
            .fold(Ok(Subst::new()), |a, (tx, ty)| {
                a.and_then(|ref s1| {
                    self.unify(tx.apply(s1), ty.apply(s1))
                        .map(|ref s2| s1.compose(s2))
                })
            })
    }

    pub fn add_bound(&mut self, bound: Bound) {
        if !self.bound.contains(&bound) {
            self.bound.push(bound);
        }
    }

    pub fn bind(&mut self, var: Tv, tipo: Type) -> Result<Subst, Error> {
        if tipo.occurs_check(var) {
            Err(Error::Infinite(tipo, Type::Var(var)))
        } else {
            match tipo {
                Type::Var(tv) if var == tv => {
                    self.add_bound(Bound::Trivial(tv));
                    Ok(Subst::new())
                }
                _ => {
                    self.add_bound(Bound::NonTrivial(var));
                    Ok(Subst::singleton(var, tipo))
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use wy_syntax::Ty;

    use super::*;

    #[test]
    fn test_unify() {
        let fun_a_bool = Type::mk_fun(Tv(0).as_type(), Type::mk_fun(Tv(1).as_type(), Type::BOOL));
        let fun_int_bool = Type::mk_fun(Type::INT, Type::mk_fun(Type::STR, Type::BOOL));
        let mut uni = Unifier::new();
        let fun123 = Ty! { 0 -> #(Hi 3 4) -> (1 -> 2) };
        println!("#0 -> () -> (#1 -> #2) <=> {}", fun123);
        uni.add_constraints([
            Constraint::Join(Tv(0).as_type(), Tv(1).as_type()),
            Constraint::Join(Tv(1).as_type(), Type::CHAR),
            Constraint::Join(
                Type::mk_tuple([Tv(2).as_type(), Tv(3).as_type()]),
                Type::mk_tuple([Type::CHAR, Type::BYTE]),
            ),
        ]);
        println!("unifying `{}` with `{}`", &fun_a_bool, &fun_int_bool);
        let sub = uni.unify(fun_a_bool, fun_int_bool);
        match sub {
            Ok(sub) => {
                println!("{}", &sub);
            }
            Err(e) => eprintln!("{}", e),
        }
    }
}
