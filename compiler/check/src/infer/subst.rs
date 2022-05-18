use std::{hash::Hash, ops::Deref};

use wy_common::{Map, Set};
use wy_syntax::{
    ident::Ident,
    tipo::{Tv, Type},
};

pub trait Substitutable {
    fn ftv(&self) -> Set<Tv>;

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized;

    fn apply_once_mut(&mut self, subst: &Subst) -> &mut Self
    where
        Self: Sized,
    {
        *self = self.apply_once(subst);
        self
    }

    fn apply(&self, subst: &Subst) -> Self
    where
        Self: PartialEq + Sized,
    {
        let mut ty = self.apply_once(subst);
        loop {
            let ty2 = ty.apply_once(subst);
            if ty == ty2 {
                break;
            } else {
                ty = ty2;
            }
        }
        ty
    }

    fn apply_mut(&mut self, subst: &Subst) -> &mut Self
    where
        Self: PartialEq + Sized,
    {
        *self = self.apply(subst);
        self
    }

    fn occurs_check(&self, var: Tv) -> bool {
        self.ftv().contains(&var)
    }
}

impl Substitutable for Type<Ident, Tv> {
    fn ftv(&self) -> Set<Tv> {
        match self {
            Type::Var(v) => Set::from([*v]),
            Type::Con(_, ts) => ts.ftv(),
            Type::Fun(x, y) => x.ftv().union(&y.ftv()).copied().collect(),
            Type::Tup(ts) => ts.ftv(),
            Type::Vec(t) => t.ftv(),
            Type::Rec(rec) => rec
                .fields()
                .into_iter()
                .flat_map(|f| f.get_value())
                .flat_map(Substitutable::ftv)
                .collect(),
        }
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        match self {
            Type::Var(n) => match subst.get(n) {
                Some(t) => t.clone(),
                None => Type::Var(*n),
            },
            Type::Con(x, ts) => Type::Con(*x, ts.apply_once(subst)),
            Type::Fun(x, y) => {
                Type::Fun(Box::new(x.apply_once(subst)), Box::new(y.apply_once(subst)))
            }
            Type::Tup(ts) => Type::Tup(ts.apply_once(subst)),
            Type::Vec(t) => Type::Vec(Box::new(t.apply_once(subst))),
            Type::Rec(rec) => Type::Rec(rec.clone().map_t(|t| t.apply_once(subst))),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Subst(Map<Tv, Type<Ident, Tv>>);

impl Subst {
    pub fn new() -> Self {
        Self(Map::new())
    }

    pub fn singleton(var: Tv, typ: Type<Ident, Tv>) -> Self {
        Self(Map::from([(var, typ)]))
    }

    #[inline]
    pub fn get(&self, name: &Tv) -> Option<&Type<Ident, Tv>> {
        self.0.get(name)
    }

    pub fn compose(&self, sub2: &Subst) -> Self {
        sub2.iter()
            .map(|(var, ty)| (*var, ty.apply_once(sub2)))
            .chain(self.0.clone())
            .collect()
    }

    #[inline]
    pub fn iter(&self) -> std::collections::hash_map::Iter<'_, Tv, Type<Ident, Tv>> {
        self.0.iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> std::collections::hash_map::IterMut<'_, Tv, Type<Ident, Tv>> {
        self.0.iter_mut()
    }

    #[inline]
    pub fn into_iter(self) -> std::collections::hash_map::IntoIter<Tv, Type<Ident, Tv>> {
        self.0.into_iter()
    }

    #[inline]
    pub fn remove(&mut self, var: &Tv) -> Option<Type<Ident, Tv>> {
        self.0.remove(var)
    }

    #[inline]
    pub fn remove_many(&mut self, vars: &[Tv]) -> &mut Self {
        for var in vars {
            self.remove(var);
        }
        self
    }
}

impl FromIterator<(Tv, Type<Ident, Tv>)> for Subst {
    #[inline]
    fn from_iter<I: IntoIterator<Item = (Tv, Type<Ident, Tv>)>>(iter: I) -> Self {
        Subst(iter.into_iter().collect::<Map<_, _>>())
    }
}

impl std::fmt::Display for Subst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Subst {{")?;
        let mut br = "";
        match self.0.len() {
            0 => {}
            n => {
                let mut w = self.0.iter().collect::<Vec<_>>();
                w.sort_by_key(|(v, _)| *v);
                let i = if n == 1 {
                    let (v, t) = w[0];
                    write!(f, " [ :{} = {} ] ", v, t)?;
                    1
                } else {
                    br = "\n";
                    0
                };
                for (v, t) in &w[i..] {
                    write!(f, " {}  {} := {} ", br, v, t)?;
                }
            }
        }
        write!(f, "{}}}", br)
    }
}

impl<T> Substitutable for Vec<T>
where
    T: Substitutable,
{
    fn ftv(&self) -> Set<Tv> {
        self.into_iter().flat_map(Substitutable::ftv).collect()
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        self.into_iter().map(|t| t.apply_once(subst)).collect()
    }
}

#[cfg(test)]
mod tests {
    use wy_syntax::ident::Ident;

    use super::*;

    #[test]
    fn test_subst() {
        let prims = &wy_intern::sym::PRIM_TY_NAMES[..];
        let bool_con = Ident::Upper(prims[0]);
        let [foo_con, bar_con, baz] = wy_intern::intern_many(["Foo", "Bar", "Baz"]);
        let subst = Subst::from_iter([
            (
                Tv(0),
                Type::Con(
                    Ident::Upper(foo_con),
                    vec![
                        Type::Vec(Box::new(Type::Con(
                            Ident::Upper(baz),
                            vec![Type::Var(Tv(1))],
                        ))),
                        Type::Var(Tv(2)),
                    ],
                ),
            ),
            (Tv(1), Type::Con(Ident::Upper(prims[1]), vec![])),
            (
                Tv(2),
                Type::Con(
                    Ident::Upper(bar_con),
                    vec![Type::Con(Ident::Upper(prims[8]), vec![Type::Var(Tv(4))])],
                ),
            ),
            (
                Tv(3),
                Type::Con(Ident::Upper(prims[8]), vec![Type::Var(Tv(4))]),
            ),
            (Tv(4), Type::Con(bool_con, vec![])),
        ]);
        println!("{}", &subst);
        let tyy = Type::Fun(
            Box::new(Type::Var(Tv(4))),
            Box::new(Type::Tup(vec![
                Type::Var(Tv(1)),
                Type::Var(Tv(2)),
                Type::Con(Ident::Upper(baz), vec![]),
            ])),
        );
        println!("{}", &tyy);
        println!("applied once: {}", &tyy.apply_once(&subst));
        println!(
            "applied twice: {}",
            tyy.apply_once(&subst).apply_once(&subst)
        );
        println!("applied n times: {}", tyy.apply(&subst));
        let expected = Type::Fun(
            Box::new(Type::Con(bool_con, vec![])),
            Box::new(Type::Tup(vec![
                Type::Con(Ident::Upper(prims[1]), vec![]),
                Type::Con(
                    Ident::Upper(bar_con),
                    vec![Type::Con(
                        Ident::Upper(prims[8]),
                        vec![Type::Con(bool_con, vec![])],
                    )],
                ),
                Type::Con(Ident::Upper(baz), vec![]),
            ])),
        );
        assert_eq!(tyy.apply(&subst), expected)
    }
}
