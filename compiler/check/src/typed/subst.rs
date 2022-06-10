use std::collections::hash_map;

use wy_common::{iter::Envr, push_if_absent, Deque, Set};
use wy_syntax::{
    ident::Ident,
    tipo::{Con, Context, Signature, Tv, Ty, Type},
};

pub trait Substitutable {
    fn ftv(&self) -> Set<Tv>;

    fn tv(&self) -> Vec<Tv>;

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

impl Substitutable for Con<Ident, Tv> {
    fn ftv(&self) -> Set<Tv> {
        if let Con::Free(t) = self {
            Set::from([*t])
        } else {
            Set::new()
        }
    }

    fn tv(&self) -> Vec<Tv> {
        if let Con::Free(t) = self {
            vec![*t]
        } else {
            vec![]
        }
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        match self {
            Con::Free(t) => match subst.get(t) {
                Some(ty) => match ty {
                    Type::Con(Con::Data(d), _) => Con::Data(*d),
                    Type::Con(c, _) => *c,
                    Type::Vec(_) => Con::List,
                    Type::Fun(..) => Con::Arrow,
                    Type::Tup(ts) => Con::Tuple(ts.len()),
                    Type::Rec(rec) => rec.ctor().map(|id| Con::Data(*id)).unwrap_or_else(|| *self),
                    _ => Con::Free(*t),
                },
                None => *self,
            },
            con => *con,
        }
    }
}

impl Substitutable for Type<Ident, Tv> {
    fn ftv(&self) -> Set<Tv> {
        match self {
            Type::Var(v) => Set::from([*v]),
            Type::Con(c, ts) => {
                let mut set = c.ftv();
                set.extend(ts.ftv());
                set
            }
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

    fn tv(&self) -> Vec<Tv> {
        self.fv()
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

            Type::Con(con, ts) => match con {
                Con::List if ts.len() == 1 => Type::Vec(Box::new(ts[0].apply_once(subst))),
                Con::Tuple(n) if ts.len() == *n + 1 => Type::Tup(ts.apply_once(subst)),
                Con::Arrow if ts.len() > 1 => ts
                    .apply_once(subst)
                    .into_iter()
                    .reduce(|a, c| Type::Fun(Box::new(a), Box::new(c)))
                    .unwrap(),
                _ => Type::Con(con.apply_once(subst), ts.apply_once(subst)),
            },

            Type::Fun(x, y) => Type::Fun(x.apply_once(subst), y.apply_once(subst)),
            Type::Tup(ts) => Type::Tup(ts.apply_once(subst)),
            Type::Vec(t) => Type::Vec(t.apply_once(subst)),
            Type::Rec(rec) => Type::Rec(rec.map_t_ref(|t| t.apply_once(subst))),
        }
    }
}

impl Substitutable for Ty<Ident> {
    fn ftv(&self) -> Set<Tv> {
        match self {
            Ty::Var(tv) => Set::from([*tv]),
            Ty::Con(con, args) => con
                .get_var()
                .copied()
                .into_iter()
                .chain(args.ftv())
                .collect(),
            Ty::App(xy) => {
                let [x, y] = xy.as_ref();
                x.ftv().into_iter().chain(y.ftv()).collect()
            }
        }
    }

    fn tv(&self) -> Vec<Tv> {
        match self {
            Ty::Var(tv) => vec![*tv],
            Ty::Con(con, args) => args
                .into_iter()
                .cloned()
                .flat_map(|ty| ty.tv())
                .fold(con.tv(), push_if_absent),
            Ty::App(xy) => {
                let [x, y] = xy.as_ref();
                y.tv().into_iter().fold(x.tv(), |mut acc, c| {
                    if !acc.contains(&c) {
                        acc.push(c);
                    }
                    acc
                })
            }
        }
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        match self {
            Ty::Var(v) => match subst.get(v) {
                Some(ty) => ty.simplify_ty(),
                None => Ty::Var(*v),
            },
            Ty::Con(con, args) => Ty::Con(con.apply_once(subst), args.apply_once(subst)),
            Ty::App(xy) => {
                let [x, y] = xy.as_ref();
                Ty::App(Box::new([x.apply_once(subst), y.apply_once(subst)]))
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Subst(Envr<Tv, Type<Ident, Tv>>);

impl Subst {
    pub fn new() -> Self {
        Self(Envr::new())
    }

    pub fn clear(&mut self) {
        self.0.clear()
    }

    pub fn singleton(var: Tv, typ: Type<Ident, Tv>) -> Self {
        Self(Envr::from([(var, typ)]))
    }

    #[inline]
    pub fn get(&self, name: &Tv) -> Option<&Type<Ident, Tv>> {
        self.0.get(name)
    }

    pub fn compose(&self, sub2: &Subst) -> Self {
        sub2.iter()
            .map(|(var, ty)| (*var, ty.apply(sub2)))
            .chain(self.0.store.clone())
            .collect()
    }

    pub fn merge(&self, other: &Self) -> Option<Self> {
        if self
            .iter()
            .filter_map(|(tv, _)| other.get(tv).map(|_| tv))
            .all(|tv| {
                let ty = tv.as_type();
                ty.apply(self) == ty.apply(other)
            })
        {
            Some(
                self.clone()
                    .into_iter()
                    .chain(other.clone().into_iter())
                    .collect(),
            )
        } else {
            None
        }
    }

    pub fn r#match(left: &Type<Ident, Tv>, right: &Type<Ident, Tv>) -> Option<Self> {
        match (left, right) {
            (Type::Fun(a, b), Type::Fun(c, d)) => {
                let u = Self::r#match(a.as_ref(), c.as_ref());
                let v = Self::r#match(b.as_ref(), d.as_ref());
                u.zip(v).and_then(|(ref sl, ref sr)| sl.merge(sr))
            }
            (Type::Var(u), t) => todo!(),
            _ => todo!(),
        }
    }

    #[inline]
    pub fn iter(&self) -> hash_map::Iter<'_, Tv, Type<Ident, Tv>> {
        self.0.iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> hash_map::IterMut<'_, Tv, Type<Ident, Tv>> {
        self.0.iter_mut()
    }

    #[inline]
    pub fn into_iter(self) -> hash_map::IntoIter<Tv, Type<Ident, Tv>> {
        self.0.store.into_iter()
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
        Subst(iter.into_iter().collect::<Envr<_, _>>())
    }
}

impl From<()> for Subst {
    fn from(_: ()) -> Self {
        Subst::new()
    }
}

impl<I> From<Option<I>> for Subst
where
    Subst: From<I>,
{
    fn from(it: Option<I>) -> Self {
        if let Some(it) = it {
            it.into()
        } else {
            Self::new()
        }
    }
}

impl<const N: usize> From<[(Tv, Type<Ident, Tv>); N]> for Subst {
    fn from(kvs: [(Tv, Type<Ident, Tv>); N]) -> Self {
        Subst(Envr::from(kvs))
    }
}

impl From<(Tv, Vec<Type<Ident, Tv>>)> for Subst {
    fn from((tv, tys): (Tv, Vec<Type<Ident, Tv>>)) -> Self {
        tys.into_iter().map(|t| (tv, t)).collect()
    }
}

impl From<(Tv, Deque<Type<Ident, Tv>>)> for Subst {
    fn from((tv, tys): (Tv, Deque<Type<Ident, Tv>>)) -> Self {
        tys.into_iter().map(|t| (tv, t)).collect()
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
                    write!(f, " [ {} := {} ] ", v, t)?;
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

    fn tv(&self) -> Vec<Tv> {
        todo!()
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        self.into_iter().map(|t| t.apply_once(subst)).collect()
    }
}

impl<T> Substitutable for Deque<T>
where
    T: Substitutable,
{
    fn ftv(&self) -> Set<Tv> {
        self.into_iter().flat_map(Substitutable::ftv).collect()
    }

    fn tv(&self) -> Vec<Tv> {
        todo!()
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        self.into_iter().map(|t| t.apply_once(subst)).collect()
    }
}

impl<T> Substitutable for Box<T>
where
    T: Substitutable,
{
    fn ftv(&self) -> Set<Tv> {
        self.as_ref().ftv()
    }

    fn tv(&self) -> Vec<Tv> {
        todo!()
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        Box::new(self.as_ref().apply_once(subst))
    }
}

impl Substitutable for Signature<Ident, Tv> {
    fn ftv(&self) -> Set<Tv> {
        self.ctxt_iter()
            .map(|ctx| ctx.tyvar)
            .chain(self.tipo.ftv())
            .chain(self.each_iter().copied())
            .collect()
    }

    fn tv(&self) -> Vec<Tv> {
        let vs = self.ctxt_iter().map(|ctx| ctx.tyvar).collect();
        self.tipo.tv().into_iter().fold(vs, push_if_absent)
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        Signature {
            each: self.each.clone(),
            ctxt: self.ctxt.clone(),
            tipo: self.tipo.apply_once(subst),
        }
    }
}

// impl<T, const N: usize> Substitutable for [T; N]
// where
//     T: Substitutable,
// {
//     fn ftv(&self) -> Set<Tv> {
//         let mut fvs = Set::new();
//         for t in self {
//             fvs.extend(t.ftv());
//         }
//         fvs
//     }

//     fn apply_once(&self, subst: &Subst) -> Self
//     where
//         Self: Sized,
//     {
//         // TODO: confirm safety? but this should be fine since it's not &T
//         // or &mut T.
//         let mut arr: [T; N] = unsafe { std::mem::zeroed() };
//         let mut i = 0;
//         for t in self {
//             arr[i] = t.apply_once(subst);
//             i += 1;
//         }
//         arr
//     }
// }

#[cfg(test)]
mod tests {
    use wy_intern::symbol;
    use wy_syntax::{ident::Ident, tipo::Con};

    use super::*;

    #[test]
    fn test_subst() {
        let [_bool, _byte, _char, _double, _float, _int, _io, _nat, _str] = [
            *symbol::reserved::BOOL,
            *symbol::reserved::BYTE,
            *symbol::reserved::CHAR,
            *symbol::reserved::DOUBLE,
            *symbol::reserved::FLOAT,
            *symbol::reserved::INT,
            *symbol::reserved::IO,
            *symbol::reserved::NAT,
            *symbol::reserved::STR,
        ];
        let bool_con = Con::Data(Ident::Upper(_bool));
        let conup = |sym| Con::Data(Ident::Upper(sym));
        let [foo_con, bar_con, baz] = wy_intern::intern_many(["Foo", "Bar", "Baz"]);
        let subst = Subst::from_iter([
            (
                Tv(0),
                Type::Con(
                    conup(foo_con),
                    vec![
                        Type::Vec(Box::new(Type::Con(conup(baz), vec![Type::Var(Tv(1))]))),
                        Type::Var(Tv(2)),
                    ],
                ),
            ),
            (Tv(1), Type::Con(conup(_int), vec![])),
            (
                Tv(2),
                Type::Con(
                    conup(bar_con),
                    vec![Type::Con(conup(_io), vec![Type::Var(Tv(4))])],
                ),
            ),
            (Tv(3), Type::Con(conup(_io), vec![Type::Var(Tv(4))])),
            (Tv(4), Type::Con(bool_con, vec![])),
        ]);
        println!("{}", &subst);
        let tyy = Type::Fun(
            Box::new(Type::Var(Tv(4))),
            Box::new(Type::Tup(vec![
                Type::Var(Tv(1)),
                Type::Var(Tv(2)),
                Type::Con(conup(baz), vec![]),
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
                Type::Con(conup(_int), vec![]),
                Type::Con(
                    conup(bar_con),
                    vec![Type::Con(conup(_io), vec![Type::Con(bool_con, vec![])])],
                ),
                Type::Con(conup(baz), vec![]),
            ])),
        );
        assert_eq!(tyy.apply(&subst), expected)
    }
}
