use std::{collections::hash_map::Entry, hash::Hash, rc::Rc};

use wy_common::{Map, Set};
pub use wy_syntax::tipo::{Field, Record, Tv, Type};

pub enum Ty {}

pub trait Substitutable {
    fn ftv(&self) -> Set<Tv>;
    fn apply(&self, subst: &Subst) -> Self;
}

impl<T> Substitutable for Vec<T>
where
    T: Substitutable,
{
    fn ftv(&self) -> wy_common::Set<Tv> {
        self.iter().flat_map(Substitutable::ftv).collect()
    }

    fn apply(&self, subst: &Subst) -> Self {
        self.iter().map(|t| t.apply(subst)).collect()
    }
}

impl Substitutable for Type {
    fn ftv(&self) -> Set<Tv> {
        let mut set = Set::new();
        match self {
            Type::Var(tv) => {
                set.insert(*tv);
            }
            Type::Con(_, xs) => set.extend(xs.ftv()),
            Type::Fun(x, y) => {
                set.extend(x.ftv());
                set.extend(y.ftv());
            }
            Type::Tup(xs) => set.extend(xs.ftv()),
            Type::Vec(x) => set.extend(x.ftv()),
            Type::Rec(rec) => {
                for field in rec.fields() {
                    if let Field::Entry(_, ty) = field {
                        set.extend(ty.ftv());
                    }
                }
            }
            Type::App(a, b) => {
                set.extend(a.ftv());
                set.extend(b.ftv())
            }
        };
        set
    }

    fn apply(&self, subst: &Subst) -> Self {
        match self {
            Type::Var(a) => match subst.lookup(a) {
                Some(k) => k.clone(),
                None => Type::Var(*a),
            },
            Type::Con(id, ks) => Type::Con(*id, ks.apply(subst)),
            Type::Fun(x, y) => Type::Fun(Box::new(x.apply(subst)), Box::new(y.apply(subst))),
            Type::Tup(xs) => Type::Tup(xs.apply(subst)),
            Type::Vec(t) => Type::Vec(Rc::new(t.apply(subst))),
            Type::Rec(rec) => Type::Rec(rec.apply(subst)),
            Type::App(x, y) => Type::App(Box::new(x.apply(subst)), Box::new(y.apply(subst))),
        }
    }
}

impl<T> Substitutable for Record<T>
where
    T: Substitutable,
{
    fn ftv(&self) -> Set<Tv> {
        let mut set = Set::new();
        match self {
            Record::Anon(fs) | Record::Data(_, fs) => set.extend(fs.ftv()),
        };
        set
    }

    fn apply(&self, subst: &Subst) -> Self {
        match self {
            Record::Anon(fs) => Record::Anon(fs.apply(subst)),
            Record::Data(k, fs) => Record::Data(*k, fs.apply(subst)),
        }
    }
}

impl<T> Substitutable for Field<T>
where
    T: Substitutable,
{
    fn ftv(&self) -> Set<Tv> {
        let mut set = Set::new();
        match self {
            Field::Entry(_, t) => set.extend(t.ftv()),
            _ => (),
        };
        set
    }

    fn apply(&self, subst: &Subst) -> Self {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => Field::Key(*k),
            Field::Entry(k, ty) => Field::Entry(*k, ty.apply(subst)),
        }
    }
}

pub type Subst = Substitution<Tv, Type>;
pub struct Substitution<K, V>(Map<K, V>);

impl<K, V> Substitution<K, V>
where
    K: Eq + Hash,
{
    pub fn empty() -> Self {
        Self(Map::new())
    }

    pub fn lookup(&self, k: &K) -> Option<&V> {
        self.0.get(k)
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.0.insert(k, v)
    }

    pub fn entry(&mut self, k: K) -> Entry<K, V> {
        self.0.entry(k)
    }

    pub fn difference(&self, other: &Self) -> Substitution<&K, &V> {
        self.0
            .iter()
            .filter(|(k, _)| other.0.contains_key(*k))
            .collect()
    }

    pub fn union<'a, 'b: 'a>(&'a self, other: &'b Self) -> Substitution<&K, &V> {
        let mut map = Map::new();
        for (k, v) in &other.0 {
            map.insert(k, v);
        }
        for (k, v) in &self.0 {
            map.insert(k, v);
        }
        Substitution(map)
    }
}

impl<K, V> AsRef<Map<K, V>> for Substitution<K, V> {
    fn as_ref(&self) -> &Map<K, V> {
        &(self.0)
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for Substitution<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Self(iter.into_iter().collect::<Map<_, _>>())
    }
}

#[cfg(test)]
mod tests {
    use wy_syntax::Ident;

    use super::*;

    #[test]
    fn it_works() {
        let typ = Type::Fun(Box::new(Type::Var(Tv(0))), Box::new(Type::Var(Tv(1))));
        let result = typ.ftv();
        assert!(result.contains(&Tv(0)));
        assert!(result.contains(&Tv(1)));
        let mut subst = Subst::empty();
        let boolcon = Ident::Upper(wy_intern::symbol::intern_once("Bool"));
        subst.insert(Tv(0), Type::Con(boolcon, vec![]));
        let t2 = typ.apply(&subst);
        println!("{}", t2)
    }
}
