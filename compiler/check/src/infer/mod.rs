use std::{collections::hash_map::Entry, hash::Hash};

use wy_common::{Map, Set};
pub use wy_syntax::tipo::{Field, Record, Tv, Type as RawType};
use wy_syntax::{ident::Ident, Arity, Tag, Variant};

pub type Type = RawType<Ident, Tv>;

/// Something that implements `Substitutable` is something that:
/// * is parametrized by -- or contains a single variant for -- `Tv`
/// * containes a "Type"
/// * allows for replacement of `Tv`s with `Type` instances based on a map of
///   "substitutions"
///
/// To be `Substitutable`, it is necessary to:
/// * be able to generate a set of all free type variables (`Tv`s)
/// * be able to generate a copy of itself with type variables replaced
///   according to some `Substitution` `{Tv -> Type}`
pub trait Substitutable {
    type Var: Copy + Eq + Hash;
    fn ftv(&self) -> Set<Self::Var>;
    fn apply(&self, subst: &Subst) -> Self;
}

impl<T> Substitutable for Vec<T>
where
    T: Substitutable,
{
    type Var = T::Var;
    fn ftv(&self) -> wy_common::Set<T::Var> {
        self.iter().flat_map(Substitutable::ftv).collect()
    }

    fn apply(&self, subst: &Subst) -> Self {
        self.iter().map(|t| t.apply(subst)).collect()
    }
}

impl Substitutable for Type {
    type Var = Tv;
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
            Type::Vec(t) => Type::Vec(Box::new(t.apply(subst))),
            Type::Rec(rec) => Type::Rec(rec.apply(subst)),
            Type::App(x, y) => Type::App(Box::new(x.apply(subst)), Box::new(y.apply(subst))),
        }
    }
}

impl<T> Substitutable for Record<T>
where
    T: Substitutable,
{
    type Var = T::Var;
    fn ftv(&self) -> Set<T::Var> {
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
    type Var = T::Var;
    fn ftv(&self) -> Set<T::Var> {
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

#[derive(Clone, Debug)]
pub struct Substitution<K, V>(Map<K, V>);
pub type Subst = Substitution<Tv, Type>;

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

#[derive(Clone, Debug)]
pub struct Scheme {
    poly: Vec<Tv>,
    tipo: Type,
}

pub struct Constructor {
    pub name: Ident,
    pub tag: Tag,
    pub arity: Arity,
    pub tipo: Type,
}

pub struct Engine {
    pub count: u32,
    resolved: Map<Ident, Scheme>,
    constructors: Map<Ident, Constructor>,
}

impl Engine {
    pub fn new() -> Self {
        Self {
            count: 0,
            resolved: Map::new(),
            constructors: Map::new(),
        }
    }

    pub fn get_ty(&self, id: &Ident) -> Option<&Scheme> {
        self.resolved.get(id)
    }

    pub fn get_con(&self, id: &Ident) -> Option<&Constructor> {
        self.constructors.get(id)
    }
    pub fn add_con(&mut self, id: Ident, con: Constructor) {
        self.constructors.insert(id, con);
    }

    pub fn tick(&mut self) -> Tv {
        let tv = Tv(self.count);
        self.count += 1;
        tv
    }
}

fn install_bool(engine: &mut Engine) {
    let [ty, tr, fl] = wy_intern::intern_many(["Bool", "True", "False"]);
    let boolean = |ty| Type::Con(Ident::Upper(ty), vec![]);
    engine.resolved.insert(
        Ident::Upper(ty),
        Scheme {
            poly: vec![],
            tipo: boolean(ty),
        },
    );
    for (i, x) in [fl, tr].iter().enumerate() {
        let name = Ident::Upper(*x);
        engine.add_con(
            name,
            Constructor {
                name,
                tag: Tag(i as u32),
                arity: Arity(0),
                tipo: boolean(ty),
            },
        );
    }
}

fn install_option(engine: &mut Engine) {
    let [ty, none, some] = wy_intern::intern_many(["Option", "None", "Some"]);
    let option = |t| Type::Con(Ident::Upper(t), vec![Type::Var(Tv(0))]);
    engine.resolved.insert(
        Ident::Upper(ty),
        Scheme {
            poly: vec![Tv(0)],
            tipo: option(ty),
        },
    );
    engine.add_con(
        Ident::Upper(none),
        Constructor {
            name: Ident::Upper(none),
            tag: Tag(0),
            arity: Arity(0),
            tipo: option(ty),
        },
    );
    engine.add_con(
        Ident::Upper(some),
        Constructor {
            name: Ident::Lower(some),
            tag: Tag(1),
            arity: Arity(1),
            tipo: option(ty),
        },
    );
}

#[cfg(test)]
mod tests {
    use wy_syntax::ident::Ident;

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
