use std::{fmt::Write, hash::Hash};

use wy_common::{Map, Mappable};
use wy_intern::{Symbol, Symbolic};

use crate::ident::Ident;

/// Represents a type variable.
///
/// TODO: (for display/printing aesthetics) reserve `Tv(6)` and `Tv(13)` for `f`
/// and `m`, respectively for type variables in constructor position??? Or put
/// off into a separate type in a later phase.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Tv(pub u32);

impl Tv {
    pub fn tick(&self) -> Self {
        Self(self.0 + 1)
    }

    pub fn display(&self) -> String {
        wy_common::text::display_var(self.0)
    }

    pub fn from_symbol(sym: Symbol) -> Self {
        Tv(sym.as_u32())
    }

    /// Lossfully coerces an identifier into a type variable.
    pub fn from_ident(ident: Ident) -> Self {
        Tv(ident.as_u32())
    }
}

impl From<Tv> for usize {
    fn from(tv: Tv) -> Self {
        tv.0 as usize
    }
}

impl PartialEq<Ident> for Tv {
    fn eq(&self, other: &Ident) -> bool {
        matches!(other, Ident::Fresh(n) if n.as_u32() == self.0)
    }
}

impl PartialEq<Tv> for Ident {
    fn eq(&self, other: &Tv) -> bool {
        matches!(self, Ident::Fresh(s) if s.as_u32() == other.0)
    }
}

impl<S> From<S> for Tv
where
    S: Symbolic,
{
    fn from(s: S) -> Self {
        Tv(s.get_symbol().as_u32())
    }
}

impl From<&Ident> for Tv {
    fn from(id: &Ident) -> Self {
        Tv(id.as_u32())
    }
}

impl std::fmt::Debug for Tv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Tv({})", self.0)
    }
}

impl std::fmt::Display for Tv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display())
    }
}

impl From<Tv> for Ident {
    fn from(tv: Tv) -> Self {
        Ident::Fresh(wy_intern::intern_once(&*tv.display()))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var<Id>(Id, Tv);
impl<Id> Var<Id> {
    pub fn new(id: Id) -> Var<Id> {
        Var(id, Tv(0))
    }

    pub fn from_pair((id, tv): (Id, Tv)) -> Self {
        Self(id, tv)
    }

    pub fn from_iter(iter: impl Iterator<Item = Id>) -> impl Iterator<Item = Var<Id>> {
        iter.zip(0u32..).map(|(id, n)| Var(id, Tv(n)))
    }

    pub fn from_enumerated(
        iter: impl Iterator<Item = (usize, Id)>,
    ) -> impl Iterator<Item = Var<Id>> {
        iter.map(|(k, id)| Var(id, Tv(k as u32)))
    }

    #[inline]
    pub fn id(self) -> Id {
        self.0
    }

    #[inline]
    pub fn tv(&self) -> Tv {
        self.1
    }

    pub fn as_pair(self) -> (Id, Tv) {
        (self.0, self.1)
    }

    pub fn map<X>(self, mut f: impl FnMut(Id) -> X) -> Var<X> {
        Var(f(self.0), self.1)
    }

    pub fn map_ref<X>(&self, mut f: impl FnMut(&Id) -> X) -> Var<X> {
        Var(f(&self.0), self.1)
    }

    pub fn with_ref(&self) -> Var<&Id> {
        Var(&self.0, self.1)
    }

    pub fn replace_var(&mut self, tv: Tv) -> Tv {
        std::mem::replace(&mut self.1, tv)
    }

    pub fn replace_id(&mut self, id: Id) -> Id {
        std::mem::replace(&mut self.0, id)
    }
}
impl<Id: std::fmt::Debug> std::fmt::Debug for Var<Id> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Var({:?}, {})", &self.0, &self.1)
    }
}
impl<Id: std::fmt::Display> std::fmt::Display for Var<Id> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.[{}]", &self.0, &self.1)
    }
}

impl<T> Extend<Var<T>> for Map<T, Tv>
where
    T: Eq + Hash,
{
    fn extend<I: IntoIterator<Item = Var<T>>>(&mut self, iter: I) {
        for Var(t, tv) in iter {
            self.insert(t, tv);
        }
    }
}

impl<T> Extend<Var<T>> for Vec<(T, Tv)> {
    fn extend<I: IntoIterator<Item = Var<T>>>(&mut self, iter: I) {
        for Var(t, tv) in iter {
            self.push((t, tv));
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Con<Id = Ident, T = Id> {
    List,
    Tuple(usize),
    Arrow,
    Data(Id),
    Free(T),
}

impl<Id, T> Con<Id, T> {
    pub fn is_list(&self) -> bool {
        matches!(self, Con::List)
    }
    pub fn is_tuple(&self) -> bool {
        matches!(self, Con::Tuple(..))
    }
    pub fn is_arrow(&self) -> bool {
        matches!(self, Con::Arrow)
    }
    pub fn is_data(&self) -> bool {
        matches!(self, Con::Data(..))
    }
    pub fn is_variable(&self) -> bool {
        matches!(self, Con::Free(..))
    }
    /// Since `Type` is generic over identifiers, in order to extract the
    /// identifier used for the (polymorphic) list constructor `:` -- which, as
    /// a result of string interning, is represented by a `Symbol` -- a closure
    /// must be provided to convert the `Symbol` corresponding to `:` into the
    /// type used to represent identifiers.
    ///
    /// Note that, while `(:)` is formally written, the actual identifier does
    /// *not* include the parentheses! Hence this function is essentially a
    /// shortcut to interning `:` and mapping it to represent an identifier.
    pub fn list_cons_id(mut f: impl FnMut(Symbol) -> Id) -> Id {
        f(*wy_intern::CONS)
    }

    /// Like with the list constructor `:`, the tuple constructor must also be
    /// processed to match the type used to represent identifiers. However,
    /// unlike the list constructor, which is used for *all* lists, tuples
    /// require a new constructor depending on the number of type components
    /// held. Namely, the constructor for a tuple with `N` elements is the
    /// lexeme formed by combining `N - 1` commas and surrounding them in
    /// parentheses.
    pub fn n_tuple_id(commas: usize, mut f: impl FnMut(Symbol) -> Id) -> Id {
        f(wy_intern::intern_once(
            &*(1..(2 + commas)).map(|_| ',').collect::<String>(),
        ))
    }

    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> Con<X, T> {
        match self {
            Con::List => Con::List,
            Con::Tuple(n) => Con::Tuple(n),
            Con::Arrow => Con::Arrow,
            Con::Data(id) => Con::Data(f(id)),
            Con::Free(t) => Con::Free(t),
        }
    }
    pub fn map_id_ref<X>(&self, mut f: impl FnMut(&Id) -> X) -> Con<X, T>
    where
        T: Copy,
    {
        match self {
            Con::List => Con::List,
            Con::Tuple(n) => Con::Tuple(*n),
            Con::Arrow => Con::Arrow,
            Con::Data(id) => Con::Data(f(id)),
            Con::Free(t) => Con::Free(*t),
        }
    }

    pub fn map_t<X>(self, mut f: impl FnMut(T) -> X) -> Con<Id, X> {
        match self {
            Con::List => Con::List,
            Con::Tuple(n) => Con::Tuple(n),
            Con::Arrow => Con::Arrow,
            Con::Data(id) => Con::Data(id),
            Con::Free(t) => Con::Free(f(t)),
        }
    }
    pub fn map_t_ref<X>(&self, mut f: impl FnMut(&T) -> X) -> Con<Id, X>
    where
        Id: Copy,
    {
        match self {
            Con::List => Con::List,
            Con::Tuple(n) => Con::Tuple(*n),
            Con::Arrow => Con::Arrow,
            Con::Data(id) => Con::Data(*id),
            Con::Free(t) => Con::Free(f(t)),
        }
    }
}

impl<Id: std::fmt::Display, T: std::fmt::Display> std::fmt::Display for Con<Id, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Con::List => write!(f, "[]"),
            Con::Tuple(ns) => {
                f.write_char('(')?;
                for _ in 0..(*ns + 1) {
                    f.write_char(',')?;
                }
                f.write_char(')')
            }
            Con::Arrow => f.write_str("(->)"),
            Con::Data(id) => write!(f, "{}", id),
            Con::Free(v) => write!(f, "{}", v),
        }
    }
}

/// Types corresponding to syntactic forms. A number of variants are effectively
/// syntactic sugar for type applications over a type constructor, represented
/// by the variant `Con`:
/// * `(a, b)` desugars into `(,) a b`
///     - `(a, b, c)` desugars into `(,,) a b c`
///     - a tuple type with *n* components is the product type of the *n-tuple*
///       constructor (written as `n - 1` commas surrounded by parentheses)
/// * `a -> b` desugars into `(->) a b`
/// * `[a]` desugars into `(:) a` The above desugared forms correspond to the
/// `Con` variant. Note: this does not hold for record types!
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type<Id = Ident, Ty = Id> {
    /// Type variables. These use their own special inner type `Tv`, which is a
    /// newtype wrapper around a `u32`.
    Var(Ty),
    /// Type constructors. Note that a `Con` variant may NOT have a type
    /// variable as the cosnstructor. For polymorphism over a constructor, use
    /// the `App` variant.
    Con(Con<Id, Ty>, Vec<Type<Id, Ty>>),
    /// Function type. The type `a -> b` describes a function whose argument is
    /// of type `a` and whose return value is of type `b`. Functions are *all*
    /// curried, hence a multi-argument function type is a function type whose
    /// argument type is *also* a function. For example, the type `a -> b -> c`
    /// describes a function whose first argument is of type `a`, second
    /// argument if of type `b` and returns a value of type `c`.
    ///
    /// Function types are sugar for type application of the type constructor
    /// `(->)`, which as an infix is *right* associative. Hence, the type
    /// signature `a -> b -> c` can be syntactically read as `(a -> b) -> c`.
    ///
    /// When an intermediary type in the function chain is itself another
    /// function type, then parentheses are added to prevent ambiguity, as in
    /// the type `a -> (b -> c) -> d`, where the first argument is of type `a`
    /// and the second is of type `b -> c`.
    Fun(Box<Type<Id, Ty>>, Box<Type<Id, Ty>>),
    Tup(Vec<Type<Id, Ty>>),
    Vec(Box<Type<Id, Ty>>),
    Rec(Record<Type<Id, Ty>, Id>),
}

impl<Id: std::fmt::Display, Ty: std::fmt::Display> std::fmt::Display for Type<Id, Ty> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Var(tv) => write!(f, "{}", tv),
            Type::Con(con, args) => {
                if args.is_empty() {
                    write!(f, "{}", con)
                } else {
                    write!(f, "{}", con)?;
                    for arg in args {
                        if arg.is_func() || (arg.is_app() && !arg.is_nullary()) {
                            write!(f, " ({})", arg)?;
                            continue;
                        }
                        write!(f, " {}", arg)?;
                    }
                    Ok(())
                }
            }
            Type::Fun(x, y) => {
                if x.is_func() {
                    write!(f, "({})", x)?;
                } else {
                    write!(f, "{}", x)?;
                }
                write!(f, " -> ")?;
                if y.is_func() {
                    write!(f, "({})", y)
                } else {
                    write!(f, "{}", y)
                }
            }
            Type::Tup(tys) => {
                write!(f, "(")?;
                match tys.as_slice() {
                    [] => {}
                    [a, rest @ ..] => {
                        write!(f, "{}", a)?;
                        for r in rest {
                            write!(f, ", {}", r)?;
                        }
                    }
                };
                write!(f, ")")
            }
            Type::Vec(t) => write!(f, "[{}]", t.as_ref()),
            Type::Rec(rec) => {
                char::fmt(&'{', f)?;
                let filtered = rec
                    .fields()
                    .iter()
                    .filter_map(|field| match field {
                        // for typed records, we should expect both lhs (keys)
                        // and rhs (types)
                        Field::Rest | Field::Key(_) => None,
                        Field::Entry(k, v) => Some((k, v)),
                    })
                    .collect::<Vec<_>>();
                match &filtered[..] {
                    [] => {}
                    [(k, v), rest @ ..] => {
                        write!(f, " {} :: {}", k, v)?;
                        for (k, v) in rest {
                            write!(f, ", {} :: {}", k, v)?;
                        }
                        write!(f, " ")?;
                    }
                };
                char::fmt(&'}', f)
            }
        }
    }
}

impl<Id, Ty> Type<Id, Ty> {
    pub const UNIT: Self = Self::Tup(vec![]);

    pub fn mk_fun(x: Self, y: Self) -> Self {
        Self::Fun(Box::new(x), Box::new(y))
    }

    pub fn contains_constructor(&self, con: &Con<Id, Ty>) -> bool
    where
        Id: PartialEq,
        Ty: PartialEq,
    {
        match self {
            Type::Var(_) => false,
            Type::Con(c, ts) => c == con || ts.iter().any(|ty| ty.contains_constructor(con)),
            Type::Fun(a, b) => {
                con.is_arrow() || a.contains_constructor(con) || b.contains_constructor(con)
            }
            Type::Tup(ts) => {
                matches!(con, Con::Tuple(n) if *n == ts.len())
                    || ts.iter().any(|ty| ty.contains_constructor(con))
            }
            Type::Vec(t) => {
                if con.is_list() {
                    true
                } else {
                    t.contains_constructor(con)
                }
            }
            Type::Rec(rec) => rec
                .fields()
                .into_iter()
                .any(|field| matches!(field.get_value(), Some(t) if t.contains_constructor(con))),
        }
    }

    /// Identifies whether this `Type` is polymorphic over the given type
    /// variable. Equivalently, this method tests for containment of the given
    /// variable of type `T`.
    pub fn depends_on(&self, var: &Ty) -> bool
    where
        Ty: PartialEq,
    {
        match self {
            Type::Var(t) => var == t,
            Type::Con(_, ts) | Type::Tup(ts) => ts.iter().any(|ty| ty.depends_on(var)),
            Type::Fun(x, y) => x.depends_on(var) || y.depends_on(var),
            Type::Vec(t) => t.depends_on(var),
            Type::Rec(rec) => rec
                .fields()
                .into_iter()
                .any(|field| matches!(field.get_value(), Some(ty) if ty.depends_on(var))),
        }
    }

    /// Tests whether a given type contains another type.
    pub fn contains(&self, subty: &Type<Id, Ty>) -> bool
    where
        Id: PartialEq,
        Ty: PartialEq,
    {
        match self {
            ty @ Type::Var(_) => ty == subty,
            Type::Fun(x, y) => x.contains(subty) || y.contains(subty),
            Type::Con(_, tys) | Type::Tup(tys) => tys.iter().any(|ty| ty.contains(subty)),
            Type::Vec(t) => t.contains(subty),
            Type::Rec(rec) => rec
                .fields()
                .into_iter()
                .any(|field| matches!(field.get_value(), Some(ty) if ty.contains(subty))),
        }
    }

    pub fn map_id<F, X>(self, f: &mut F) -> Type<X, Ty>
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Type::Var(t) => Type::Var(t),
            Type::Con(Con::Data(n), ts) => Type::Con(Con::Data(f(n)), ts.fmap(|ty| ty.map_id(f))),
            Type::Con(id, tys) => Type::Con(
                id.map_id(|i| f(i)),
                tys.into_iter().map(|ty| ty.map_id(f)).collect(),
            ),
            Type::Fun(x, y) => Type::Fun(Box::new(x.map_id(f)), Box::new(y.map_id(f))),
            Type::Tup(ts) => Type::Tup(ts.into_iter().map(|t| t.map_id(f)).collect()),
            Type::Vec(t) => Type::Vec(Box::new(t.map_id(f))),
            Type::Rec(_) => todo!(),
        }
    }

    pub fn map_id_ref<F, X>(&self, f: &mut F) -> Type<X, Ty>
    where
        F: FnMut(&Id) -> X,
        Ty: Copy,
    {
        match self {
            Type::Var(t) => Type::Var(*t),
            Type::Con(id, tys) => Type::Con(
                id.map_id_ref(|id| f(id)),
                tys.iter().map(|ty| ty.map_id_ref(f)).collect(),
            ),
            Type::Fun(x, y) => Type::Fun(Box::new(x.map_id_ref(f)), Box::new(y.map_id_ref(f))),
            Type::Tup(ts) => Type::Tup(ts.iter().map(|t| t.map_id_ref(f)).collect()),
            Type::Vec(t) => Type::Vec(Box::new(t.map_id_ref(f))),
            Type::Rec(_) => todo!(),
        }
    }

    pub fn map_t_ref<F, U>(&self, f: &mut F) -> Type<Id, U>
    where
        F: FnMut(&Ty) -> U,
        Id: Copy,
    {
        match self {
            Type::Var(t) => Type::Var(f(t)),
            Type::Con(c, ts) => Type::Con(c.map_t_ref(|t| f(t)), iter_map_t_ref(&ts[..], f)),
            Type::Fun(x, y) => Type::Fun(Box::new(x.map_t_ref(f)), Box::new(y.map_t_ref(f))),
            Type::Tup(tys) => Type::Tup(iter_map_t_ref(&tys[..], f)),
            Type::Vec(ty) => Type::Vec(Box::new(ty.map_t_ref(f))),
            Type::Rec(rs) => Type::Rec(rs.map_t_ref(|ty| ty.map_t_ref(f))),
        }
    }

    pub fn is_func(&self) -> bool {
        matches!(self, Self::Fun(..))
    }

    pub fn is_app(&self) -> bool {
        matches!(self, Self::Con(..))
    }

    /// Returns `true` if the type is a single type constructor with arity 0.
    pub fn is_nullary(&self) -> bool {
        match self {
            Type::Con(_, ts) => ts.is_empty(),
            _ => false,
        }
    }

    /// If a given type is a nullary type, then this will return a reference to
    /// the identifier represemting the nullary type constructor.
    pub fn id_if_nullary(&self) -> Option<&Id> {
        match self {
            Type::Con(Con::Data(id), args) if args.is_empty() => Some(id),
            _ => None,
        }
    }

    /// Returns a vector containing all type variables in a given type in order.
    /// For example, this method applied to the type `(a, Int, a -> b -> c)`
    /// returns the vector `[a, b, c]`. Note that duplicates are *not* included!
    pub fn fv(&self) -> Vec<Ty>
    where
        Ty: Copy + PartialEq,
    {
        let mut fvs = vec![];
        match self {
            Type::Var(a) => {
                if !fvs.contains(a) {
                    fvs.push(*a)
                }
            }
            Type::Con(Con::Free(t), ts) => {
                if !fvs.contains(t) {
                    fvs.push(*t);
                }
                ts.into_iter().flat_map(|ty| ty.fv()).for_each(|tv| {
                    if !fvs.contains(&tv) {
                        fvs.push(tv);
                    }
                })
            }
            Type::Con(_, ts) | Type::Tup(ts) => {
                ts.into_iter().flat_map(|ty| ty.fv()).for_each(|tv| {
                    if !fvs.contains(&tv) {
                        fvs.push(tv);
                    }
                });
            }
            Type::Fun(ta, tb) => {
                for t in ta.fv().into_iter().chain(tb.fv()) {
                    if !fvs.contains(&t) {
                        fvs.push(t);
                    }
                }
            }
            Type::Vec(ty) => {
                for t in ty.fv() {
                    if !fvs.contains(&t) {
                        fvs.push(t);
                    }
                }
            }
            Type::Rec(rec) => match rec {
                Record::Anon(fields) | Record::Data(_, fields) => fields
                    .iter()
                    .flat_map(|field| match field {
                        Field::Rest | Field::Key(_) => vec![],
                        Field::Entry(_, ty) => ty.fv(),
                    })
                    .for_each(|t| {
                        if !fvs.contains(&t) {
                            fvs.push(t);
                        }
                    }),
            },
        };
        fvs
    }

    /// Generates a fresh list of type variables, each mapped to from a type
    /// variable contained within the given type. Duplicates are not included.
    ///
    /// `(a, m, u)` has the free type variables `a`, `m`, and `u`, each of which
    /// is internally represented by an unsigned 32-bit integer. If we were to
    /// apply this method to the type `(a, m, u)`, the enumeration `[(a, a), (b,
    /// m), (c, u)]` would be returned, providing the basis for which type
    /// variables may be reordered (or normalized).
    ///
    /// Since type variables are effectively wrappers around a number, it is
    /// possible to derive a mapping from one set of type variables to a new
    /// one, facilitating the process of *normalizing* the type variables within
    /// a given type.
    pub fn enumerate(&self) -> impl Iterator<Item = Var<Ty>>
    where
        Ty: Copy + Eq,
    {
        let mut vars = self.fv();
        vars.dedup();
        vars.into_iter().zip(0..).map(|(t, var)| Var(t, Tv(var)))
    }

    pub fn ty_str(&self) -> TypeStr<'_, Id, Ty> {
        TypeStr(self)
    }

    pub fn map_t<U>(self, f: &mut impl FnMut(Ty) -> U) -> Type<Id, U> {
        match self {
            Type::Var(t) => Type::Var(f(t)),
            Type::Con(c, ts) => {
                let mut args = vec![];
                let con = match c {
                    Con::Arrow => Con::Arrow,
                    Con::List => Con::List,
                    Con::Tuple(n) => Con::Tuple(n),
                    Con::Data(id) => Con::Data(id),
                    Con::Free(c) => Con::Free(f(c)),
                };
                for ty in ts {
                    args.push(ty.map_t(f))
                }
                Type::Con(con, args)
            }
            Type::Fun(x, y) => Type::Fun(Box::new(x.map_t(f)), Box::new(y.map_t(f))),
            Type::Tup(tys) => Type::Tup({
                let mut args = vec![];
                for ty in tys {
                    args.push(ty.map_t(f));
                }
                args
            }),
            Type::Vec(ty) => Type::Vec(Box::new(ty.map_t(f))),
            Type::Rec(rs) => Type::Rec(rs.map_t(|ty| ty.map_t(f))),
        }
    }
}

fn iter_map_t_ref<X: Copy, Y, Z>(
    typs: &[Type<X, Y>],
    f: &mut impl FnMut(&Y) -> Z,
) -> Vec<Type<X, Z>> {
    let mut tys = vec![];
    for ty in typs {
        tys.push(ty.map_t_ref(f))
    }
    tys
}

impl Type<Ident, Tv> {
    pub fn replace(self, map: &Map<Type<Ident, Tv>, Type<Ident, Tv>>) -> Type<Ident, Tv> {
        if let Some(ty) = map.get(&self) {
            return ty.clone();
        }
        match self {
            Type::Var(_) => self,
            Type::Con(con, tys) => Type::Con(con, tys.fmap(|ty| ty.replace(map))),
            Type::Fun(x, y) => {
                let (a, b) = (x, y).fmap(|ty| ty.replace(map));
                Type::Fun(a, b)
            }
            Type::Tup(ts) => Type::Tup(ts.fmap(|ty| ty.replace(map))),
            Type::Vec(t) => Type::Vec(t.fmap(|ty| ty.replace(map))),
            Type::Rec(rec) => Type::Rec(rec.map(|(con, fields)| {
                (
                    con,
                    fields.fmap(|field| {
                        field.map(|(lhs, rhs)| (lhs, rhs.fmap(|ty| ty.replace(map))))
                    }),
                )
            })),
        }
    }
}

pub struct TypeStr<'t, Id, T>(&'t Type<Id, T>);
impl<'t, Id, T> std::fmt::Debug for TypeStr<'t, Id, T>
where
    Id: 't + std::fmt::Display,
    T: 't + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Record<T, Id = Ident> {
    /// Anonymous records don't have a *constructor* and are hence *extensible*,
    /// but less type-safe
    Anon(Vec<Field<T, Id>>),
    /// Records associated with a given *constructor* and hence are statially
    /// associated with that constructor's type.
    Data(Id, Vec<Field<T, Id>>),
}

impl<T, Id> Record<T, Id> {
    pub const VOID: Self = Self::Anon(vec![]);
    /// Returns `true` if the record contains no fields, *regardless* of
    /// `Record` variant. This is equivalent to calling `Record::len` and
    /// comparing it to `0`.
    pub fn is_empty(&self) -> bool {
        match self {
            Record::Anon(fields) | Record::Data(_, fields) => fields.is_empty(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Record::Anon(es) | Record::Data(_, es) => es.len(),
        }
    }

    /// Returns a slice of all the `Field`s contained by this `Record`. Note
    /// that this method *makes no distinction* regarding its *constructor*.
    pub fn fields(&self) -> &[Field<T, Id>] {
        match self {
            Record::Anon(fields) | Record::Data(_, fields) => fields.as_slice(),
        }
    }

    #[inline]
    pub fn keys(&self) -> impl Iterator<Item = &Id> + '_ {
        self.fields().iter().filter_map(|field| match field {
            Field::Rest => None,
            Field::Key(k) | Field::Entry(k, _) => Some(k),
        })
    }

    #[inline]
    pub fn ctor(&self) -> Option<&Id> {
        match self {
            Record::Anon(_) => None,
            Record::Data(c, _) => Some(c),
        }
    }

    pub fn contains_key(&self, key: &Id) -> bool
    where
        Id: PartialEq,
    {
        self.keys().any(|id| id == key)
    }

    pub fn get(&self, key: &Id) -> Option<&T>
    where
        Id: PartialEq,
    {
        self.fields().into_iter().find_map(|field| {
            field
                .get_key()
                .and_then(|id| if id == key { field.get_value() } else { None })
        })
    }

    pub fn find(&self, pred: impl FnMut(&&Field<T, Id>) -> bool) -> Option<&Field<T, Id>>
    where
        Id: PartialEq,
        T: PartialEq,
    {
        self.fields().into_iter().find(pred)
    }

    /// Applies a transformation to the underlying components of a `Record`.
    /// Since a `Record` may or may not have a *constructor*, it follows that
    /// the kind of record *returned* will also depend on whether the first
    /// component of the tuple returned by the closure contains a `Some` variant
    /// or not. This means that it is possible to map from an `Record::Anon`
    /// variant to a `Record::Data` variant and vice-versa.
    pub fn map<F, U, V>(self, mut f: F) -> Record<V, U>
    where
        F: FnMut((Option<Id>, Vec<Field<T, Id>>)) -> (Option<U>, Vec<Field<V, U>>),
    {
        match self {
            Record::Anon(fields) => {
                let (_, fs) = f((None, fields));
                Record::Anon(fs)
            }
            Record::Data(con, fields) => {
                let (c, fs) = f((Some(con), fields));
                if let Some(ctor) = c {
                    Record::Data(ctor, fs)
                } else {
                    Record::Anon(fs)
                }
            }
        }
    }

    pub fn map_ref<U, V>(
        &self,
        f: &mut impl FnMut(Option<&Id>, &Vec<Field<T, Id>>) -> (Option<U>, Vec<Field<V, U>>),
    ) -> Record<V, U> {
        let (k, vs) = match self {
            Record::Anon(fields) => f(None, fields),
            Record::Data(k, v) => f(Some(k), v),
        };
        if let Some(con) = k {
            Record::Data(con, vs)
        } else {
            Record::Anon(vs)
        }
    }

    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> Record<T, X> {
        match self {
            Record::Anon(fs) => {
                Record::Anon(fs.into_iter().map(|fld| fld.map_id(|id| f(id))).collect())
            }
            Record::Data(k, vs) => Record::Data(
                f(k),
                vs.into_iter().map(|fld| fld.map_id(|id| f(id))).collect(),
            ),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> Record<T, X>
    where
        T: Copy,
    {
        match self {
            Record::Anon(fs) => Record::Anon(fs.iter().map(|fld| fld.map_id_ref(f)).collect()),
            Record::Data(k, vs) => {
                Record::Data(f(k), vs.iter().map(|fld| fld.map_id_ref(f)).collect())
            }
        }
    }

    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> Record<U, Id> {
        let mut entries = vec![];
        if let Record::Anon(es) = self {
            for field in es {
                match field {
                    Field::Rest => entries.push(Field::Rest),
                    Field::Key(k) => entries.push(Field::Key(k)),
                    Field::Entry(k, v) => entries.push(Field::Entry(k, f(v))),
                };
            }
            return Record::Anon(entries);
        } else if let Record::Data(k, vs) = self {
            for field in vs {
                match field {
                    Field::Rest => entries.push(Field::Rest),
                    Field::Key(k) => entries.push(Field::Key(k)),
                    Field::Entry(k, v) => entries.push(Field::Entry(k, f(v))),
                };
            }
            return Record::Data(k, entries);
        } else {
            unreachable!()
        }
    }

    pub fn map_t_ref<F, U>(&self, mut f: F) -> Record<U, Id>
    where
        F: FnMut(&T) -> U,
        Id: Copy,
    {
        match self {
            Record::Anon(es) => Record::Anon(iter_map_t_ref_field(&es[..], &mut |t| f(t))),
            Record::Data(k, v) => Record::Data(*k, iter_map_t_ref_field(&v[..], &mut |t| f(t))),
        }
    }
}

fn iter_map_t_ref_field<X, Y, Z>(
    fields: &[Field<Y, X>],
    mut f: &mut impl FnMut(&Y) -> Z,
) -> Vec<Field<Z, X>>
where
    X: Copy,
{
    let mut fs = vec![];
    for field in fields {
        fs.push(field.map_t_ref(&mut f))
    }
    fs
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Field<T, Id = Ident> {
    /// Primarily used in partial records to indicate that a given record's list
    /// of fields is incomplete. Note that it is a syntactic error for this
    /// field to *not* be the last field in record's list of fields.
    Rest,
    /// A `Field` containing only a key. Depending on the syntactic context,
    /// this may correspond to "punning" of field labels, where the field
    /// `Field::Key(x)` is interpreted as an `Field::Entry(x, x')`, with `x'`
    /// being the result of some simple mapping `f :: Id -> T` applied to `x`.
    /// For *expressions*, this `f` is equivalent to `Expression::Ident`, while
    /// for *patterns* it corresponds to `Pattern::Var`.
    Key(Id),
    /// A (record) `Field` corresponding to a key-value pair of type `(Id, T)`.
    Entry(Id, T),
}

impl<T, Id> Field<T, Id> {
    pub fn is_rest(&self) -> bool {
        matches!(self, Self::Rest)
    }
    pub fn key_only(&self) -> bool {
        matches!(self, Self::Key(..))
    }
    pub fn get_key(&self) -> Option<&Id> {
        match self {
            Field::Rest => None,
            Field::Key(k) | Field::Entry(k, _) => Some(k),
        }
    }

    /// If the `Field` is an `Entry` variant, then this returns a reference to
    /// the held value, wrapped in `Option::Some`. Otherwise, this returns
    /// `None`.
    pub fn get_value(&self) -> Option<&T> {
        match self {
            Field::Rest | Field::Key(_) => None,
            Field::Entry(_, v) => Some(v),
        }
    }

    pub fn map<F, U, X>(self, mut f: F) -> Field<X, U>
    where
        F: FnMut((Id, Option<T>)) -> (U, Option<X>),
    {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => match f((k, None)) {
                (a, None) => Field::Key(a),
                (a, Some(b)) => Field::Entry(a, b),
            },
            Field::Entry(k, v) => match f((k, Some(v))) {
                (a, None) => Field::Key(a),
                (a, Some(b)) => Field::Entry(a, b),
            },
        }
    }

    pub fn map_ref<U, X>(
        &self,
        f: &mut impl FnMut((&Id, Option<&T>)) -> (U, Option<X>),
    ) -> Field<X, U> {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => Field::Key(f((k, None)).0),
            Field::Entry(k, v) => match f((k, Some(v))) {
                (key, None) => Field::Key(key),
                (key, Some(val)) => Field::Entry(key, val),
            },
        }
    }

    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> Field<T, X> {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => Field::Key(f(k)),
            Field::Entry(k, v) => Field::Entry(f(k), v),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> Field<T, X>
    where
        T: Copy,
    {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => Field::Key(f(k)),
            Field::Entry(k, v) => Field::Entry(f(k), *v),
        }
    }

    pub fn map_t<F, U>(self, mut f: F) -> Field<U, Id>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => Field::Key(k),
            Field::Entry(k, v) => Field::Entry(k, f(v)),
        }
    }

    pub fn map_t_ref<F, U>(&self, mut f: F) -> Field<U, Id>
    where
        F: FnMut(&T) -> U,
        Id: Copy,
    {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => Field::Key(*k),
            Field::Entry(k, v) => Field::Entry(*k, f(v)),
        }
    }
}

/// A `Context` always appears as an element in a sequence of other `Context`s
/// preceding a `=>` and a type signature, and encodes what *type constraints* a
/// given *type variable* must adhere to in the following type signature.
///
/// For example, the following type signature contains *two* `Context`s
/// corresponding to two type variables `a` and `b`, where, for some given
/// typeclasses `A` and `B`, `a` is constrained (= required to be a member of)
/// the typeclass `A`, and `b` is constrained to `B`.
/// ```wysk
/// ~~> Context 1
/// ~~|  vvv
///     |A a, B b| => (a, b)
/// ~~:       ^^^  
/// ~~:  Context 2
/// ~~: ^--------^
/// ~~: Context 1 and Context 2, surrounded by `|` and followed by `=>`
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Context<Id = Ident, T = Ident> {
    pub class: Id,
    /// Defaults to `Tv`, but is parametrized in order to allow for simple
    /// (lowercase) identifiers to be used during parsing (which should then be
    /// *normalized* once the RHS is available so that `T` directly matches any
    /// type variables from the RHS).
    pub tyvar: T,
}

impl<Id, T> Context<Id, T> {
    pub fn map_id<F, X>(self, mut f: F) -> Context<X, T>
    where
        F: FnMut(Id) -> X,
    {
        let Context { class, tyvar } = self;
        Context {
            class: f(class),
            tyvar,
        }
    }
    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> Context<X, T>
    where
        T: Copy,
    {
        Context {
            class: f(&self.class),
            tyvar: self.tyvar,
        }
    }
    pub fn map_t<F, U>(self, mut f: F) -> Context<Id, U>
    where
        F: FnMut(T) -> U,
    {
        let Context { class, tyvar } = self;
        Context {
            class,
            tyvar: f(tyvar),
        }
    }
    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Context<Id, U>
    where
        Id: Copy,
    {
        Context {
            class: self.class,
            tyvar: f(&self.tyvar),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature<Id = Ident, T = Ident> {
    pub each: Vec<T>,
    pub ctxt: Vec<Context<Id, T>>,
    pub tipo: Type<Id, T>,
}

wy_common::struct_field_iters! {
    |Id, T| Signature<Id, T>
    | each => quant_iter :: T
    | ctxt => ctxt_iter :: Context<Id, T>
}

impl<Id, T> Signature<Id, T> {
    /// Checks whether all type variables in the type signature's contexts
    /// appear in the type annotation. It is valid for the type to contain type
    /// variables not covered by the contexts, *however* all type variables
    /// within the contexts *must* be used in the type!
    ///
    /// For example, the signature `|Foo a, Bar b| a -> b` is valid, but the
    /// signature `|Foo a, Bar b, Baz c| a -> b` is not as the type `a -> b`
    /// does not include the type variable `c`.
    pub fn no_unused_ctx_tyvars(&self) -> bool
    where
        T: Copy + PartialEq,
    {
        let tyvars = self.tipo.fv();
        self.ctxt.iter().all(|ctxt| tyvars.contains(&ctxt.tyvar))
    }

    pub fn ctxt_iter_mut(&mut self) -> std::slice::IterMut<'_, Context<Id, T>> {
        self.ctxt.iter_mut()
    }

    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> Signature<X, T> {
        Signature {
            each: self.each,
            ctxt: self
                .ctxt
                .into_iter()
                .map(|ctx| ctx.map_id(|id| f(id)))
                .collect(),
            tipo: self.tipo.map_id(&mut f),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> Signature<X, T>
    where
        T: Copy,
    {
        Signature {
            each: self.each.clone(),
            ctxt: self.ctxt_iter().map(|ctx| ctx.map_id_ref(f)).collect(),
            tipo: self.tipo.map_id_ref(f),
        }
    }

    pub fn map_t<U>(self, f: &mut impl FnMut(T) -> U) -> Signature<Id, U> {
        let mut ctxt = vec![];
        for Context { class, tyvar } in self.ctxt {
            ctxt.push(Context {
                class,
                tyvar: f(tyvar),
            })
        }
        Signature {
            each: self.each.fmap(|t| f(t)),
            ctxt,
            tipo: self.tipo.map_t(f),
        }
    }

    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Signature<Id, U>
    where
        Id: Copy,
    {
        Signature {
            each: self.quant_iter().map(|t| f(t)).collect(),
            ctxt: self.ctxt_iter().map(|c| c.map_t_ref(f)).collect(),
            tipo: self.tipo.map_t_ref(f),
        }
    }
}
