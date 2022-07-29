use std::{fmt::Write, hash::Hash};

use serde::{Deserialize, Serialize};
use wy_common::{either::Either, push_if_absent, Map, Mappable};
use wy_intern::{Symbol, Symbolic};
use wy_name::ident::{Ident, Identifier};

use crate::decl::Arity;
use crate::record::{Field, Record};

/// Represents a type variable.
///
/// TODO: (for display/printing aesthetics) reserve `Tv(6)` and `Tv(13)` for `f`
/// and `m`, respectively for type variables in constructor position??? Or put
/// off into a separate type in a later phase.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize)]
pub struct Tv(pub u32);

impl Tv {
    pub fn get(&self) -> u32 {
        self.0
    }
    pub fn tick(&self) -> Self {
        Self(self.0 + 1)
    }

    pub fn display(&self) -> String {
        wy_common::text::display_var(self.0)
    }

    pub fn from_symbol(sym: Symbol) -> Self {
        Tv(sym.as_u32())
    }

    pub fn symbol(&self) -> Symbol {
        Symbol::intern(self.display())
    }

    /// Lossfully coerces an identifier into a type variable.
    pub fn from_ident(ident: Ident) -> Self {
        Tv(ident.as_u32())
    }

    pub fn write_str(&self, buf: &mut String) {
        wy_common::text::write_display_var(self.0 as usize, buf)
    }

    pub fn as_type<X>(self) -> Type<X, Self> {
        Type::Var(self)
    }

    pub fn as_con<X>(self) -> Con<X, Self> {
        Con::Free(self)
    }
}

impl From<Tv> for usize {
    fn from(tv: Tv) -> Self {
        tv.0 as usize
    }
}

impl PartialEq<Ident> for Tv {
    fn eq(&self, other: &Ident) -> bool {
        matches!(other, Ident::Fresh(n) if *n == self.0)
    }
}

impl PartialEq<Tv> for Ident {
    fn eq(&self, other: &Tv) -> bool {
        matches!(self, Ident::Fresh(s) if *s == other.0)
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

impl From<&Ident> for Tv {
    fn from(id: &Ident) -> Self {
        Tv(id.get_symbol().as_u32())
    }
}

impl From<Ident> for Tv {
    fn from(id: Ident) -> Self {
        Tv(id.get_symbol().as_u32())
    }
}

impl From<Tv> for Ident {
    fn from(tv: Tv) -> Self {
        Ident::Fresh(tv.get())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Var<Id>(pub Id, pub Tv);
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
    pub fn head(self) -> Id {
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

    pub fn replace_head(&mut self, id: Id) -> Id {
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

impl<T> std::ops::Deref for Var<T> {
    type Target = Tv;

    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

impl<T> From<(T, Tv)> for Var<T> {
    fn from((t, tv): (T, Tv)) -> Self {
        Var(t, tv)
    }
}

impl Default for Var<Kind> {
    fn default() -> Self {
        Self(Kind::Star, Tv(0))
    }
}

impl Var<Kind> {
    pub fn kind(&self) -> &Kind {
        &self.0
    }
    pub fn kind_mut(&mut self) -> &mut Kind {
        &mut self.0
    }
    pub fn set_kind(&mut self, kind: Kind) {
        self.0 = kind;
    }
    #[inline]
    pub fn is_star(&self) -> bool {
        matches!(&self.0, Kind::Star)
    }
    #[inline]
    pub fn is_arrow(&self) -> bool {
        matches!(&self.0, Kind::Arrow(..))
    }
    pub fn kinds_eq(&self, var: &Self) -> bool {
        self.0 == var.0
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

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Con<Id = Ident, T = Id> {
    /// List constructor `[]`; arity = 1
    List,
    /// Tuple constructor(s) of provided arity. A value of 0 is taken to refer
    /// to the empty tuple unit type `()`.
    Tuple(usize),
    /// Function constructor `(->)`; arity = 2
    Arrow,
    /// User-defined type constructor
    Data(Id),
    Free(T),
    /// Type constructor aliases, used to superficially preserve type aliases
    /// within an environment where the alias can be resolved
    Alias(Id),
}

impl<Id: Symbolic> Symbolic for Con<Id, Tv> {
    fn get_symbol(&self) -> Symbol {
        match self {
            Con::List => wy_intern::COLON,
            Con::Tuple(ts) => {
                let s = std::iter::repeat(',').take(*ts).collect::<String>();
                wy_intern::intern_once(&*s)
            }
            Con::Arrow => wy_intern::ARROW,
            Con::Data(s) => s.get_symbol(),
            Con::Free(t) => wy_intern::intern_once(&*t.display()),
            Con::Alias(s) => s.get_symbol(),
        }
    }
}

wy_common::variant_preds! {
    |Id, T| Con[Id, T]
    | is_list => List
    | is_tuple => Tuple(_)
    | is_unit => Tuple(xs) [if *xs == 0]
    | is_arrow => Arrow
    | is_data => Data(_)
    | is_free => Free(_)
    | is_alias => Alias(_)
}

impl<S: Identifier + Symbolic> PartialEq<S> for Con<Ident, Tv> {
    fn eq(&self, other: &S) -> bool {
        match (self, other) {
            (Con::List, c) => c.get_symbol() == wy_intern::COLON,
            (Con::Tuple(n), c) => c.get_symbol() == Ident::mk_tuple_commas(*n).get_symbol(),
            (Con::Arrow, c) => c.get_symbol() == wy_intern::ARROW,
            (Con::Data(c) | Con::Alias(c), id) => id.get_symbol() == c.get_symbol(),
            (Con::Free(t), s) if s.is_fresh() || s.is_lower() => {
                s.get_symbol() == Symbol::intern(t.display())
            }
            _ => false,
        }
    }
}

impl Con<Ident, Tv> {
    const fn mk_data(symbol: Symbol) -> Con<Ident, Tv> {
        Con::Data(Ident::Upper(symbol))
    }

    pub fn from_ident(ident: Ident) -> Self {
        if let Ident::Fresh(n) = ident {
            Con::Free(Tv(n))
        } else if let Some(n) = ident.comma_count() {
            Con::Tuple(n)
        } else if ident.is_cons_sign() {
            Con::List
        } else if ident.is_arrow() {
            Con::ARROW
        } else {
            Con::Data(ident)
        }
    }

    pub const ARROW: Self = Self::mk_data(wy_intern::ARROW);
    pub const BOOL: Self = Self::mk_data(wy_intern::BOOL);
    pub const INT: Self = Self::mk_data(wy_intern::INT);
    pub const NAT: Self = Self::mk_data(wy_intern::NAT);
    pub const FLOAT: Self = Self::mk_data(wy_intern::FLOAT);
    pub const DOUBLE: Self = Self::mk_data(wy_intern::DOUBLE);
    pub const BYTE: Self = Self::mk_data(wy_intern::BYTE);
    pub const CHAR: Self = Self::mk_data(wy_intern::CHAR);
    pub const STR: Self = Self::mk_data(wy_intern::STR);
    pub const IO: Self = Self::mk_data(wy_intern::IO);
    pub const HOLE: Self = Self::mk_data(wy_intern::WILD);
}

impl<Id: std::fmt::Debug, T: std::fmt::Debug> std::fmt::Debug for Con<Id, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::List => write!(f, "[]"),
            Self::Tuple(n) => (0..=*n)
                .fold(write!(f, "("), |a, _| a.and(write!(f, ",")))
                .and(write!(f, ")")),
            Self::Arrow => write!(f, "(->)"),
            Self::Data(con) | Self::Alias(con) => Id::fmt(con, f),
            Self::Free(var) => T::fmt(var, f),
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
            Con::Data(id) | Con::Alias(id) => write!(f, "{}", id),
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
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type<Id = Ident, T = Id> {
    /// Type variables. These use their own special inner type `Tv`, which is a
    /// newtype wrapper around a `u32`.
    Var(T),
    /// Type constructor applications.
    Con(Con<Id, T>, Vec<Type<Id, T>>),
    /// Function type. The type `a -> b` describes a function whose argument is
    /// of type `a` and whose return value is of type `b`. Functions are *all*
    /// curried, hence a multi-argument function type is a function type whose
    /// argument type is *also* a function. For example, the type `a -> b -> c`
    /// describes a function whose first argument is of type `a`, second
    /// argument if of type `b` and returns a value of type `c`.
    ///
    /// Function types are sugar for type application of the type constructor
    /// `(->)`, which as an infix is *right* associative. Hence, the type
    /// signature `a -> b -> c -> d` can be syntactically grouped and re-written
    /// as `a -> (b -> (c -> d))`.
    ///
    /// When an intermediary type in the function chain is itself another
    /// function type, then parentheses are added to prevent ambiguity, as in
    /// the type `a -> (b -> c) -> d`, which is read as `a -> ((b -> c) -> d)`,
    /// where the first argument is of type `a` and the second is of type `b ->
    /// c`.
    Fun(Box<Type<Id, T>>, Box<Type<Id, T>>),
    Tup(Vec<Type<Id, T>>),
    Vec(Box<Type<Id, T>>),
    Rec(Record<Id, Type<Id, T>>),
}

wy_common::variant_preds! {
    |Id, T| Type[Id, T]
    | is_var => Var(_)
    | is_fun => Fun(..)
    | is_con => Con(..)
    | is_vec => Vec(..)
    | is_nullary => Con(_, ts) [if ts.is_empty()]
    | is_fun_of_fun => Fun(x, _) [if x.is_fun()]
    | is_1arg_fun => Fun(x, y) [if !x.is_fun() && !y.is_fun()]
    | is_2arg_fun => Fun(x, y) [if !x.is_fun() && y.is_1arg_fun()]
    | is_fun_arg2_is_fun => Fun(_, y) [if y.is_fun_of_fun()]
    | is_list_con_form => Con(Con::List, _)
    | is_arrow_con_form => Con(Con::Arrow, _)
    | is_con_var => Con(Con::Free(_), _)
    | is_concrete_con => Con(Con::Data(_), _)
    | is_alias_con => Con(Con::Alias(_), _)
}

impl<Id, T> Type<Id, T> {
    pub const UNIT: Self = Self::Tup(vec![]);

    #[inline]
    pub fn mk_fun(x: Self, y: Self) -> Self {
        Self::Fun(Box::new(x), Box::new(y))
    }

    /// Given a type `t0` and a (reversible) collection of types `t1`, `t2`,
    /// ..., `tn`, returns the function type `t0 -> (t1 -> (t2 -> ... -> tn))`.
    /// If the collection of types provided is empty, then the initial type `t0`
    /// is returned.
    #[inline]
    pub fn try_mk_fun(head: Self, rest: impl DoubleEndedIterator + Iterator<Item = Self>) -> Self {
        if let Some(tail) = rest.rev().reduce(|a, c| Self::mk_fun(a, c)) {
            Self::mk_fun(head, tail)
        } else {
            head
        }
    }

    #[inline]
    pub fn mk_var_tyapp(con_var: T, args: impl IntoIterator<Item = Self>) -> Self {
        Self::Con(Con::Free(con_var), args.into_iter().collect())
    }

    #[inline]
    pub fn mk_app(ty_con: Con<Id, T>, ty_args: impl IntoIterator<Item = Self>) -> Self {
        Self::Con(ty_con, ty_args.into_iter().collect())
    }

    #[inline]
    pub fn mk_list(list_of: Self) -> Self {
        Self::Vec(Box::new(list_of))
    }

    #[inline]
    pub fn mk_tuple(tuple_of: impl IntoIterator<Item = Self>) -> Self {
        Self::Tup(tuple_of.into_iter().collect())
    }

    #[inline]
    pub fn mk_var(tyvar: T) -> Self {
        Self::Var(tyvar)
    }

    #[inline]
    pub fn to_list(self) -> Self {
        Self::mk_list(self)
    }

    #[inline]
    pub fn clone_to_list(&self) -> Self
    where
        Id: Clone,
        T: Copy,
    {
        Self::mk_list(self.clone())
    }

    #[inline]
    pub fn get_con(&self) -> Option<Con<Id, T>>
    where
        Id: Clone,
        T: Copy,
    {
        match self {
            Type::Var(_) => None,
            Type::Con(c, _) => Some(c.clone()),
            Type::Fun(_, _) => Some(Con::Arrow),
            Type::Tup(ts) => {
                if ts.is_empty() {
                    None
                } else {
                    Some(Con::Tuple(ts.len()))
                }
            }
            Type::Vec(_) => Some(Con::List),
            Type::Rec(r) => r.ctor().map(|id| Con::Data(id.clone())),
        }
    }

    /// Returns the number of arguments in a function. If the arity is `zero`,
    /// then this method returns `None`.
    pub fn fun_arity(&self) -> Option<Arity> {
        let mut arity = Arity::ZERO;
        let mut tmp = self;
        while let Self::Fun(_x, y) = tmp {
            arity += 1;
            tmp = y.as_ref();
        }
        if arity.is_zero() {
            None
        } else {
            Some(arity)
        }
    }

    /// Returns a vector of all the argument types of a function type in order
    /// from left to right; e.g., for the type
    ///
    ///     a -> b -> c -> d
    ///
    /// which is parsed as
    ///
    ///     a -> (b -> (c -> d))
    ///
    /// this method returns the list
    ///
    ///     [a, b, c, d]
    ///
    /// If the type corresponding to `Self` is not a function type, then a
    /// single-element vector containing the `Self` type instance is returned.
    /// Thus, this method returns vectors of length > 1 for function types. The
    /// method `maybe_fun_vec` returns instead an `Either<Type, Vec<Type>>`
    /// instance as an alternative to this functionality.
    ///
    /// Note however that this does not have a "flattening" effect: the type
    ///
    ///     (a -> b) -> (c -> (d -> e)) -> f
    ///
    /// with this method applied, would return
    ///
    ///     [(a -> b), (c -> (d -> e)), f]
    ///
    /// while the function type
    ///
    ///     (a -> b) -> c -> d -> (e -> f)
    ///
    /// would return
    ///
    ///     [(a -> b), c, d, e, f]
    ///
    /// since function arrows are *right* associative.
    ///
    pub fn fun_vec(self) -> Vec<Self> {
        let mut args = vec![];
        let mut tmp = self;
        while let Self::Fun(x, y) = tmp {
            args.push(*x);
            tmp = *y;
        }
        args.push(tmp);
        args
    }

    /// If `Self` is a function type, then it returns a list of each of its
    /// arguments wrapped in an `Either::Left` variant. Otherwise, it returns
    /// `Self` wrapped in an `Either::Right` variant.
    ///
    /// See notes for [`Type::fun_vec`] for more details.
    pub fn maybe_fun_vec(self) -> Either<Vec<Self>, Self> {
        match self {
            Self::Fun(x, y) => {
                let mut args = vec![];
                args.push(*x);
                let mut tmp = *y;
                while let Self::Fun(u, v) = tmp {
                    args.push(*u);
                    tmp = *v;
                }
                args.push(tmp);
                Either::Left(args)
            }
            ty => Either::Right(ty),
        }
    }

    /// TODO!
    ///
    /// Compares the current type to the one provided and compares their general
    /// structures without comparing type variables, etc.
    ///
    /// This method does NOT unify types, nor does it check whether two types
    /// are strictly unifiable; rather, this method provides a quick (and dirty)
    /// way to inspect two types to determine whether they are *strictly
    /// non-unifiable*.
    ///
    /// An example of this is between differently sized tuples, tuples and
    /// lists, and type constructors with differing arities, as well as
    /// performing a (preliminary) occurs check consisting of a type variable on
    /// one side and a (non-type variable) type containing that type variable on
    /// the right-hand side, e.g., `a` vs `[a]`, `b` vs `(a, b)`, `a` vs `a ->
    /// a`, etc.
    ///
    /// **Note** that in the table below, the `Pass?` column specifically refers
    /// to whether the two types are able to be unified. A `false` indicates
    /// that two types are KNOWN to not be unifiable, and corresponds to the
    /// same boolean value returned by this method, while `maybe` is used in
    /// place of `true` to emphasize the asymmetric determinism of this method,
    /// e.g., `maybe` corresponds to a `true` return value.
    ///
    /// | LHS       | RHS        | Pass? | Why?
    /// |:----------|:-----------|:------|:-----------------------------------
    /// |`a`        | `[a]`      | false | `a` would be infinite
    /// |`(a, b, c)`| `(a, b)`   | false | unequal constructors `(,,)` != `(,)`
    /// |`a -> b`   | `c -> d`   | maybe | variables may resolve on both sides
    /// |`m a b`    | `m a a`    | maybe | variable `b` may resolve
    /// |`[(a, b)]` | `m a b`    | ???   | mismatched kind for `[] ((,) a b)`
    pub fn compatible(&self, other: &Self) -> bool
    where
        T: Copy + PartialEq,
        Id: Clone + PartialEq,
    {
        use Con as C;
        use Type as T;
        fn zips<A: Clone + PartialEq, B: Copy + PartialEq>(
            xs: &Vec<Type<A, B>>,
            ys: &Vec<Type<A, B>>,
        ) -> bool {
            // confirm commutativity!!!
            xs.len() == ys.len()
                && xs
                    .into_iter()
                    .zip(ys)
                    .all(|(x, y)| x.compatible(y) && y.compatible(y))
        }

        match (self, other) {
            // both being variables means we know nothing about the types'
            // structures
            (T::Var(_), T::Var(_)) => true,

            (T::Var(a), t) | (t, T::Var(a)) => !t.depends_on(a),

            // built-in differences in kind
            (T::Vec(_), T::Tup(_)) | (T::Tup(_), T::Vec(_)) => false,

            // unit is a special case when it comes to being represented by a
            // tuple constructor
            (T::Tup(xs) | T::Con(C::Tuple(0), xs), T::Tup(ys) | T::Con(C::Tuple(0), ys))
                if xs.is_empty() && ys.is_empty() =>
            {
                true
            }

            (T::Tup(xs), T::Tup(ys)) if xs.len() == ys.len() => zips(xs, ys),

            // (1, 2) ~ (,) 1 2
            (T::Tup(xs), T::Con(C::Tuple(n), ys)) | (T::Con(C::Tuple(n), xs), T::Tup(ys))
                if *n > 1 && {
                    let m = *n - 1;
                    xs.len() == m && ys.len() == m
                } =>
            {
                zips(xs, ys)
            }
            (T::Vec(x), T::Con(C::List, ys)) | (T::Con(C::List, ys), T::Vec(x))
                if ys.len() == 1 =>
            {
                let y = &ys[0];
                // confirm commutativity
                x.compatible(y) && y.compatible(x)
            }

            (x, y) => {
                x.vars().into_iter().all(|ref t| !y.depends_on(t))
                    && y.vars().into_iter().all(|ref t| !x.depends_on(t))
            }
        }
    }

    /// Returns the current type rewritten to in terms of only `Type::Var` and
    /// `Type::Con`. Note: while the tuple constructors for values are identical
    /// to that of the tuple type constructors, the same does *not* hold for
    /// lists: the list *data* constructor `(:)` is distinct from the list
    /// *type* constructor `[]`, which is otherwise identical to the empty list
    /// expression.
    ///
    /// * `[a]` => `[] a`  
    /// * `(a, b)` => `(,) a b`
    /// * `a -> b` => `(->) a b`
    /// * `[Char]` => `[] Char`
    /// * `(Char, Int, [a])` => `(,,) Char Int ([] a)`
    /// * `(a -> b) -> m a -> m b` => `(->) ((->) a b) ((->) (m a) (m b)) `
    ///
    pub fn simplify(self) -> Self {
        match self {
            a @ Type::Var(_) => a,
            Type::Con(con, args) => Type::Con(con, args.fmap(|ty| ty.simplify())),
            Type::Fun(t1, t2) => Type::Con(Con::Arrow, vec![t1.simplify(), t2.simplify()]),
            Type::Tup(ts) => Type::Con(Con::Tuple(ts.len()), ts.fmap(|t| t.simplify())),
            Type::Vec(t) => Type::Con(Con::List, vec![t.simplify()]),
            Type::Rec(_) => todo!(),
        }
    }

    pub fn contains_constructor(&self, con: &Con<Id, T>) -> bool
    where
        Id: PartialEq,
        T: PartialEq,
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
    pub fn depends_on(&self, var: &T) -> bool
    where
        T: PartialEq,
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
    pub fn contains(&self, subty: &Type<Id, T>) -> bool
    where
        Id: PartialEq,
        T: PartialEq,
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

    /// If a given type is a nullary type, then this will return a reference to
    /// the identifier represemting the nullary type constructor.
    pub fn id_if_nullary(&self) -> Option<&Id> {
        match self {
            Type::Con(Con::Data(id), args) if args.is_empty() => Some(id),
            _ => None,
        }
    }

    /// Returns a list of all the free variables in the order in which they
    /// appear
    pub fn vars(&self) -> Vec<T>
    where
        T: Copy,
    {
        let mut vars = vec![];
        match self {
            Type::Var(v) => vars.push(*v),
            Type::Con(Con::Free(v), args) => {
                vars.push(*v);
                args.into_iter().for_each(|ty| vars.extend(ty.vars()));
            }
            Type::Con(_, args) => args.into_iter().for_each(|ty| vars.extend(ty.vars())),
            Type::Fun(x, y) => {
                vars.extend(x.vars());
                vars.extend(y.vars());
            }
            Type::Tup(args) => args.into_iter().for_each(|ty| vars.extend(ty.vars())),
            Type::Vec(t) => vars.extend(t.vars()),
            Type::Rec(rec) => rec.fields().into_iter().for_each(|fld| {
                if let Some(v) = fld.get_value() {
                    vars.extend(v.vars())
                }
            }),
        };
        vars
    }

    /// Returns a vector containing all type variables in a given type in order.
    /// For example, this method applied to the type `(a, Int, a -> b -> c)`
    /// returns the vector `[a, b, c]`. Note that duplicates are *not* included!
    pub fn fv(&self) -> Vec<T>
    where
        T: Copy + PartialEq,
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
    pub fn enumerate(&self) -> impl Iterator<Item = Var<T>>
    where
        T: Copy + Eq,
    {
        let mut vars = self.fv();
        vars.dedup();
        vars.into_iter().zip(0..).map(|(t, var)| Var(t, Tv(var)))
    }

    pub fn ty_str(&self, prec: usize) -> TypeStr<'_, Id, T> {
        TypeStr(self, prec)
    }
}

pub fn poly_vars<'a, Id>(poly: impl IntoIterator<Item = &'a Tv>) -> Vec<Type<Id, Tv>> {
    poly.into_iter().copied().map(Tv::as_type).collect()
}

pub struct TypeStr<'t, Id, T>(&'t Type<Id, T>, usize);
impl<'t, Id, T> std::fmt::Debug for TypeStr<'t, Id, T>
where
    Id: 't + std::fmt::Display,
    T: 't + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Takes a type constructor and its type arguments, of the form `C t1 t2 ...
/// tn` and returns the function type `t1 -> t2 -> ... -> tn -> C t1 t2 ... tn`.
///
/// Note that this is NOT necessarily the function type used by every
/// construction: consider the following snippet of code:
/// ```wysk
/// data Foo a = Foo' a a a
/// ~~ Foo' :: a -> a -> a -> Foo a
/// foo :: [a] -> Int -> Foo Int
///     | xs y = let m = length xs in Foo' (m - y) (m + y) (m * y)
/// ```
/// We see that the type constructor `Foo` is parametrized over one single type,
/// yet the *data constructor* `Foo'`, as well as the function `foo` -- both of
/// which return a `Foo` type -- has more than 1 argument.
pub fn guess_tycon_fun_ty<Id, T>(con: Con<Id, T>, args: Vec<Type<Id, T>>) -> Type<Id, T>
where
    Id: Clone,
    T: Copy,
{
    args.clone()
        .into_iter()
        .rev()
        .fold(Type::Con(con, args), |a, c| Type::mk_fun(a, c))
}

impl Type<Ident, Tv> {
    pub const BOOL: Self = Self::mk_nullary(Con::BOOL);
    pub const INT: Self = Self::mk_nullary(Con::INT);
    pub const NAT: Self = Self::mk_nullary(Con::NAT);
    pub const FLOAT: Self = Self::mk_nullary(Con::FLOAT);
    pub const DOUBLE: Self = Self::mk_nullary(Con::DOUBLE);
    pub const CHAR: Self = Self::mk_nullary(Con::CHAR);
    pub const STR: Self = Self::mk_nullary(Con::STR);
    pub const BYTE: Self = Self::mk_nullary(Con::BYTE);

    pub const fn mk_nullary(con: Con<Ident, Tv>) -> Self {
        Self::Con(con, vec![])
    }

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

    /// Returns a tuple type with `n` components, each component a
    /// fresh type variable. If `n = 0`, then the unit type is
    /// returned, and calling this method with `n = 1` will always
    /// return the type variable `a` (`Type::Var(Tv(0))`).
    ///
    /// For example, `n = 3` returns `(a, b, c)`.
    ///
    /// Note that type variables must be
    /// refreshed when used in a type context.
    pub fn mk_n_tuple(n: usize) -> Type<Ident, Tv> {
        if n == 0 {
            Type::UNIT
        } else if n == 1 {
            Type::Var(Tv(0))
        } else {
            Type::Tup((0..n).map(|m| Type::Var(Tv(m as u32))).collect())
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
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Context<Id = Ident, T = Ident> {
    /// The name of the type class for which this holds
    pub class: Id,
    /// Defaults to `Tv`, but is parametrized in order to allow for simple
    /// (lowercase) identifiers to be used during parsing (which should then be
    /// *normalized* once the RHS is available so that `T` directly matches any
    /// type variables from the RHS).
    pub head: T,
}

pub type Predicate<Id, T> = Context<Id, Type<Id, T>>;

impl<Id, T> Context<Id, T> {
    pub fn class_id(&self) -> &Id {
        &self.class
    }
    pub fn head(&self) -> &T {
        &self.head
    }

    pub fn unzip(contexts: &[Self]) -> Vec<(Id, T)>
    where
        Id: Clone,
        T: Clone,
    {
        contexts
            .into_iter()
            .map(|ctx| (ctx.class.clone(), ctx.head.clone()))
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Signature<Id = Ident, T = Ident> {
    /// quantified type variables -- should this be here or a separate struct or
    /// type variant?
    pub each: Vec<T>,
    pub ctxt: Vec<Context<Id, T>>,
    pub tipo: Type<Id, T>,
}

wy_common::struct_field_iters! {
    |Id, T| Signature<Id, T>
    | each => each_iter :: T
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
        self.ctxt.iter().all(|ctxt| tyvars.contains(&ctxt.head))
    }

    pub fn ctxt_iter_mut(&mut self) -> std::slice::IterMut<'_, Context<Id, T>> {
        self.ctxt.iter_mut()
    }
}

/// Equivalent to `Option<Signature<Id, T>>`, expressing whether a
/// type annotation has been provided (in which case the `Explicit`
/// variant is used) or omitted (in which case the `Implicit` variant
/// is used).
///
/// A benefit to using a custom type over `Option` is that it allows
/// for further extension to the type system. Universal quantification
/// is currently (superficially) recorded in the `Signature` type, but
/// will be offloaded to `Contract`s, allowing for `Signature`s to
/// specialize in gluing together class constraints with type nodes.
///
/// An explicit contract corresponds to the type signature found in
/// source code and is never overwritten (only isomorphically modified
/// in terms of representation), but rather used as a reference with
/// which type inference and checking is unified in later phases.
///
/// Note that whether a contract is implicit or explicit does not
/// affect whether the item to which it is tied has its type inferred.
/// For example, the type of a binding is still inferred regardless as
/// whether it was explicitly annotated with a type. However, after
/// inference, explicit contracts are unified against the inferred
/// types in addition to the inference-generated constraints.
///
/// For example, during type inference every binding has a type
/// inferred along with a set of type constraints. Type checking fails
/// if the inferred type cannot be solved according to the generated
/// constraints. If a given binding is annotated, and the inferred
/// type is solvable with respect to the generated constraints but
/// cannot be unified with respect to the annotated type, an error
/// will be raised and type checking will fail, as the explicit
/// contract takes precedence over implicit inference.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Contract<Id, T> {
    Implicit,
    Explicit(Signature<Id, T>),
}

wy_common::variant_preds! {
    |Id, T| Contract[Id, T]
    | is_implicit => Implicit
    | is_explicit => Explicit(_)
}

impl<Id, T> Contract<Id, T> {
    pub fn signature(&self) -> Option<&Signature<Id, T>> {
        if let Self::Explicit(s) = self {
            Some(s)
        } else {
            None
        }
    }
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
                        if arg.is_fun() || (arg.is_con() && !arg.is_nullary()) {
                            write!(f, " ({})", arg)?;
                            continue;
                        }
                        write!(f, " {}", arg)?;
                    }
                    Ok(())
                }
            }
            // x -> y
            Type::Fun(x, y) => {
                if x.is_fun() {
                    write!(f, "({})", x)?;
                } else {
                    write!(f, "{}", x)?;
                }
                write!(f, " -> ")?;
                // if y.is_fun() {
                //     write!(f, "({})", y)
                // } else {
                write!(f, "{}", y)
                // }
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
                match &rec
                    .fields()
                    .iter()
                    .filter_map(|field| match field {
                        // for typed records, we should expect both lhs (keys)
                        // and rhs (types)
                        Field::Rest | Field::Key(_) => None,
                        Field::Entry(k, v) => Some((k, v)),
                    })
                    .collect::<Vec<_>>()[..]
                {
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

#[macro_export]
macro_rules! Ty {
    (Int) => {{ Type::INT }};
    (Nat) => {{ Type::NAT }};
    (Byte) => {{ Type::BYTE }};
    (Bool) => {{ Type::BOOL }};
    (IO $x:expr) => {{ Type::mk_app(Con::IO, $x) }};
    (Str) => {{ Type::STR }};
    (Char) => {{ Type::Char }};
    (Float) => {{ Type::FLOAT }};
    (Double) => {{ Type::DOUBLE }};
    (#()) => {{ $crate::tipo::Type::UNIT }};
    (
        ($($ts:tt)+)
    ) => {{
        $crate::Ty! { $($ts)+ }
    }};
    (
        ($($an:tt,)*)
    ) => {{ $crate::tipo::Type::mk_tuple([$($an,)*]) }};
    (@$id:ident) => {{ $id.clone() }};
    (@$id:ident -> $($rest:tt)+) => {{
        Type::mk_fun(
            $id.clone(), $crate::Ty! { $($rest)+ }
        )
    }};
    ($num:literal) => {{ Type::Var(Tv($num)) }};
    ($num:literal -> $($rest:tt)+) => {{
        Type::mk_fun(Type::Var(Tv($num)), $crate::Ty! { $($rest)+ })
    }};
    (#($t0:ident $($ts:tt)*)) => {{
        $crate::tipo::Type::mk_app(
            $crate::tipo::Con::Data(
                Ident::Upper(wy_intern::intern_once(stringify!($t0)))
            ),
            [$($crate::Ty! { $ts },)*]
        )
    }};
    (#($t0:ident $($($ts:tt)+)?) -> $($tail:tt)+) => {{
        $crate::tipo::Type::mk_fun(
            $crate::tipo::Type::mk_app(
                $crate::tipo::Con::Data(
                    wy_name::ident::Ident::Upper(wy_intern::intern_once(stringify!($t0)))
                ),
                [$($($crate::Ty! { $ts },)+)?]
            ),
            $crate::Ty! { $($tail)+ }
        )
    }};
    (
        $con:ident $(. $($ts:tt)+)?
    ) => {{
        $crate::Ty! { #( $con $($($ts)+)? )}
    }};
    (
        $con:ident $(. $($ts:tt)+)? -> $(rest:tt)+
    ) => {{
        $crate::tipo::Type::mk_fun(
            $crate::Ty! { #( $con $($($ts)+)? )},
            $crate::Ty! { $($rest)+ }
        )
    }};
    (
        [$($ts:tt)+]
    ) => {{ $crate::tipo::Type::mk_list($($ts)+) }};
    (
        $left:tt -> $($right:tt)+
    ) => {{
        $crate::tipo::Type::mk_fun(
            $crate::Ty! { $left }, $crate::Ty! { $($right)+ }
        )
    }};

}

impl<Id> Type<Id, Tv> {
    /// Like the method `simplify`, this reduces a type in terms of type
    /// variables and type application, but represented with a `Ty` instance
    /// instead of as a `Self` type.
    pub fn simplify_ty(&self) -> Ty
    where
        Id: Copy + Symbolic,
    {
        match self {
            Type::Var(v) => Ty::Var(Var(Kind::Star, *v)),
            Type::Con(c, args) => {
                let kind = || Kind::mk(self.fv().len());
                match c {
                    Con::List => {
                        if args.is_empty() {
                            Ty::Con(Symbol::from("[]"), Kind::mk(2))
                        } else {
                            Ty::mk_list(args[0].simplify_ty())
                        }
                    }
                    Con::Tuple(n) => {
                        let m = args.len();
                        if *n == m {
                            Ty::mk_tuple(args.into_iter().map(Self::simplify_ty).collect())
                        } else {
                            todo!()
                        }
                    }
                    Con::Arrow => args
                        .into_iter()
                        .map(|t| t.simplify_ty())
                        .reduce(Ty::mk_fun)
                        .unwrap_or_else(|| Ty::Con(Ty::ARROW, Kind::mk(3))),
                    Con::Data(n) | Con::Alias(n) => args.into_iter().map(|t| t.simplify_ty()).fold(
                        Ty::Con(n.get_symbol(), Kind::mk(self.fv().len())),
                        |a, c| Ty::mk_app(a, c),
                    ),
                    Con::Free(t) => args.into_iter().map(|t| t.simplify_ty()).fold(
                        Ty::Con(t.symbol(), Kind::Arrow(Box::new([Kind::Star, kind()]))),
                        |a, c| Ty::mk_app(a, c),
                    ),
                }
            }
            Type::Fun(x, y) => {
                use Kind::{Arrow, Star};
                let k = || Arrow(Box::new([Star, Arrow(Box::new([Star, Star]))]));
                let app = |a, b| Ty::App(Box::new([a, b]));
                let fun = |a, b| app(app(Ty::Con(Ty::ARROW, k()), a), b);
                // a -> b -> c
                // (->) a ((->) b c)
                fun(x.simplify_ty(), y.simplify_ty())
            }
            Type::Tup(ts) => Ty::mk_tuple(ts.into_iter().map(|ty| ty.simplify_ty()).collect()),
            Type::Vec(ts) => Ty::mk_list(ts.simplify_ty()),
            Type::Rec(_) => todo!(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Ty {
    Var(Var<Kind>),
    Con(Symbol, Kind),
    App(Box<[Self; 2]>),
    Gen(usize),
}

impl Default for Ty {
    fn default() -> Self {
        Ty::Var(Var(Kind::Star, Tv(0)))
    }
}

impl Ty {
    pub const ARROW: Symbol = wy_intern::ARROW;

    /// Returns a list containing all type variables in a given type in order
    /// **without** duplicates. Use the `vars` method to get a list containing
    /// all type variables with duplicates.
    ///
    /// For example, this method applied to the type `(a, Int, a -> b -> c)`,
    /// which simplifies to `(,,) a Int ((->) a ((->) b c))`, returns the list
    /// `[a, b, c]`.
    pub fn fv(&self) -> Vec<Tv> {
        match self {
            Ty::Var(Var(_, tv)) => vec![*tv],
            Ty::App(xy) => {
                let [x, y] = xy.as_ref();
                y.fv().into_iter().fold(x.fv(), push_if_absent)
            }
            _ => vec![],
        }
    }

    pub fn kind(&self) -> &Kind {
        match self {
            Ty::Var(Var(k, _)) => k,
            Ty::Con(_, k) => k,
            Ty::App(ab) => match ab.as_ref()[0].kind() {
                Kind::Arrow(uv) => &uv.as_ref()[1],
                Kind::Star => {
                    println!(
                            "\n\u{1b}[0m\u{1b}[31;15m[Error] malformed type\u{1b}[0m: the type\n\t`{self}`\nshould not be of kind `*`\n"
                        );
                    panic!("kind of `{self}`")
                }
            },
            Ty::Gen(_) => todo!(),
        }
    }

    #[inline]
    pub fn is_var(&self) -> bool {
        matches!(self, Ty::Var(..))
    }

    #[inline]
    pub fn is_con(&self) -> bool {
        matches!(self, Ty::Con(..))
    }

    #[inline]
    pub fn is_app(&self) -> bool {
        matches!(self, Ty::App(..))
    }

    #[inline]
    pub fn is_fun(&self) -> bool {
        matches!(
            self,
            Ty::App(ab) if matches!(
                &ab.as_ref()[0],
                Ty::App(xy) if matches!(
                    &xy.as_ref()[0],
                    Ty::Con(s, _) if *s == Self::ARROW
                )
            )
        )
    }

    #[inline]
    pub fn is_tuple(&self) -> bool {
        if let Ty::App(ab) = self {
            let mut tmp = &ab.as_ref()[0];
            while let Ty::App(xy) = tmp {
                let [x, _] = &**xy;
                if let Ty::Con(s, _) = x {
                    if s.as_str().starts_with("(,") {
                        return true;
                    }
                } else {
                    tmp = x
                }
            }
        };
        false
    }

    #[inline]
    pub fn is_list(&self) -> bool {
        matches!(self, Ty::App(xy) if matches!(&xy.as_ref()[0], Ty::Con(s, _) if s.as_str() == "[]"))
    }

    pub fn mk_app(ta: Ty, tb: Ty) -> Ty {
        Ty::App(Box::new([ta, tb]))
    }

    pub fn mk_fun(from_ty: Self, to_ty: Self) -> Self {
        Ty::App(Box::new([
            Ty::App(Box::new([
                Ty::Con(Ty::ARROW, Kind::Arrow(Box::new([Kind::Star, Kind::Star]))),
                from_ty,
            ])),
            to_ty,
        ]))
    }

    pub fn mk_list(list_of: Self) -> Self {
        Self::mk_app(Self::Con(Symbol::intern("[]"), Kind::mk(2)), list_of)
    }

    pub fn mk_tuple(mut tuple_of: Vec<Self>) -> Self {
        match tuple_of.len() {
            0 => Ty::Con(Symbol::from_str("()"), Kind::Star),
            1 => tuple_of.remove(0),
            n => {
                let con = Ty::Con(
                    std::iter::once('(')
                        .chain(std::iter::repeat_with(|| ','))
                        .chain(std::iter::once(')'))
                        .collect(),
                    Kind::mk(n + 1),
                );
                tuple_of
                    .into_iter()
                    .rev()
                    .fold(con, |a, c| Ty::mk_app(a, c))
            }
        }
    }
}

impl std::fmt::Debug for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        struct K<A>([A; 2]);
        impl<A: std::fmt::Debug> std::fmt::Debug for K<A> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_tuple("")
                    .field(&self.0[0])
                    .field(&self.0[1])
                    .finish()
            }
        }
        match self {
            Ty::Var(Var(k, t)) => write!(f, "Var({t} :: {k})"),
            Ty::Con(s, k) => {
                write!(f, "Con({s} :: {k})")
            }
            Ty::App(xy) => {
                let [x, y] = &**xy;
                write!(f, "App")?;
                K::fmt(&K([x, y]), f)
            }
            Ty::Gen(n) => write!(f, "Gen('{n})"),
        }
    }
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Var(Var(_, t)) => write!(f, "{t}"),
            Ty::Con(s, _) => write!(f, "{s}"),
            Ty::App(xy) => {
                let [x, y] = &**xy;
                if let Ty::Con(s, _) = x {
                    if s.as_str() == "[]" {
                        write!(f, "[{y}]")
                    } else {
                        write!(f, "{s} {y}")
                    }
                } else if let Ty::App(uv) = x {
                    let [u, v] = uv.as_ref();
                    if let Ty::Con(s, _) = u {
                        match s.as_str() {
                            "->" => {
                                if v.is_fun() {
                                    write!(f, "({v} -> {y})")
                                } else {
                                    write!(f, "{v} -> {y}")
                                }
                            }
                            "(,)" => {
                                write!(f, "({v}, {y})")
                            }
                            s => {
                                write!(f, "{s} {v} {y}")
                            }
                        }
                    } else {
                        write!(f, "{u} {v} {y}")
                    }
                } else {
                    write!(f, "{x} {y}")
                }
            }
            Ty::Gen(n) => f.write_str("'").and(usize::fmt(n, f)),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Kind {
    Star,
    Arrow(Box<[Kind; 2]>),
}

wy_common::variant_preds! {
    Kind
    | is_star => Star
    | is_arrow => Arrow(..)
}

impl std::fmt::Debug for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Star => write!(f, "*"),
            Self::Arrow(ab) => {
                let [a, b] = ab.as_ref();
                match (a, b) {
                    (Kind::Star, Kind::Star) => write!(f, "* -> *"),
                    (Kind::Star, k) => write!(f, "* -> {:?}", k),
                    (k, Kind::Star) => write!(f, "({:?}) -> *", k),
                    _ => write!(f, "{:?} -> {:?}", a, b),
                }
            }
        }
    }
}

impl std::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Star => write!(f, "*"),
            Kind::Arrow(ab) => {
                let [a, b] = ab.as_ref();
                match (a, b) {
                    (Kind::Star, Kind::Star) => write!(f, "* -> *"),
                    (Kind::Star, k) => write!(f, "* -> {k}"),
                    (k, Kind::Star) => write!(f, "({k}) -> *"),
                    _ => write!(f, "{} -> {}", a, b),
                }
            }
        }
    }
}

impl Kind {
    pub fn fun_con() -> Self {
        Kind::Arrow(Box::new([
            Kind::Star,
            Kind::Arrow(Box::new([Kind::Star, Kind::Star])),
        ]))
    }
    pub fn list_con() -> Self {
        Kind::Arrow(Box::new([Kind::Star, Kind::Star]))
    }

    pub fn mk(mut n: usize) -> Kind {
        let mut k = Kind::Star;
        while n > 0 {
            k = Kind::Arrow(Box::new([Kind::Star, k]));
            n -= 1;
        }
        k
    }
    pub fn degree(&self) -> usize {
        match self {
            Kind::Star => 0,
            Kind::Arrow(k) => {
                let mut stack = vec![];
                for kx in k.as_ref() {
                    stack.push(kx);
                }
                // stack.reverse();
                let mut deg = 0;
                while let Some(kind) = stack.pop() {
                    deg += 1;
                    if let Kind::Arrow(xy) = kind {
                        stack.extend(xy.as_ref());
                    } else {
                        continue;
                    }
                }
                deg
            }
        }
    }
}

impl Iterator for Kind {
    type Item = Kind;

    fn next(&mut self) -> Option<Self::Item> {
        match std::mem::replace(self, Kind::Star) {
            Kind::Star => None,
            Kind::Arrow(xy) => {
                let [x, y] = *xy;
                *self = y;
                Some(x)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_ty_macro() {
        let vars = (0..10).map(Tv).collect::<Vec<_>>();
        if let [a, b, c, d, e, f, g, h, ..] = vars[..] {
            assert_eq!(
                Ty! { 0 -> 1 -> (2 -> 3) -> #(Foo 4 5 6 7) },
                Type::mk_fun(
                    Type::Var(a),
                    Type::mk_fun(
                        Type::Var(b),
                        Type::mk_fun(
                            Type::mk_fun(Type::Var(c), Type::Var(d)),
                            Type::Con(
                                Con::Data(Ident::Upper(Symbol::from("Foo"))),
                                vec![Type::Var(e), Type::Var(f), Type::Var(g), Type::Var(h)]
                            )
                        )
                    )
                )
            );
            let ty = Ty! { 0 -> 1 -> (2 -> 3) -> #(Foo 4 5 6 7) };
            println!("type: {}", &ty);
            let ty = dbg![ty.simplify_ty()];
            println!("simplified: {}", &ty);
            println!("kind: {}", ty.kind());
            let kinds = ty.kind().clone().collect::<Vec<_>>();
            println!("subkinds: {:?}", kinds);
        } else {
            unreachable!()
        }
    }
}
