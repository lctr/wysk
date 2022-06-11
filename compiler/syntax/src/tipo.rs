use std::{fmt::Write, hash::Hash};

use wy_common::{either::Either, push_if_absent, Map, Mappable};
use wy_intern::{Symbol, Symbolic};

use crate::{decl::Arity, ident::Ident};

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

    pub fn write_str(&self, buf: &mut String) {
        wy_common::text::write_display_var(self.0, buf)
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

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl<Id, T> Con<Id, T> {
    /// If this constructor is not concrete (i.e., is a `Con::Free` variant),
    /// then it returns an option, wrapped with `Some`, containing a reference
    /// to the type variable standing in place of the type constructor.
    /// Otherwise returns `None`.
    pub fn get_var(&self) -> Option<&T> {
        match self {
            Self::Free(t) => Some(t),
            _ => None,
        }
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
        f(wy_intern::COLON)
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
            Con::Alias(id) => Con::Alias(f(id)),
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
            Con::Alias(id) => Con::Alias(f(id)),
        }
    }

    pub fn map_t<X>(self, mut f: impl FnMut(T) -> X) -> Con<Id, X> {
        match self {
            Con::List => Con::List,
            Con::Tuple(n) => Con::Tuple(n),
            Con::Arrow => Con::Arrow,
            Con::Data(id) => Con::Data(id),
            Con::Free(t) => Con::Free(f(t)),
            Con::Alias(id) => Con::Alias(id),
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
            Con::Alias(id) => Con::Alias(*id),
        }
    }
}

impl Con<Ident, Tv> {
    const fn mk_data(symbol: Symbol) -> Con<Ident, Tv> {
        Con::Data(Ident::Upper(symbol))
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
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
    Rec(Record<Type<Id, T>, Id>),
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
        Id: Copy,
        T: Copy,
    {
        Self::mk_list(self.clone())
    }

    #[inline]
    pub fn get_con(&self) -> Option<Con<Id, T>>
    where
        Id: Copy,
        T: Copy,
    {
        match self {
            Type::Var(_) => None,
            Type::Con(c, _) => Some(*c),
            Type::Fun(_, _) => Some(Con::Arrow),
            Type::Tup(ts) => {
                if ts.is_empty() {
                    None
                } else {
                    Some(Con::Tuple(ts.len()))
                }
            }
            Type::Vec(_) => Some(Con::List),
            Type::Rec(r) => r.ctor().map(|id| Con::Data(*id)),
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
        Id: Copy + PartialEq,
    {
        use Con as C;
        use Type as T;
        fn zips<A: Copy + PartialEq, B: Copy + PartialEq>(
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

    pub fn map_id<F, X>(self, f: &mut F) -> Type<X, T>
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

    pub fn map_id_ref<F, X>(&self, f: &mut F) -> Type<X, T>
    where
        F: FnMut(&Id) -> X,
        T: Copy,
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
        F: FnMut(&T) -> U,
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
            Type::Rec(_) => todo!(),
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

    pub fn map_t<U>(self, f: &mut impl FnMut(T) -> U) -> Type<Id, U> {
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
                    Con::Alias(id) => Con::Alias(id),
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
    Id: Copy,
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
}

impl<Id> Type<Id, Tv> {
    /// Like the method `simplify`, this reduces a type in terms of type
    /// variables and type application, but represented with a `Ty` instance
    /// instead of as a `Self` type.
    pub fn simplify_ty(&self) -> Ty<Id>
    where
        Id: Copy,
    {
        match self {
            Type::Var(v) => Ty::Var(*v),
            Type::Con(c, args) => Ty::Con(*c, args.into_iter().map(|t| t.simplify_ty()).collect()),
            Type::Fun(_, _) => todo!(),
            Type::Tup(_) => todo!(),
            Type::Vec(_) => todo!(),
            Type::Rec(_) => todo!(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Ty<Id = Ident> {
    Var(Tv),
    Con(Con<Id, Tv>, Vec<Ty<Id>>),
    App(Box<[Self; 2]>),
}

impl<Id> Default for Ty<Id> {
    fn default() -> Self {
        Ty::Var(Tv(0))
    }
}

impl<Id> Ty<Id> {
    /// Returns a list containing all type variables in a given type in order
    /// **without** duplicates. Use the `vars` method to get a list containing
    /// all type variables with duplicates.
    ///
    /// For example, this method applied to the type `(a, Int, a -> b -> c)`,
    /// which simplifies to `(,,) a Int ((->) a ((->) b c))`, returns the list
    /// `[a, b, c]`.
    pub fn fv(&self) -> Vec<Tv> {
        match self {
            Ty::Var(tv) => vec![*tv],
            Ty::Con(con, args) => {
                // let mut tvs = con.get_var().copied().into_iter().collect::<Vec<_>>();
                args.into_iter().fold(
                    con.get_var().copied().into_iter().collect::<Vec<_>>(),
                    |mut a, c| {
                        for var in c.fv() {
                            if !a.contains(&var) {
                                a.push(var);
                            }
                        }
                        a
                    },
                )
            }
            Ty::App(xy) => {
                let [x, y] = xy.as_ref();
                y.fv().into_iter().fold(x.fv(), push_if_absent)
            }
        }
    }

    #[inline]
    pub fn mk_fun_ty(from_ty: Self, to_ty: Self) -> Self {
        Self::Con(Con::Arrow, vec![from_ty, to_ty])
    }

    /// Given a type `t0` and a (reversible) collection of types `t1`, `t2`,
    /// ..., `tn`, returns the function type `t0 -> (t1 -> (t2 -> ... -> tn))`.
    /// If the collection of types provided is empty, then the initial type `t0`
    /// is returned.
    pub fn maybe_fun(head: Self, rest: impl DoubleEndedIterator + Iterator<Item = Self>) -> Self {
        if let Some(tail) = rest.rev().reduce(|a, c| Self::mk_fun_ty(a, c)) {
            Self::Con(Con::Arrow, vec![head, tail])
        } else {
            head
        }
    }

    pub fn mk_list(list_of: Self) -> Self {
        Self::Con(Con::List, vec![list_of])
    }

    pub fn mk_tuple(tuple_of: Vec<Self>) -> Self {
        Self::Con(Con::Tuple(tuple_of.len()), tuple_of)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Kind {
    Star,
    Arrow(Box<Kind>, Box<Kind>),
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
            Self::Arrow(arg0, arg1) => {
                write!(f, "{:?} -> {:?}", arg0, arg1)
            }
        }
    }
}

impl std::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Star => write!(f, "*"),
            Kind::Arrow(a, b) => write!(f, "{} -> {}", a, b),
        }
    }
}

impl Kind {
    pub fn from_poly(tvs: &[Tv]) -> Self {
        let mut kind = Self::Star;
        for _ in tvs {
            kind = Self::Arrow(Box::new(Self::Star), Box::new(kind));
        }
        kind
    }
    pub fn from_type(ty: &Type) -> Self {
        match ty {
            Type::Var(_) => Self::Star,
            Type::Con(Con::Tuple(0), _) => Self::Star,
            Type::Con(Con::List, t) if t.len() == 1 => {
                Self::Arrow(Box::new(Self::Star), Box::new(Self::from_type(&t[0])))
            }
            Type::Con(_, xs) if xs.is_empty() => Self::Star,
            Type::Con(_, xs) => xs.into_iter().fold(Self::Star, |a, c| {
                Self::Arrow(Box::new(Self::from_type(c)), Box::new(a))
            }),
            Type::Fun(..) => Self::Star,
            Type::Tup(xs) if xs.is_empty() => Self::Star,
            Type::Tup(xs) => Self::Arrow(
                xs.into_iter().fold(Box::new(Self::Star), |a, c| {
                    Box::new(Self::Arrow(a, Box::new(Self::from_type(c))))
                }),
                Box::new(Self::Star),
            ),
            Type::Vec(t) => {
                Self::Arrow(Box::new(Self::Star), Box::new(Self::from_type(t.as_ref())))
            }
            Type::Rec(_) => Self::Star,
        }
    }
    pub fn split(&self) -> Option<(&Self, &Self)> {
        if let Self::Arrow(x, y) = self {
            Some((x.as_ref(), y.as_ref()))
        } else {
            None
        }
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

    /// Returns `None` unless both lhs and rhs are present.
    pub fn as_pair(&self) -> Option<(&Id, &T)> {
        match self {
            Field::Rest => None,
            Field::Key(_) => None,
            Field::Entry(k, v) => Some((k, v)),
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
    pub fn map_id<F, X>(self, mut f: F) -> Context<X, T>
    where
        F: FnMut(Id) -> X,
    {
        Context {
            class: f(self.class),
            head: self.head,
        }
    }
    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> Context<X, T>
    where
        T: Copy,
    {
        Context {
            class: f(&self.class),
            head: self.head,
        }
    }
    pub fn map_t<F, U>(self, mut f: F) -> Context<Id, U>
    where
        F: FnMut(T) -> U,
    {
        Context {
            class: self.class,
            head: f(self.head),
        }
    }
    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Context<Id, U>
    where
        Id: Copy,
    {
        Context {
            class: self.class,
            head: f(&self.head),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
        for Context { class, head: tyvar } in self.ctxt {
            ctxt.push(Context {
                class,
                head: f(tyvar),
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
            each: self.each_iter().map(|t| f(t)).collect(),
            ctxt: self.ctxt_iter().map(|c| c.map_t_ref(f)).collect(),
            tipo: self.tipo.map_t_ref(f),
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
            Type::Fun(x, y) => {
                if x.is_fun() {
                    write!(f, "({})", x)?;
                } else {
                    write!(f, "{}", x)?;
                }
                write!(f, " -> ")?;
                if y.is_fun() {
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
                    $crate::ident::Ident::Upper(wy_intern::intern_once(stringify!($t0)))
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
        ($a0:tt $(, $an:tt)*)
    ) => {{ $crate::tipo::Type::mk_tuple([$a0 $(, $an)*]) }};
    (
        $left:tt -> $($right:tt)+
    ) => {{
        $crate::tipo::Type::mk_fun(
            $crate::Ty! { $left }, $crate::Ty! { $($right)+ }
        )
    }};

}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_ty_macro() {
        let vars = (0..10).map(Tv).collect::<Vec<_>>();
        if let [a, b, c, d, e, f, g, h] = vars[..] {
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
        } else {
            unreachable!()
        }
    }
}
