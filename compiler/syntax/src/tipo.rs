use std::fmt;
use std::{fmt::Write, hash::Hash};

use serde::{Deserialize, Serialize};

use wy_common::functor::PipeF;
use wy_common::Set;
use wy_common::{either::Either, Map};
// use wy_common::Mappable;
use wy_intern::{Symbol, Symbolic};
use wy_name::ident::{Ident, Identifier};
pub use wy_name::Tv;

use crate::decl::Arity;
use crate::SpannedIdent;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Var<Id, V = Tv>(pub Id, pub V);

pub type TVar = Var<Ident>;

impl<Id, V> Var<Id, V> {
    pub fn new(id: Id) -> Var<Id> {
        Var(id, Tv(0))
    }

    pub fn from_pair((id, tv): (Id, V)) -> Self {
        Self(id, tv)
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

    pub fn head_ref(&self) -> &Id {
        &self.0
    }

    pub fn head_mut(&mut self) -> &mut Id {
        &mut self.0
    }

    #[inline]
    pub fn tail(self) -> V {
        self.1
    }

    pub fn tail_ref(&self) -> &V {
        &self.1
    }

    pub fn tail_mut(&mut self) -> &mut V {
        &mut self.1
    }

    pub fn as_pair(self) -> (Id, V) {
        (self.0, self.1)
    }

    pub fn replace_tail(&mut self, tv: V) -> V {
        std::mem::replace(&mut self.1, tv)
    }

    pub fn replace_head(&mut self, id: Id) -> Id {
        std::mem::replace(&mut self.0, id)
    }
}

impl<Id: fmt::Debug, V> fmt::Debug for Var<Id, V>
where
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Var({:?}, {:?})", &self.0, &self.1)
    }
}
impl<Id: fmt::Display, V> fmt::Display for Var<Id, V>
where
    V: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.[{}]", &self.0, &self.1)
    }
}

impl<V> std::ops::Deref for Var<V> {
    type Target = Tv;

    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

impl<Id> std::borrow::Borrow<Tv> for Var<Id> {
    fn borrow(&self) -> &Tv {
        self.tail_ref()
    }
}

impl<Id> std::borrow::BorrowMut<Tv> for Var<Id> {
    fn borrow_mut(&mut self) -> &mut Tv {
        self.tail_mut()
    }
}

impl<V> From<(V, Tv)> for Var<V> {
    fn from((t, tv): (V, Tv)) -> Self {
        Var(t, tv)
    }
}

impl<X, V> Extend<Var<X, V>> for Map<X, V>
where
    X: Eq + Hash,
{
    fn extend<I: IntoIterator<Item = Var<X, V>>>(&mut self, iter: I) {
        for Var(t, tv) in iter {
            self.insert(t, tv);
        }
    }
}

impl<X, V> Extend<Var<X, V>> for Vec<(X, V)> {
    fn extend<I: IntoIterator<Item = Var<X, V>>>(&mut self, iter: I) {
        for Var(t, tv) in iter {
            self.push((t, tv));
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Con<Id = SpannedIdent, V = SpannedIdent> {
    /// List constructor `[]`; arity = 1
    List,
    /// Tuple constructor(s) of provided arity. A value of 0 is taken to refer
    /// to the empty tuple unit type `()`.
    Tuple(usize),
    /// Function constructor `(->)`; arity = 2
    Arrow,
    /// User-defined type constructor
    Named(Id),
    Varied(V),
}

impl<Id, V> Con<Id, V> {
    pub fn map_id<U>(self, f: impl FnOnce(Id) -> U) -> Con<U, V> {
        match self {
            Con::List => Con::List,
            Con::Tuple(n) => Con::Tuple(n),
            Con::Arrow => Con::Arrow,
            Con::Named(id) => Con::Named(f(id)),
            Con::Varied(t) => Con::Varied(t),
        }
    }

    pub fn map_t<W>(self, f: impl FnOnce(V) -> W) -> Con<Id, W> {
        match self {
            Con::List => Con::List,
            Con::Tuple(n) => Con::Tuple(n),
            Con::Arrow => Con::Arrow,
            Con::Named(id) => Con::Named(id),
            Con::Varied(t) => Con::Varied(f(t)),
        }
    }

    pub fn map_t_ref<W>(&self, f: impl FnOnce(&V) -> W) -> Con<Id, W>
    where
        Id: Clone,
    {
        match self {
            Con::List => Con::List,
            Con::Tuple(n) => Con::Tuple(*n),
            Con::Arrow => Con::Arrow,
            Con::Named(id) => Con::Named(id.clone()),
            Con::Varied(t) => Con::Varied(f(t)),
        }
    }
    pub fn as_ref(&self) -> Con<&Id, &V> {
        match self {
            Con::List => Con::List,
            Con::Tuple(n) => Con::Tuple(*n),
            Con::Arrow => Con::Arrow,
            Con::Named(id) => Con::Named(id),
            Con::Varied(v) => Con::Varied(v),
        }
    }
}

impl<Id: Symbolic> Symbolic for Con<Id, Tv> {
    fn get_symbol(&self) -> Symbol {
        match self {
            Con::List => wy_intern::sym::COLON,
            Con::Tuple(ts) => {
                let s = std::iter::repeat(',').take(*ts).collect::<String>();
                Symbol::intern(&*s)
            }
            Con::Arrow => wy_intern::sym::ARROW,
            Con::Named(s) => s.get_symbol(),
            Con::Varied(t) => Symbol::intern(&*t.display()),
        }
    }
}

wy_common::variant_preds! {
    |Id, V| Con[Id, V]
    | is_list => List
    | is_tuple => Tuple(_)
    | is_unit => Tuple(xs) [if *xs == 0]
    | is_arrow => Arrow
    | is_data => Named(_)
    | is_free => Varied(_)
}

impl<S: Identifier + Symbolic> PartialEq<S> for Con<Ident, Tv> {
    fn eq(&self, other: &S) -> bool {
        match (self, other) {
            (Con::List, c) => c.get_symbol() == wy_intern::sym::COLON,
            (Con::Tuple(n), c) => c
                .get_symbol()
                .as_str()
                .pipe(|s| s.len() == *n && s.chars().all(|c| c == ',')),
            (Con::Arrow, c) => c.get_symbol() == wy_intern::sym::ARROW,
            (Con::Named(c), id) => id.get_symbol() == c.get_symbol(),
            (Con::Varied(Tv(n)), s) => {
                matches!(s.get_ident(), Ident::Fresh(m) if m == *n)
            }
        }
    }
}

impl Con<Ident, Tv> {
    const fn mk_data(symbol: Symbol) -> Con<Ident, Tv> {
        Con::Named(Ident::Upper(symbol))
    }

    pub fn from_ident(ident: Ident) -> Self {
        if let Ident::Fresh(n) = ident {
            Con::Varied(Tv(n))
        } else if let Some(n) = ident.comma_count() {
            Con::Tuple(n)
        } else if ident.is_cons_sign() {
            Con::List
        } else if ident.is_arrow() {
            Con::ARROW
        } else {
            Con::Named(ident)
        }
    }

    pub const ARROW: Self = Self::mk_data(wy_intern::sym::ARROW);
    pub const BOOL: Self = Self::mk_data(wy_intern::sym::BOOL);
    pub const INT: Self = Self::mk_data(wy_intern::sym::INT);
    pub const NAT: Self = Self::mk_data(wy_intern::sym::NAT);
    pub const FLOAT: Self = Self::mk_data(wy_intern::sym::FLOAT);
    pub const DOUBLE: Self = Self::mk_data(wy_intern::sym::DOUBLE);
    pub const BYTE: Self = Self::mk_data(wy_intern::sym::BYTE);
    pub const CHAR: Self = Self::mk_data(wy_intern::sym::CHAR);
    pub const STR: Self = Self::mk_data(wy_intern::sym::STR);
    pub const IO: Self = Self::mk_data(wy_intern::sym::IO);
    pub const HOLE: Self = Self::mk_data(wy_intern::sym::WILD);
}

impl<Id: fmt::Debug, V: fmt::Debug> fmt::Debug for Con<Id, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::List => write!(f, "[]"),
            Self::Tuple(n) => (0..=*n)
                .fold(write!(f, "("), |a, _| a.and(write!(f, ",")))
                .and(write!(f, ")")),
            Self::Arrow => write!(f, "(->)"),
            Self::Named(con) => Id::fmt(con, f),
            Self::Varied(var) => V::fmt(var, f),
        }
    }
}

impl<Id: fmt::Display, V: fmt::Display> fmt::Display for Con<Id, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Con::List => write!(f, "[]"),
            Con::Tuple(ns) => {
                f.write_char('(')?;
                for _ in 0..(*ns) {
                    f.write_char(',')?;
                }
                f.write_char(')')
            }
            Con::Arrow => f.write_str("(->)"),
            Con::Named(id) => write!(f, "{}", id),
            Con::Varied(v) => write!(f, "{}", v),
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
pub enum Type<Id = SpannedIdent, V = SpannedIdent> {
    /// Type variables. These use their own special inner type `Tv`, which is a
    /// newtype wrapper around a `u32`.
    Var(V),
    /// Type constructor applications.
    Con(Con<Id, V>, Vec<Type<Id, V>>),
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
    Fun(Box<Type<Id, V>>, Box<Type<Id, V>>),
    Tup(Vec<Type<Id, V>>),
    Vec(Box<Type<Id, V>>),
}

wy_common::variant_preds! {
    |Id, V| Type[Id, V]
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
    | is_con_var => Con(Con::Varied(_), _)
    | is_concrete_con => Con(Con::Named(_), _)
    | is_alias_con => Con(Con::Varied(_), _)
}

impl<Id, V> Type<Id, V> {
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
    pub fn mk_app(ty_con: Con<Id, V>, ty_args: impl IntoIterator<Item = Self>) -> Self {
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
    pub fn mk_var(tyvar: V) -> Self {
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
        V: Copy,
    {
        Self::mk_list(self.clone())
    }

    #[inline]
    pub fn get_con(&self) -> Option<Con<Id, V>>
    where
        Id: Clone,
        V: Copy,
    {
        match self {
            Type::Var(_) => None,
            Type::Con(c, _) => Some(c.clone()),
            Type::Fun(_, _) => Some(Con::Arrow),
            Type::Tup(ts) => {
                if ts.is_empty() {
                    None
                } else {
                    Some(Con::Tuple(ts.len() - 1))
                }
            }
            Type::Vec(_) => Some(Con::List),
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
    /// ```wysk
    ///     a -> b -> c -> d
    /// ```
    /// which is parsed as
    /// ```wysk
    ///     a -> (b -> (c -> d))
    /// ```
    /// this method returns the list
    /// ```wysk
    ///     [a, b, c, d]
    /// ```
    /// If the type corresponding to `Self` is not a function type, then a
    /// single-element vector containing the `Self` type instance is returned.
    /// Thus, this method returns vectors of length > 1 for function types. The
    /// method `maybe_fun_vec` returns instead an `Either<Type, Vec<Type>>`
    /// instance as an alternative to this functionality.
    ///
    /// Note however that this does not have a "flattening" effect: the type
    /// ```wysk
    ///     (a -> b) -> (c -> (d -> e)) -> f
    /// ```
    /// with this method applied, would return
    /// ```wysk
    ///     [(a -> b), (c -> (d -> e)), f]
    /// ```
    /// while the function type
    /// ```wysk
    ///     (a -> b) -> c -> d -> (e -> f)
    /// ```
    /// would return
    /// ```wysk
    ///     [(a -> b), c, d, e, f]
    /// ```
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
    pub fn pre_simplify(self) -> Self {
        match self {
            a @ Type::Var(_) => a,
            Type::Con(con, args) => {
                Type::Con(con, args.into_iter().map(|ty| ty.pre_simplify()).collect())
            }
            Type::Fun(t1, t2) => Type::Con(Con::Arrow, vec![t1.pre_simplify(), t2.pre_simplify()]),
            Type::Tup(ts) => Type::Con(
                Con::Tuple(ts.len() - 1),
                ts.into_iter().map(|t| t.pre_simplify()).collect(),
            ),
            Type::Vec(t) => Type::Con(Con::List, vec![t.pre_simplify()]),
        }
    }

    pub fn contains_constructor(&self, con: &Con<Id, V>) -> bool
    where
        Id: PartialEq,
        V: PartialEq,
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
        }
    }

    /// Identifies whether this `Type` is polymorphic over the given type
    /// variable. Equivalently, this method tests for containment of the given
    /// variable of type `V`.
    pub fn depends_on(&self, var: &V) -> bool
    where
        V: PartialEq,
    {
        match self {
            Type::Var(t) => var == t,
            Type::Con(_, ts) | Type::Tup(ts) => ts.iter().any(|ty| ty.depends_on(var)),
            Type::Fun(x, y) => x.depends_on(var) || y.depends_on(var),
            Type::Vec(t) => t.depends_on(var),
        }
    }

    /// Tests whether a given type contains another type.
    pub fn contains(&self, subty: &Type<Id, V>) -> bool
    where
        Id: PartialEq,
        V: PartialEq,
    {
        match self {
            ty @ Type::Var(_) => ty == subty,
            Type::Fun(x, y) => x.contains(subty) || y.contains(subty),
            Type::Con(_, tys) | Type::Tup(tys) => tys.iter().any(|ty| ty.contains(subty)),
            Type::Vec(t) => t.contains(subty),
        }
    }

    /// If a given type is a nullary type, then this will return a reference to
    /// the identifier represemting the nullary type constructor.
    pub fn id_if_nullary(&self) -> Option<&Id> {
        match self {
            Type::Con(Con::Named(id), args) if args.is_empty() => Some(id),
            _ => None,
        }
    }

    /// Returns a list of references to all the free variables in the order in which they
    /// appear with duplicates included.
    pub fn vars(&self) -> Vec<&V> {
        let mut vars = vec![];
        match self {
            Type::Var(v) => vars.push(v),
            Type::Con(Con::Varied(v), args) => {
                vars.push(v.clone());
                args.into_iter().for_each(|ty| vars.append(&mut ty.vars()));
            }
            Type::Con(_, args) => args.into_iter().for_each(|ty| vars.append(&mut ty.vars())),
            Type::Fun(x, y) => {
                vars.append(&mut x.vars());
                vars.append(&mut y.vars());
            }
            Type::Tup(args) => args.into_iter().for_each(|ty| vars.append(&mut ty.vars())),
            Type::Vec(t) => vars.append(&mut t.vars()),
        };
        vars
    }

    /// Returns a list (= vector) of references to all type variables
    /// in the order they were encountered without repetition. This
    /// method is slower than the method `fv` as it doesn't rely on
    /// `O(1)` lookup type afforded by hashing.
    pub fn vs(&self) -> Vec<&V>
    where
        V: PartialEq,
    {
        use wy_common::push_if_absent as push_unique;
        match self {
            Type::Var(t) => vec![t],
            Type::Con(_, args) => args
                .into_iter()
                .flat_map(Self::vs)
                .fold(vec![], push_unique),
            Type::Fun(x, y) => x.vs().into_iter().chain(y.vs()).fold(vec![], push_unique),
            Type::Tup(ts) => ts.into_iter().flat_map(Self::vs).fold(vec![], push_unique),
            Type::Vec(t) => t.vs(),
        }
    }

    /// Returns a set containing all type variables in a given type in
    /// order without repetition as an `IndexSet`.
    /// For example, this method applied to the type `(a, Int, a -> b -> c)`
    /// returns the vector `{a, b, c}`.
    pub fn fv(&self) -> Set<V>
    where
        V: Clone + Eq + std::hash::Hash,
    {
        let mut fvs = Set::new();
        match self {
            Type::Var(a) => {
                fvs.insert(a.clone());
            }
            Type::Con(Con::Varied(t), ts) => {
                // is `m` in `m a` a type variable since it's also a
                // constructor? or is it simply generic?
                fvs.insert(t.clone());
                ts.into_iter().flat_map(|ty| ty.fv()).for_each(|tv| {
                    fvs.insert(tv);
                })
            }
            Type::Con(_, ts) | Type::Tup(ts) => {
                ts.into_iter().flat_map(|ty| ty.fv()).for_each(|tv| {
                    fvs.insert(tv);
                });
            }
            Type::Fun(ta, tb) => {
                fvs.extend(ta.fv());
                fvs.extend(tb.fv());
            }
            Type::Vec(ty) => {
                fvs.extend(ty.fv());
            }
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
    pub fn enumerate(&self) -> impl Iterator<Item = Var<V>>
    where
        V: Clone + Eq + std::hash::Hash,
    {
        let vars = self.fv();
        // vars.dedup();
        vars.into_iter().zip(0..).map(|(v, n)| Var(v, Tv(n)))
    }

    /// If the second type parameter implements `Symbolic`, and `Id`
    /// is `Copy`, returns a new copy of the type where the second
    /// type parameter becomes a `Symbol`. This establishes a common
    /// type amongst possible parametrizations; when aiming to convert
    /// the second type parameter `V` to the standard `Tv`, we first
    /// map to `Symbol`s since `Symbol`s and `Tv`s are both newtypes
    /// around 32-bit integers. While a `Symbol` can *not* be
    /// constructed manually, its internal `u32` value is accessible
    /// and `Tv`s can be generated from said integer value.
    ///
    /// Leaving it at this step is fine, but visually will present
    /// some odd textual representations of the newly generated `Tv`
    /// type variable; thus, after mapping from `V` -> `Symbol` ->
    /// `Tv`, we (re)-enumerate the type variables `Tv` to generate a
    /// key-value pair (of `Tv`s to `Tv`s) -- the iterator for which
    /// can be partially generated using the `enumerate` method --
    /// with the old `Tv`s as keys and newly reordered/generated `Tv`s
    /// as values.
    ///
    /// Lastly, the top-most structure that's *not* a type (like a
    /// `Signature`, `Quantified`, or `Qualified` struct) **MUST** be
    /// the entry point for this: *all* type variable key-value pairs
    /// *must* exist in the map, otherwise a type variable is not
    /// substituted and our surjection fails -- statically enforced
    /// not by unwrapping map lookup results but by instead relying on
    /// the use of `std::ops::Index<Tv>` for `Map<Tv, Tv>` lookups;
    /// additionally, the top-level structure containing type
    /// variables of its own (shared by the type) must also update its
    /// paramterized type variable representation to match (otherwise
    /// we'd have, say, type variables in a predicate that used to
    /// exist within the type but no longer match!).
    ///
    /// This workflow spans across the methods `var_to_sym`,
    /// `enumerate`, `fv` (via `enumerate`), and `rename_vars`.
    pub fn var_to_sym(&self) -> Type<Id, Symbol>
    where
        Id: Copy,
        V: Symbolic,
    {
        match self {
            Type::Var(tv) => Type::Var(tv.get_symbol()),
            Type::Con(con, args) => {
                let con = match con {
                    Con::List => Con::List,
                    Con::Tuple(n) => Con::Tuple(*n),
                    Con::Arrow => Con::Arrow,
                    Con::Named(id) => Con::Named(*id),
                    Con::Varied(v) => Con::Varied(v.get_symbol()),
                };
                let args = args.into_iter().map(Self::var_to_sym).collect();
                Type::Con(con, args)
            }
            Type::Fun(x, y) => Type::Fun(Box::new(x.var_to_sym()), Box::new(y.var_to_sym())),
            Type::Tup(ts) => Type::Tup(ts.into_iter().map(Self::var_to_sym).collect()),
            Type::Vec(t) => Type::Vec(Box::new(t.var_to_sym())),
        }
    }

    pub fn normalize(self, subst: &Map<V, Tv>) -> Type<Id, Tv>
    where
        Id: Copy,
        V: Eq + Hash,
    {
        match self {
            Type::Var(ref tv) => Type::Var(subst[tv]),
            Type::Con(con, args) => Type::Con(
                con.map_t(|ref t| subst[t]),
                args.into_iter().map(|ty| ty.normalize(subst)).collect(),
            ),
            Type::Fun(x, y) => {
                Type::Fun(Box::new(x.normalize(subst)), Box::new(y.normalize(subst)))
            }
            Type::Tup(ts) => Type::Tup(ts.into_iter().map(|ty| ty.normalize(subst)).collect()),
            Type::Vec(t) => Type::Vec(Box::new(t.normalize(subst))),
        }
    }
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

impl<Id, V> fmt::Display for Type<Id, V>
where
    Id: fmt::Display,
    V: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
        }
    }
}

/// The left-hand side of a type alias, newtype or class declaration.
///
/// A `SimpleType` consists of a type constructor followed by a flat
/// sequence of type variables (which may be empty) and hence always
/// have the form `C t1 t2 ... tn`, where `t1`, `t2`, ..., etc., are
/// optional but must be *distinct* type variables. In other words, a
/// simple type is the type application of a single type constructor
/// with arbitrarily many non-repeated type variables.
///
/// For example, the type `Foo a b` is a simple type, as well as
/// `Bool` and `Bar baz boo`, but **not** `(a, b)`, `[a]`, `Foo (Bar
/// a) baz`, etc.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SimpleType<Id = SpannedIdent, V = SpannedIdent>(pub Id, pub Vec<V>);

impl<Id, V> SimpleType<Id, V> {
    pub fn new(tycon_id: Id, tyvars: Vec<V>) -> Self {
        SimpleType(tycon_id, tyvars)
    }

    pub const fn new_nullary(tycon_id: Id) -> Self {
        SimpleType(tycon_id, Vec::new())
    }

    pub fn con(&self) -> &Id {
        &self.0
    }

    pub fn vars(&self) -> &[V] {
        &self.1
    }

    #[inline]
    pub fn len_vars(&self) -> usize {
        self.1.len()
    }

    #[inline]
    /// Returns `true` if it has no type variables, otherwise it
    /// `false`.
    pub fn is_nullary(&self) -> bool {
        self.1.is_empty()
    }

    #[inline]
    pub fn contains_var(&self, tyvar: &V) -> bool
    where
        V: PartialEq,
    {
        self.1.contains(tyvar)
    }

    #[inline]
    pub fn vars_iter(&self) -> std::slice::Iter<'_, V> {
        self.1.iter()
    }

    #[inline]
    pub fn vars_iter_mut(&mut self) -> std::slice::IterMut<'_, V> {
        self.1.iter_mut()
    }

    pub fn no_dupe_vars(&self) -> bool
    where
        V: PartialEq,
    {
        self.len_vars()
            == self
                .vars_iter()
                .fold(
                    Vec::with_capacity(self.len_vars()),
                    wy_common::push_if_absent,
                )
                .len()
    }
}

impl<Id, V> fmt::Display for SimpleType<Id, V>
where
    Id: fmt::Display,
    V: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.0)?;
        for v in &self.1 {
            write!(f, " {v}")?;
        }
        Ok(())
    }
}

/// A parameter for `Predicate`s. This should *generally* be a single
/// type variable, but it is possible for it to be a generic type
/// application while still being valid (= in head-normal form), such
/// as in the predicate `|Eq (m a)|`.
///
/// It is a syntax error for a `Parameter` to contain any non-variable
/// constructors; this can be seen in the type parametrization of the
/// `Parameter` type, which does not depend on constructor identifiers
/// like most AST nodes, e.g., `Type<Id, V>` uses `Id` for fixed
/// constructor identifiers and `V` for type variables (as well as the
/// the case of a generic constructor).
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Parameter<V = SpannedIdent>(pub V, pub Vec<V>);

impl<V> Parameter<V> {
    pub fn iter(&self) -> impl Iterator<Item = &V> + '_ {
        std::iter::once(&self.0).chain(self.1.iter())
    }

    pub fn mapf<F, X>(self, f: &mut wy_common::functor::Func<'_, F>) -> Parameter<X>
    where
        F: FnMut(V) -> X,
    {
        let Parameter(head, tail) = self;
        let head = f.apply(head);
        let tail = tail.into_iter().map(|v| f.apply(v)).collect();
        Parameter(head, tail)
    }
}

/// A `Predicate` encodes what *type constraints* a given *type
/// variable* must adhere to in the following type signature. A
/// `Predicate` always appears as an element in a sequence of other
/// `Predicate`s enclosed by a single pipe `|`, and must precede a
/// `Type`.
///
/// For example, the following type signature contains *two*
/// `Predicate`s corresponding to two type variables `a` and `b`,
/// where, for some given typeclasses `A` and `B`, `a` is constrained
/// (= required to be a member of) the typeclass `A`, and `b` is
/// constrained to `B`.
/// ```wysk
/// ~~> Predicate 1
/// ~~|  vvv
///     |A a, B b| (a, b)
/// ~~:       ^^^  
/// ~~:  Predicate 2
/// ~~: ^--------^
/// ~~: Predicate 1 and Predicate 2, surrounded by `|` and followed by the type `(a, b)`
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Predicate<Id = SpannedIdent, V = SpannedIdent> {
    /// The name of the type class for which this holds
    pub class: Id,
    /// Type that must be a member of the class in the `class` field
    pub head: Parameter<V>,
}

impl<Id, V> Predicate<Id, V> {
    pub fn class(&self) -> &Id {
        &self.class
    }
    pub fn head(&self) -> &Parameter<V> {
        &self.head
    }
    pub fn tyvars(&self) -> impl Iterator<Item = &V> + '_ {
        self.head.iter()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Qualified<Id = SpannedIdent, V = SpannedIdent> {
    pub pred: Vec<Predicate<Id, V>>,
    pub tipo: Type<Id, V>,
}

impl<Id, V> Qualified<Id, V> {
    pub fn pred_iter(&self) -> std::slice::Iter<'_, Predicate<Id, V>> {
        self.pred.iter()
    }
    pub fn pred_iter_mut(&mut self) -> std::slice::IterMut<'_, Predicate<Id, V>> {
        self.pred.iter_mut()
    }
    pub fn vars(&self) -> impl Iterator<Item = &V> + '_ {
        // todo!()
        self.pred_iter()
            .flat_map(|pred| pred.head().iter())
            .chain(self.tipo.vars())
    }
}

/// Quantified variables, referring to explicitly quantified (type)
/// variables in source code such as `foo :: forall a b . a -> b`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Quantified<Id = SpannedIdent, V = Tv>(pub Vec<Var<Id, V>>);

impl<X, V> Default for Quantified<X, V> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<Id, V> Quantified<Id, V> {
    pub const EMPTY: Self = Self::new();

    pub const fn new() -> Self {
        Self(Vec::new())
    }

    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        Quantified(Vec::with_capacity(cap))
    }

    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, Var<Id, V>> {
        self.0.iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, Var<Id, V>> {
        self.0.iter_mut()
    }

    #[inline]
    pub fn into_iter(self) -> std::vec::IntoIter<Var<Id, V>> {
        self.0.into_iter()
    }

    pub fn tvs(&self) -> impl Iterator<Item = &V> + '_ {
        self.iter().map(|Var(_, tv)| tv)
    }

    pub fn ids(&self) -> impl Iterator<Item = &Id> + '_ {
        self.iter().map(|Var(x, _)| x)
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<X> Quantified<X> {
    pub fn max_tv(&self) -> Tv {
        self.iter()
            .map(|Var(_, Tv(n))| n)
            .max()
            .map(|n| Tv(*n))
            .unwrap_or_else(|| Tv(0))
    }
    pub fn min_tv(&self) -> Tv {
        self.iter()
            .map(|Var(_, Tv(n))| n)
            .min()
            .map(|n| Tv(*n))
            .unwrap_or_else(|| Tv(0))
    }

    #[inline]
    pub fn tv_bounds(&self) -> (Tv, Tv) {
        (self.min_tv(), self.max_tv())
    }

    pub fn contains_tv(&self, tv: &Tv) -> bool {
        self.iter().any(|Var(_, vt)| tv == vt)
    }

    /// Returns the `Tv` greater than the maximum `Tv` currently contained.
    pub fn tv_supremum(&self) -> Tv {
        Tv(self.max_tv().0 + 1)
    }

    pub fn push_fresh(&mut self, item: X) -> &mut Var<X> {
        let len = self.len();
        self.0.push(Var(item, self.tv_supremum()));
        &mut self.0[len]
    }
}

impl<X> IntoIterator for Quantified<X> {
    type Item = Var<X>;

    type IntoIter = std::vec::IntoIter<Var<X>>;

    fn into_iter(self) -> Self::IntoIter {
        Quantified::into_iter(self)
    }
}

impl<'a, X> IntoIterator for &'a Quantified<X> {
    type Item = &'a Var<X>;

    type IntoIter = std::slice::Iter<'a, Var<X>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<X> FromIterator<X> for Quantified<X> {
    fn from_iter<T: IntoIterator<Item = X>>(iter: T) -> Self {
        Quantified(
            iter.into_iter()
                .enumerate()
                .map(|(n, x)| Var(x, Tv(n as u32)))
                .collect(),
        )
    }
}

impl<X, V> FromIterator<(X, V)> for Quantified<X, V> {
    fn from_iter<T: IntoIterator<Item = (X, V)>>(iter: T) -> Self {
        Self(iter.into_iter().map(|(x, v)| Var(x, v)).collect())
    }
}

impl<X, V> FromIterator<Var<X, V>> for Quantified<X, V> {
    fn from_iter<T: IntoIterator<Item = Var<X, V>>>(iter: T) -> Self {
        Quantified(Vec::from_iter(iter))
    }
}

impl fmt::Display for Quantified<()> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            Ok(())
        } else {
            write!(f, "forall")?;
            for Var(_, tv) in self {
                write!(f, " {tv}")?;
            }
            write!(f, ". ")
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Annotation<Id = SpannedIdent, V = SpannedIdent> {
    pub quant: Quantified<Id, V>,
    pub qual: Qualified<Id, V>,
}

impl<Id, V> Annotation<Id, V> {
    pub fn constrains(&self, tvar: &V) -> bool
    where
        V: PartialEq,
    {
        self.qual
            .pred_iter()
            .any(|pred| pred.head.iter().any(|v| v == tvar))
    }
}

/// An explicit type signature corresponds to the type annotation found in
/// source code and is never overwritten (only isomorphically modified
/// in terms of representation), but rather used as a reference with
/// which type inference and checking is unified in later phases. This
/// contrasts with an `Annotation`, which holds the same data as the
/// `Signature::Explicit` variant and is used when explicit type
/// signatures are *required*, such as in class declarations.
///
/// Note that whether a type signature is implicit or explicit does not
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
pub enum Signature<Id = SpannedIdent, V = SpannedIdent> {
    Implicit,
    Explicit(Annotation<Id, V>),
}

wy_common::variant_preds! {
    |Id, V| Signature[Id, V]
    | is_implicit => Implicit
    | is_explicit => Explicit (_)
    | is_quantified => Explicit (Annotation { quant, ..}) [if !quant.is_empty()]
}

impl<Id, V> Signature<Id, V> {
    pub fn qualified(&self) -> Option<&Qualified<Id, V>> {
        if let Self::Explicit(Annotation { qual: sig, .. }) = self {
            Some(sig)
        } else {
            None
        }
    }

    pub fn quantified(&self) -> Option<&Quantified<Id, V>> {
        if let Self::Explicit(Annotation { quant, .. }) = self {
            Some(quant)
        } else {
            None
        }
    }

    pub fn tyvars(&self) -> impl Iterator<Item = &V> + '_ {
        let qual = self
            .qualified()
            .into_iter()
            .flat_map(|qual| qual.vars())
            .map(|v| v);
        let quant = self
            .quantified()
            .into_iter()
            .flat_map(|quant| quant.tvs())
            .map(|v| v);
        qual.chain(quant)
    }

    pub fn quantified_ids(&self) -> impl Iterator<Item = &Id> + '_ {
        self.quantified().into_iter().flat_map(Quantified::ids)
    }
}
