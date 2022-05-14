use wy_intern::Symbol;

use crate::ident::Ident;

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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context<Id = Ident, T = Ident> {
    pub class: Id,
    /// Defaults to `Tv`, but is parametrized in order to allow for simple
    /// (lowercase) identifiers to be used during parsing (which should then be
    /// *normalized* once the RHS is available so that `T` directly matches any
    /// type variables from the RHS).
    pub tyvar: T,
}

impl<Id, T> Context<Id, T> {
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature<Id = Ident, T = Ident> {
    pub each: Vec<Id>,
    pub ctxt: Vec<Context<Id, T>>,
    pub tipo: Type<Id, T>,
}

impl<Id, T> Signature<Id, T> {
    pub fn map_t<F, U>(self, mut f: F) -> Signature<Id, U>
    where
        F: FnMut(T) -> U,
    {
        let Signature { each, ctxt, tipo } = self;
        let ctxt = ctxt.into_iter().map(|c| c.map_t(|t| f(t))).collect();
        let tipo = tipo.map_t(&mut f);
        Signature { each, ctxt, tipo }
    }
}

/// Represents a type variable.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Tv(pub u32);

impl Tv {
    pub fn incr(&self) -> Self {
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
        Tv(ident.symbol().as_u32())
    }
}

impl From<Symbol> for Tv {
    fn from(sym: Symbol) -> Self {
        Tv::from_symbol(sym)
    }
}

impl std::fmt::Display for Tv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display())
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<Id = Ident, T = Ident> {
    /// Type variables. These use their own special inner type `Tv`, which is a
    /// newtype wrapper around a `u32`.
    Var(T),
    /// Type constructors. Note that a `Con` variant may NOT have a type
    /// variable as the cosnstructor. For polymorphism over a constructor, use
    /// the `App` variant.
    Con(Id, Vec<Type<Id, T>>),
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
    Fun(Box<Type<Id, T>>, Box<Type<Id, T>>),
    Tup(Vec<Type<Id, T>>),
    Vec(Box<Type<Id, T>>),
    Rec(Record<Type<Id, T>, Id>),
    App(Box<Type<Id, T>>, Box<Type<Id, T>>),
}

// impl<Id> std::fmt::Debug for Type<Id> {}
impl<Id: std::fmt::Display, T: std::fmt::Display> std::fmt::Display for Type<Id, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Var(tv) => write!(f, "{}", tv),
            Type::Con(con, args) => {
                if args.is_empty() {
                    write!(f, "{}", con)
                } else {
                    write!(f, "({}", con)?;
                    for arg in args {
                        write!(f, " {}", arg)?;
                    }
                    write!(f, ")")
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
                        // for typed records, we should expect both lhs (keys) and
                        // rhs (types)
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
            Type::App(c, d) => {
                write!(f, "{} {}", c, d)
            }
        }
    }
}

impl<Id, T> Type<Id, T> {
    pub const UNIT: Self = Self::Tup(vec![]);

    pub fn map_t<F, U>(self, f: &mut F) -> Type<Id, U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Type::Var(t) => Type::Var(f(t)),
            Type::Con(c, ts) => Type::Con(c, ts.into_iter().map(|ty| ty.map_t(f)).collect()),
            Type::Fun(x, y) => Type::Fun(Box::new(x.map_t(f)), Box::new(y.map_t(f))),
            Type::Tup(tys) => Type::Tup(tys.into_iter().map(|ty| ty.map_t(f)).collect::<Vec<_>>()),
            Type::Vec(ty) => Type::Vec(Box::new(ty.map_t(f))),
            Type::Rec(rs) => Type::Rec(rs.map_t(|ty| ty.map_t(f))),
            Type::App(x, y) => Type::App(Box::new(x.map_t(f)), Box::new(y.map_t(f))),
        }
    }

    pub fn is_func(&self) -> bool {
        matches!(self, Self::Fun(..))
    }

    pub fn un_app(&self) -> Option<(&Self, &Self)> {
        if let Self::App(c, d) = self {
            Some((c.as_ref(), d.as_ref()))
        } else {
            None
        }
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
            Type::Con(id, args) if args.is_empty() => Some(id),
            _ => None,
        }
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
            Type::App(x, y) => {
                for tv in x.fv().into_iter().chain(y.fv()) {
                    if !fvs.contains(&tv) {
                        fvs.push(tv)
                    }
                }
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
    pub fn enumerate(&self) -> impl Iterator<Item = (T, Tv)>
    where
        T: Copy + Eq,
    {
        let vars = self.fv();
        let w = vars.len();
        vars.iter()
            .fold(Vec::with_capacity(w), |a, c| {
                let mut acc = a;
                if acc.contains(c) {
                    acc
                } else {
                    acc.push(*c);
                    acc
                }
            })
            .into_iter()
            .enumerate()
            .map(|(v, tv)| (tv, Tv(v as u32)))
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
        f(wy_intern::intern_once(":"))
    }

    /// Like with the list constructor `:`, the tuple constructor must also be
    /// processed to match the type used to represent identifiers. However,
    /// unlike the list constructor, which is used for *all* lists, tuples
    /// require a new constructor depending on the number of type components
    /// held. Namely, the constructor for a tuple with `N` elements is the
    /// lexeme formed by combining `N - 1` commas and surrounding them in
    /// parentheses.
    pub fn n_tuple_id(commas: usize, mut f: impl FnMut(Symbol) -> Id) -> Id {
        let ntup = (1..(2 + commas)).map(|_| ',').collect::<String>();
        f(wy_intern::intern_once(&*ntup))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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

    pub fn map_t<F, U>(self, mut f: F) -> Record<U, Id>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Record::Anon(es) => Record::Anon(
                es.into_iter()
                    .map(|e| e.map_t(|t| f(t)))
                    .collect::<Vec<_>>(),
            ),
            Record::Data(k, v) => Record::Data(
                k,
                v.into_iter().map(|v| v.map_t(|t| f(t))).collect::<Vec<_>>(),
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
}
