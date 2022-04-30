pub mod fixity;
pub mod visit;

use std::rc::Rc;

use wy_common::{text, Map};
use wy_intern::symbol::Symbol;
use wy_lexer::Literal;

use fixity::*;

// TODO: documentation; potential split-up of definitions into separate files?

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Ident {
    Upper(Symbol),
    Lower(Symbol),
    Infix(Symbol),
}

impl std::fmt::Debug for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Upper(arg0) => write!(f, "Upper({})", arg0),
            Self::Lower(arg0) => write!(f, "Lower({})", arg0),
            Self::Infix(arg0) => write!(f, "Infix({})", arg0),
        }
    }
}

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.get_symbol())
    }
}

impl Ident {
    pub fn get_symbol(&self) -> Symbol {
        match self {
            Self::Upper(s) | Self::Lower(s) | Self::Infix(s) => *s,
        }
    }
    pub fn is_upper(&self) -> bool {
        matches!(self, Self::Upper(..))
    }
    pub fn is_lower(&self) -> bool {
        matches!(self, Self::Lower(..))
    }
    pub fn is_infix(&self) -> bool {
        matches!(self, Self::Infix(..))
    }
}

wy_common::newtype!({ u64 in Uid | Show (+= usize |rhs| rhs as u64) });

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program<Id = Ident> {
    pub modules: Vec<Module<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module<Id = Ident> {
    pub modname: Id,
    pub imports: Vec<ImportDecl<Id>>,
    pub datatys: Vec<DataDecl<Id>>,
    pub classes: Vec<ClassDecl<Id>>,
    pub implems: Vec<InstDecl<Id>>,
    pub fundefs: Vec<FnDecl<Id>>,
    pub infixes: Vec<FixityDecl<Id>>,
    pub aliases: Vec<AliasDecl<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportDecl<Id = Ident> {
    pub name: Id,
    pub rename: Option<Id>,
    pub hidden: bool,
    pub imports: Vec<Import<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Import<Id = Ident> {
    Function(Id),
    /// Type imports: type only, no type constructors
    Abstract(Id),
    /// Data type imports that include *all* of their constructors
    Total(Id),
    /// Data type imports that include only the specified constructors
    Partial(Id, Vec<Id>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixityDecl<Id = Ident> {
    pub infixes: Vec<Id>,
    pub fixity: Fixity,
}

impl<Id> FixityDecl<Id> {
    pub fn new(assoc: Assoc, prec: Prec, infixes: Vec<Id>) -> Self {
        Self {
            infixes,
            fixity: Fixity { assoc, prec },
        }
    }
}

impl<Id: Copy + Eq + std::hash::Hash> From<&[FixityDecl<Id>]>
    for FixityTable<Id>
{
    fn from(fixity_decls: &[FixityDecl<Id>]) -> Self {
        Self(
            fixity_decls
                .iter()
                .flat_map(|FixityDecl { infixes, fixity }| {
                    infixes.iter().map(|infix| (*infix, *fixity))
                })
                .collect(),
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DataDecl<Id = Ident> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub ctxt: Vec<Context<Id>>,
    pub vnts: Vec<Variant<Id>>,
    pub with: Vec<Id>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variant<Id = Ident> {
    pub name: Id,
    pub args: Vec<Type<Id>>,
    // pub tag: Tag,
    pub arity: Arity,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Tag(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Arity(pub usize);

impl Arity {
    pub fn from_len<T>(ts: &[T]) -> Self {
        Self(ts.len())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AliasDecl<Id = Ident> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub sign: Signature<Id>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NewtypeDecl<Id = Ident> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub ctor: Id,
    pub tipo: Type<Id>,
    pub with: Vec<Id>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Tv(pub u32);

impl Tv {
    pub fn incr(&self) -> Self {
        Self(self.0 + 1)
    }

    pub fn display(&self) -> String {
        text::display_var(self.0)
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
pub enum Type<Id = Ident> {
    /// Type variables. These use their own special inner type `Tv`, which is a
    /// newtype wrapper around a `u32`.
    Var(Tv),
    /// Type constructors. Note that a `Con` variant may NOT have a type
    /// variable as the cosnstructor. For polymorphism over a constructor, use
    /// the `App` variant.
    Con(Id, Vec<Type<Id>>),
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
    Fun(Box<Type<Id>>, Box<Type<Id>>),
    Tup(Vec<Type<Id>>),
    Vec(Rc<Type<Id>>),
    Rec(Record<Type<Id>, Id>),
    App(Box<Type<Id>>, Vec<Type<Id>>),
}

// impl<Id> std::fmt::Debug for Type<Id> {}
impl<Id: std::fmt::Display> std::fmt::Display for Type<Id> {
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
            Type::App(c, xs) => {
                write!(f, "{}", c)?;
                for x in xs {
                    write!(f, " {}", x)?;
                }
                Ok(())
            }
        }
    }
}

impl<Id> Type<Id> {
    pub const UNIT: Self = Self::Tup(vec![]);

    pub fn is_func(&self) -> bool {
        matches!(self, Self::Fun(..))
    }

    /// Returns `true` if the type is a single type constructor. Type
    /// applications consisting of a single type, defined by a single type
    /// constructor, with no type arguments are also considered nullary, though
    /// it is important to consider the case in which a *non-nullary* type
    /// constructor hasn't been provided any type arguments.
    pub fn is_nullary(&self) -> bool {
        match self {
            Type::Con(_, ts) => ts.is_empty(),
            Type::App(head, tail) => tail.is_empty() && head.is_nullary(),
            _ => false,
        }
    }

    /// If a given type is a nullary type, then this will return a reference to
    /// the identifier represemting the nullary type constructor.
    pub fn id_if_nullary(&self) -> Option<&Id> {
        match self {
            Type::Con(id, args) if args.is_empty() => Some(id),
            Type::App(head, tail) if tail.is_empty() => head.id_if_nullary(),
            _ => None,
        }
    }

    /// Returns a vector containing all type variables in a given type in order.
    /// For example, this method applied to the type `(a, Int, a -> b -> c)`
    /// returns the vector `[a, b, c]`. Note that duplicates are *not* included!
    pub fn fv(&self) -> Vec<Tv> {
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
            Type::App(ct, ts) => ct
                .fv()
                .into_iter()
                .chain(ts.iter().flat_map(|t| t.fv()))
                .for_each(|tv| {
                    if !fvs.contains(&tv) {
                        fvs.push(tv);
                    }
                }),
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
    pub fn enumerate(&self) -> Vec<(Tv, Tv)> {
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
            .collect()
    }

    /// Takes all the type variables in a type, re-ordering them all
    /// and applying fresh names according to the new (normalized)
    /// ordering.
    ///
    /// For example, the type signature
    ///
    ///         [u] -> [st] -> [(u, st)]
    ///
    /// becomes
    ///
    ///         [a] -> [b] -> [(a, b)]
    pub fn normalize(&self) -> Result<Self, Self>
    where
        Id: Copy,
    {
        match self {
            Type::Var(a) => {
                if let Some((_u, v)) =
                    self.enumerate().into_iter().find(|(u, _)| u == a)
                {
                    Ok(Self::Var(v))
                } else {
                    Err(Self::Var(*a))
                }
            }
            Type::Con(id, args) => args
                .iter()
                .fold(Ok(vec![]), |a, c| {
                    let mut acc = a?;
                    let t = c.normalize()?;
                    acc.push(t);
                    Ok(acc)
                })
                .map(|rgs| Type::Con(*id, rgs)),
            Type::Fun(x, y) => {
                let ty_x = x.normalize()?;
                let ty_y = y.normalize()?;
                Ok(Self::Fun(Box::new(ty_x), Box::new(ty_y)))
            }
            Type::Tup(ts) => ts
                .iter()
                .fold(Ok(vec![]), |a, c| {
                    let mut acc = a?;
                    let t = c.normalize()?;
                    acc.push(t);
                    Ok(acc)
                })
                .map(Self::Tup),
            Type::Vec(ty) => {
                ty.as_ref().clone().normalize().and_then(|x| Ok(x))
                // Ok(Self::Vec(Rc::new(ty.clone().normalize()?)))
            }
            Type::Rec(rec) => {
                fn reduce<I: Copy>(
                    fields: &Vec<Field<Type<I>, I>>,
                ) -> Result<Vec<Field<Type<I>, I>>, Type<I>> {
                    fields.iter().fold(Ok(vec![]), |a, c| {
                        let mut acc = a?;
                        let field = match c {
                            Field::Rest => Field::Rest,
                            Field::Key(k) => Field::Key(*k),
                            Field::Entry(k, ty) => {
                                ty.normalize().map(|t| Field::Entry(*k, t))?
                            }
                        };
                        acc.push(field);
                        Ok(acc)
                    })
                }

                match rec {
                    Record::Anon(fields) => {
                        reduce(fields).map(Record::Anon).map(Type::Rec)
                    }
                    Record::Data(con, fields) => reduce(fields)
                        .map(|fs| Record::Data(*con, fs))
                        .map(Type::Rec),
                }
            }
            Type::App(a, ts) => {
                let head = a.normalize().map(Box::new)?;
                let tail = ts.iter().fold(Ok(vec![]), |a, c| {
                    let mut acc = a?;
                    let ty = c.normalize()?;
                    acc.push(ty);
                    Ok(acc)
                })?;
                Ok(Type::App(head, tail))
            }
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
        f(wy_intern::intern_once(":"))
    }

    /// Like with the list constructor `:`, the tuple constructor must also be
    /// processed to match the type used to represent identifiers. However,
    /// unlike the list constructor, which is used for *all* lists, tuples
    /// require a new constructor depending on the number of type components
    /// held. Thus it follows that, in order to reconstruct the type constructor
    /// for a tuple, two ingredients are necessary: the *number* of components
    /// in the tuple type expected, as well as a closure mapping the internal
    /// `Symbol` to the `Id` type representing identifiers.
    ///
    /// Notice that there are some further caveats:
    /// * `()` does *not* have a constructor.
    /// * `(a)` is equivalent to `a` *`(a, a)` is formed by the constructor
    /// `(,)`
    /// * `(a_1, a_2, ..., a_n)` is formed by the constructor consisting of `n -
    ///   1` commas.
    ///
    /// Because of the aforementioned caveats, it follows that the numeric
    /// argument to this method corresponds to the number of type components *to
    /// be added* to the standard tuple containing `2` types. Thus, for a given
    /// integer `n`, this will return the constructor for a tuple containing *n
    /// + 2* elements.
    ///
    /// An easy way to remember this is to remember that the integer provided
    /// *directly* corresponds to the number of *extra commas* in the resulting
    /// string representation of the constructor. This means that providing `0`
    /// will return the (polymorphic) constructor for 2-tuples.
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

    pub fn keys(&self) -> impl Iterator<Item = &Id> + '_ {
        self.fields().iter().filter_map(|field| match field {
            Field::Rest => None,
            Field::Key(k) | Field::Entry(k, _) => Some(k),
        })
    }

    /// Applies a transformation to the underlying components of a `Record`.
    /// Since a `Record` may or may not have a *constructor*, it follows that
    /// the kind of record *returned* will also depend on whether the first
    /// component of the tuple returned by the closure contains a `Some` variant
    /// or not. This means that it is possible to map from an `Record::Anon`
    /// variant to a `Record::Data` variant and vice-versa.
    pub fn map<F, U, V>(self, mut f: F) -> Record<V, U>
    where
        F: FnMut(
            (Option<Id>, Vec<Field<T, Id>>),
        ) -> (Option<U>, Vec<Field<V, U>>),
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context<Id = Ident, T = Tv> {
    pub class: Id,
    /// Defaults to `Tv`, but is parametrized in order to allow for simple
    /// (lowercase) identifiers to be used during parsing (which should then be
    /// *normalized* once the RHS is available so that `T` directly matches any
    /// type variables from the RHS).
    pub tyvar: T,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassDecl<Id = Ident> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub ctxt: Vec<Context<Id>>,
    pub defs: Vec<Method<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstDecl<Id = Ident> {
    pub name: Id,
    pub tipo: Type<Id>,
    pub ctxt: Vec<Context<Id>>,
    pub defs: Vec<Binding<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnDecl<Id = Ident> {
    pub name: Id,
    pub defs: Vec<Binding<Id>>,
    pub sign: Option<Signature<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature<Id = Ident> {
    pub ctxt: Vec<Context<Id>>,
    pub tipo: Type<Id>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Method<Id = Ident> {
    Sig(Id, Signature<Id>),
    Impl(Binding<Id>),
}

/// ```wysk
/// ~{
///       `name`
///         |          `tipo`   
///         v     vvvvvvvvvvvvvvvv
/// }~  fn foo :: a -> b -> (a, b)
///     | x y = (x, y);
/// ~~: ^^^^^^^^^^^^^^ `arms[0]`
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding<Id = Ident> {
    pub name: Id,
    pub arms: Vec<Match<Id>>,
    pub tipo: Option<Signature<Id>>,
}

/// ```wysk
///     fn foo :: Int -> Int -> Bool
/// ~~> Match[0]
/// ~~|  `args`
/// ~~|   vvv
///     | x y if x > y = True
/// ~~:       ^^^^^^^^   ^^^^
/// ~~:        `pred`   `body`
/// ~~> Match[1]
/// ~~|  `args`
/// ~~|   vvv
///     | x y = False && u where u = x + y > 0
/// ~~:   ^^^   ^^^^^^^^^^ ^^^^^^^^^^^^^^^^^^^
/// ~~: `args`    `body`         `wher[0]`
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Match<Id = Ident> {
    pub args: Vec<Pattern<Id>>,
    pub pred: Option<Expression<Id>>,
    pub body: Expression<Id>,
    pub wher: Vec<Binding<Id>>,
}

/// Pattern matching over a function definition
/// ```wysk
/// fn null :: [a] -> Bool
/// | [] = True
/// | _ = False;
/// ```
/// can be simplified to a `case` expression
/// ```wysk
/// fn null :: [a] -> Bool
/// | xs = case xs of
/// ~~> Alternative[0]
/// ~~|  `pat`
/// ~~|   vv
///     | [] -> True
/// ~~> Alternative[1]
/// ~~|  `pat`
/// ~~|   |  `pred`      `body`
/// ~~|   v vvvvvvvvv    vvvvv
///     | _ if t || u -> False
///         where t = True;
/// ~~:           ^^^^^^^^ `wher[0]`
///               u = False;
/// ~~:           ^^^^^^^^^ `wher[1]`
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alternative<Id = Ident> {
    pub pat: Pattern<Id>,
    pub pred: Option<Expression<Id>>,
    pub body: Expression<Id>,
    pub wher: Vec<Binding<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Declaration<Id = Ident> {
    Data(DataDecl<Id>),
    Alias(AliasDecl<Id>),
    Fixity(FixityDecl<Id>),
    Class(ClassDecl<Id>),
    Instance(InstDecl<Id>),
    Function(FnDecl<Id>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expression<Id = Ident> {
    Ident(Id),
    Lit(Literal),
    Neg(Box<Expression<Id>>),
    Infix {
        infix: Id,
        left: Box<Expression<Id>>,
        right: Box<Expression<Id>>,
    },
    Tuple(Vec<Expression<Id>>),
    Array(Vec<Expression<Id>>),
    /// List comprehensions contain an expression and a list of statements
    /// consisting of *generators* and *predicates*.
    ///
    /// For example, if we suppose `f :: Int -> Int` is some integer-valued
    /// function, and `even :: Int -> Bool` is some integer-valued predicate
    /// testing for integer parity, then the following list expression would
    /// generate a list of the results of applying `f` to each even integer
    /// between `0` and `10` (not-inclusive).
    /// ```haskell
    ///     [ f x | x <- [0..10], even x ]
    /// ```
    /// In fact, the above expression would be equivalent to
    /// ```haskell
    ///     map f (filter even [0..10])
    /// ```
    /// and can be generalized to the following (inefficient) `let` expression,
    /// where we use `f`
    /// ```haskell
    /// let f :: a -> b
    ///     | a' = ...
    ///     g :: a -> Bool
    ///     | a'' = ...
    ///     h :: [a] -> [b]
    ///     | [] = []
    ///     | (a:as) if g a -> f a : h as
    ///     | (a:as) -> h as
    /// in ...
    /// ```
    ///
    /// In particular, we can view a list comprehension as syntactic sugar
    /// for
    ///
    List(Box<Expression<Id>>, Vec<Statement<Id>>),
    Dict(Record<Expression<Id>, Id>),
    Lambda(Pattern<Id>, Box<Expression<Id>>),
    Let(Vec<Binding<Id>>, Box<Expression<Id>>),
    App(Box<Expression<Id>>, Box<Expression<Id>>),
    Cond(Box<[Expression<Id>; 3]>),
    Case(Box<Expression<Id>>, Vec<Alternative<Id>>),
    Cast(Box<Expression<Id>>, Type<Id>),
    Do(Vec<Statement<Id>>, Box<Expression<Id>>),
    Range(Box<Expression<Id>>, Option<Box<Expression<Id>>>),
    Group(Box<Expression<Id>>),
}

impl<Id> Expression<Id> {
    pub const UNIT: Self = Self::Tuple(vec![]);
    pub const NULL: Self = Self::Array(vec![]);
    pub const VOID: Self = Self::Dict(Record::Anon(vec![]));
    pub fn is_unit(&self) -> bool {
        matches!(self, Self::Tuple(vs) if vs.is_empty())
    }
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Array(vs) if vs.is_empty())
    }
    pub fn is_void(&self) -> bool {
        matches!(self, Self::Dict(Record::Anon(vs)) if vs.is_empty())
    }
    pub fn is_empty_record(&self) -> bool {
        matches!(self, Self::Dict(Record::Anon(fs)|Record::Data(_, fs)) if fs.is_empty() )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement<Id = Ident> {
    // <PAT> <- <EXPR>
    Generator(Pattern<Id>, Expression<Id>),
    // <EXPR>
    Predicate(Expression<Id>),
    // let (<ID> <PAT>* = <EXPR>)+
    DoLet(Vec<Binding<Id>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern<Id = Ident> {
    Wild,
    Var(Id),
    Lit(Literal),
    Con(Id, Vec<Pattern<Id>>),
    Tup(Vec<Pattern<Id>>),
    Lst(Vec<Pattern<Id>>),
    At(Id, Box<Pattern<Id>>),
    Or(Vec<Pattern<Id>>),
    Rec(Record<Pattern<Id>, Id>),
    Cast(Box<Pattern<Id>>, Type<Id>),
}

impl<Id> Pattern<Id> {
    pub const UNIT: Self = Self::Tup(vec![]);
    pub const NIL: Self = Self::Lst(vec![]);
    pub const VOID: Self = Self::Rec(Record::VOID);
    pub fn is_unit(&self) -> bool {
        matches!(self, Self::Tup(vs) if vs.is_empty())
    }
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Lst(vs) if vs.is_empty())
    }
    pub fn is_void(&self) -> bool {
        matches!(self, Self::Rec(Record::Anon(vs)) if vs.is_empty())
    }
    pub fn is_empty_record(&self) -> bool {
        matches!(self, Self::Rec(Record::Anon(fs)|Record::Data(_, fs)) if fs.is_empty() )
    }
}
