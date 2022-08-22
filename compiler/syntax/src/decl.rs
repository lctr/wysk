use serde::{Deserialize, Serialize};
use wy_common::functor::Functor;

pub use wy_lexer::{
    comment::{self, Comment},
    Literal,
};
use wy_span::{Span, Spanned};

use crate::{attr::*, fixity::*, stmt::*, tipo::*, SpannedIdent};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FixityDecl<Id = SpannedIdent> {
    pub span: Span,
    pub infixes: Vec<Id>,
    pub fixity: Fixity,
    pub from_pragma: bool,
}

impl<Id> FixityDecl<Id> {
    pub fn infixes_iter(&self) -> std::slice::Iter<'_, Id> {
        self.infixes.iter()
    }

    pub fn infixes_iter_mut(&mut self) -> std::slice::IterMut<'_, Id> {
        self.infixes.iter_mut()
    }

    pub fn mapf<F, X>(self, f: &mut wy_common::functor::Func<'_, F>) -> FixityDecl<X>
    where
        F: FnMut(Id) -> X,
    {
        FixityDecl {
            span: self.span,
            infixes: Functor::fmap(self.infixes, f),
            fixity: self.fixity,
            from_pragma: self.from_pragma,
        }
    }
}

impl<Id: Clone> From<&[FixityDecl<Spanned<Id>>]> for Fixities<Id> {
    fn from(fixs: &[FixityDecl<Spanned<Id>>]) -> Self {
        fixs.into_iter()
            .flat_map(|decl| {
                decl.infixes_iter()
                    .cloned()
                    .map(|Spanned(id, _)| (id, decl.fixity))
            })
            .collect()
    }
}

impl From<&[FixityDecl<wy_name::Ident>]> for Fixities<wy_name::Ident> {
    fn from(fixs: &[FixityDecl<wy_name::Ident>]) -> Self {
        fixs.into_iter()
            .flat_map(|decl| decl.infixes_iter().copied().map(|id| (id, decl.fixity)))
            .collect()
    }
}

impl<Id: Copy + Eq + std::hash::Hash> From<&[FixityDecl<Spanned<Id>>]> for FixityTable<Id> {
    fn from(fixity_decls: &[FixityDecl<Spanned<Id>>]) -> Self {
        Self(
            fixity_decls
                .iter()
                .flat_map(
                    |FixityDecl {
                         span: _,
                         infixes,
                         fixity,
                         from_pragma: _,
                     }| {
                        infixes.iter().map(|infix| (*infix.item(), *fixity))
                    },
                )
                .collect(),
        )
    }
}

impl From<&[FixityDecl<wy_name::Ident>]> for FixityTable<wy_name::Ident> {
    fn from(fixity_decls: &[FixityDecl<wy_name::Ident>]) -> Self {
        Self(
            fixity_decls
                .iter()
                .flat_map(
                    |FixityDecl {
                         span: _,
                         infixes,
                         fixity,
                         from_pragma: _,
                     }| { infixes.iter().map(|infix| (*infix, *fixity)) },
                )
                .collect(),
        )
    }
}

/// A `DataDecl` defines a new *type constructor* `name` as well as a
/// fixed set of *data constructors*, termed `variant`s, to construct
/// values of said type. The type constructor defined may additionally
/// hold constraints over the types by which it may be parametrized,
/// as well as have *certain* built-in classes automatically
/// implemented.
///
/// # Constructors
/// Values for the defined type are constructed using the included
/// *data* constructors. Data constructors share a separate namespace
/// from the type constructor itself, so it is possible for a type
/// constructor to have a data constructor with the same name. Note
/// that a data declaration need not have data constructors.
///
/// Data constructors are semantically functions that return values of
/// the data type. Constructors may either be *nullary* and take no
/// arguments, be *curried* and take one or more arguments, or be
/// *records* in which the arguments are labelled.
///
/// Note that record constructors may be treated as curried
/// constructors when used without the record syntax but require that
/// arguments be applied in the same order in which the field labels
/// are defined.
///
/// The order in which constructors are defined is relevant for some
/// automatically derived classes (such as `Ord` or `Enum` when all
/// constructors are nullary).
///
/// # Polymorphism
/// A data type may be polymorphic over a set of type variables, all
/// of which must be declared as arguments to the type constructor
/// `name` and *must* be linear, i.e., must not have repeated type
/// variables.
///
/// # Automatically derived class implementations
/// A data declaration may contain an optional `with` clause, which
/// contains either a single class name or a list of class names; the
/// compiler will automatically generate instances of these class
/// names for the type defined by the data declaration. **Note** the
/// classes in the `with` clause are limited and additionally require
/// that every type contained by the defined type also be instances of
/// each class. It is an error for a data declaration to hold data for
/// some type that is not an instance of a class listed in the `with`
/// clause.
///
/// The (to be defacto) supported classes are the following:
/// * `Eq` - total equality
/// * `Ord` - total ordering
/// * `Show` - string representable
/// * `Enum` - enumerable, only valid when all constructors are
///   nullary
/// * `Bound` - bounded from above and below, requires `Ord` and `Eq`
/// * `Hash` - hashable, requires `Eq`
///
/// # Syntactic components
/// | Fields | Description                                           |
/// |--------|:------------------------------------------------------|
/// | `name` | name of type (constructor) being defined              |
/// | `poly` | list of type variables parametrizing the type         |
/// | `pred` | classes of which type variables must be instances     |
/// | `vnts` | data constructors for the defined type                |
/// | `with` | classes for which instances are automatically derived |
///
/// # Example
/// The following source code defines a type constructor `Foo`,
/// parametrized by the type variable `a` (which must be an instance
/// of the class `A`), with data constructors `Bar a :: a -> Foo a`
/// and `Baz :: a -> Foo a -> Foo a`, and automatically derived
/// instances for the classes `A`, `B`, `C`.
///
/// ```wysk
/// ~~    pred name poly
/// ~~     🡓   🡓  🡓
/// data |A a| Foo a
///     = Bar a          ~~ variant 0
///     | Baz a (Foo a)  ~~ variant 1
///     with (A, B, C);  ~~ with (deriving) clause
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DataDecl<Id = SpannedIdent, V = SpannedIdent> {
    pub span: Span,
    pub prag: Vec<Pragma<Id, V>>,
    pub tdef: SimpleType<Id, V>,
    pub pred: Vec<Predicate<Id, V>>,
    pub vnts: Vec<Variant<Id, V>>,
    pub with: Option<WithClause<Id>>,
}

wy_common::struct_field_iters! {
    |Id, V| DataDecl<Id, V>
    | pred => context_iter :: Predicate<Id, V>
    | vnts => variants_iter :: Variant<Id, V>
}

impl<Id, V> DataDecl<Id, V> {
    pub fn preds_iter_mut(&mut self) -> std::slice::IterMut<'_, Predicate<Id, V>> {
        self.pred.iter_mut()
    }

    pub fn variants_iter_mut(&mut self) -> std::slice::IterMut<'_, Variant<Id, V>> {
        self.vnts.iter_mut()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WithClause<Id = SpannedIdent> {
    pub span: Span,
    pub names: Vec<Id>,
    pub from_pragma: bool,
}

wy_common::struct_field_iters! {
    |Id| WithClause<Id>
    | names => names_iter :: Id
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Selector<Id = SpannedIdent, V = SpannedIdent> {
    pub name: Id,
    pub tipo: Type<Id, V>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TypeArg<Id = SpannedIdent, V = SpannedIdent, T = Type<Id, V>, S = Selector<Id, V>> {
    /// Not really used since nullary type constructors can just take
    /// an empty vector of `TypeArg`s, however this is here to allow
    /// parametrizing the existing type and selector parameters
    Empty(std::marker::PhantomData<(Id, V)>),
    ///
    Type(T),
    ///
    Selector(S),
}

wy_common::variant_preds! {
    |Id, V| TypeArg[Id, V]
    | is_type => Type(_)
    | is_selector => Selector(..)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TypeArgs<Id = SpannedIdent, V = SpannedIdent> {
    Curried(Vec<Type<Id, V>>),
    Record(Vec<Selector<Id, V>>),
}

impl<Id, V> TypeArgs<Id, V> {
    pub fn len(&self) -> usize {
        match self {
            TypeArgs::Curried(ts) => ts.len(),
            TypeArgs::Record(sels) => sels.len(),
        }
    }

    // REDO
    pub fn iter<'a>(&'a self) -> Vec<TypeArg<Id, V, &'a Type<Id, V>, &'a Selector<Id, V>>> {
        match self {
            TypeArgs::Curried(ty) => ty
                .into_iter()
                .map(|f| TypeArg::<Id, V, &Type<Id, V>, &Selector<Id, V>>::Type(f))
                .collect::<Vec<_>>(),
            TypeArgs::Record(sel) => sel
                .into_iter()
                .map(|s| TypeArg::<Id, V, &Type<Id, V>, &Selector<Id, V>>::Selector(s))
                .collect::<Vec<_>>(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Variant<Id = SpannedIdent, V = SpannedIdent> {
    pub name: Id,
    pub span: Span,
    pub prag: Vec<Pragma<Id, V>>,
    pub args: TypeArgs<Id, V>,
}

impl<Id, V> Variant<Id, V> {
    // pub fn args_iter(&self) -> std::slice::Iter<'_, TypeArg<Id, V>> {
    //     self.args.iter()
    // }

    // pub fn args_iter_mut(&mut self) -> std::slice::IterMut<'_, TypeArg<Id, V>> {
    //     self.args.iter_mut()
    // }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Arity(pub usize);

impl std::fmt::Debug for Arity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Arity({})", &self.0)
    }
}

impl std::fmt::Display for Arity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Arity({})", &self.0)
    }
}

impl Arity {
    pub const ZERO: Self = Self(0);

    pub fn as_usize(self) -> usize {
        self.0
    }

    pub fn new(len: usize) -> Self {
        Arity(len)
    }

    /// Shortcut to check whether a given item takes *no arguments*.
    pub fn is_zero(self) -> bool {
        self.0 == 0
    }
}

// make it easy to compare Arity using usizes by implementing PartialEq<usize>
// and PartialOrd<usize>
wy_common::newtype!(Arity | usize | PartialEq);
wy_common::newtype!(Arity | usize | PartialOrd);
wy_common::newtype!(Arity | usize | (+= usize |rhs| rhs) );

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AliasDecl<Id = SpannedIdent, V = SpannedIdent> {
    pub span: Span,
    pub prag: Vec<Pragma<Id, V>>,
    pub ldef: SimpleType<Id, V>,
    pub tipo: Type<Id, V>,
}

/// `Newtype`s allow for *renaming* of types. Ideally little to no overhead is
/// involved in working with newtypes, as the "type renaming" of a newtype is
/// effectively forgotten post-typechecking. A newtype declaration is helpful
/// for discriminating against various "uses" of a single type. For example, it
/// is perfectly acceptable to use a type alias to distinguish between numerical
/// units, however this does not provide a safeguard against inconsistencies!
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NewtypeDecl<Id = SpannedIdent, V = SpannedIdent> {
    pub span: Span,
    pub prag: Vec<Pragma<Id, V>>,
    pub tdef: SimpleType<Id, V>,
    pub ctor: Id,
    pub narg: TypeArg<Id, V>,
    pub with: Option<WithClause<Id>>,
}

impl<Id, V> NewtypeDecl<Id, V> {
    pub fn name(&self) -> &Id {
        self.tdef.con()
    }

    pub fn vars(&self) -> &[V] {
        self.tdef.vars()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassDecl<Id = SpannedIdent, V = SpannedIdent> {
    pub span: Span,
    pub prag: Vec<Pragma<Id, V>>,
    pub cdef: SimpleType<Id, V>,
    pub pred: Vec<Predicate<Id, V>>,
    pub defs: Vec<MethodDef<Id, V>>,
}

wy_common::struct_field_iters! {
    |Id, V| ClassDecl<Id, V>
    | pred => pred_iter :: Predicate<Id, V>
    | defs => defs_iter :: MethodDef<Id, V>
    | prag => prag_iter :: Pragma<Id, V>
}

impl<Id, V> ClassDecl<Id, V> {
    pub fn item_names(&self) -> impl Iterator<Item = &Id> + '_ {
        self.defs.iter().map(|MethodDef { name, .. }| name)
    }

    pub fn defs_iter_mut(&mut self) -> std::slice::IterMut<'_, MethodDef<Id, V>> {
        self.defs.iter_mut()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InstDecl<Id = SpannedIdent, V = SpannedIdent> {
    pub span: Span,
    pub prag: Vec<Pragma<Id, V>>,
    pub name: Id,
    pub tipo: Type<Id, V>,
    pub pred: Vec<Predicate<Id, V>>,
    pub defs: Vec<Binding<Id, V>>,
}

wy_common::struct_field_iters! {
    |Id, V| InstDecl<Id, V>
    | pred => pred_iter :: Predicate<Id, V>
    | defs => defs_iter :: Binding<Id, V>
    | prag => prag_iter :: Pragma<Id, V>
}

impl<Id, V> InstDecl<Id, V> {
    pub fn item_names(&self) -> impl Iterator<Item = &Id> + '_ {
        self.defs_iter().map(|Binding { name, .. }| name)
    }
    pub fn get_pred(&self, id: &Id) -> Option<&Predicate<Id, V>>
    where
        Id: PartialEq,
    {
        self.pred_iter().find(|ctx| &ctx.class == id)
    }

    pub fn get_def(&self, id: &Id) -> Option<&Binding<Id, V>>
    where
        Id: PartialEq,
    {
        self.defs_iter().find(|b| b.name == *id)
    }

    pub fn defs_iter_mut(&mut self) -> std::slice::IterMut<'_, Binding<Id, V>> {
        self.defs.iter_mut()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FnDecl<Id = SpannedIdent, V = SpannedIdent> {
    pub span: Span,
    pub prag: Vec<Pragma<Id, V>>,
    pub name: Id,
    pub sign: Signature<Id, V>,
    pub defs: Vec<Arm<Id, V>>,
}

wy_common::struct_field_iters! {
    |Id, V| FnDecl<Id, V>
    | defs => defs_iter :: Arm<Id, V>
    | prag => prag_iter :: Pragma<Id, V>
}

impl<Id, V> FnDecl<Id, V> {
    pub fn has_tysig(&self) -> bool {
        !self.sign.is_implicit()
    }

    pub fn defs_iter_mut(&mut self) -> std::slice::IterMut<'_, Arm<Id, V>> {
        self.defs.iter_mut()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MethodBody<Id = SpannedIdent, V = SpannedIdent> {
    Unimplemented,
    Default(Vec<Arm<Id, V>>),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodDef<Id = SpannedIdent, V = SpannedIdent> {
    pub span: Span,
    pub prag: Vec<Pragma<Id, V>>,
    pub name: Id,
    pub annt: Annotation<Id, V>,
    pub body: MethodBody<Id, V>,
}

// wy_common::struct_field_iters! {
//     |Id, V| MethodDef<Id, V>
//     | body => body_iter :: Match<Id, V>
// }

/// TODO: update `MethodImpl` to be suitable for use in `InstDecl`s
/// for implemented methods
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodImpl<Id = SpannedIdent, V = SpannedIdent>(pub Binding<Id, V>);
impl<Id, V> MethodImpl<Id, V> {
    pub fn new(binding: Binding<Id, V>) -> Self {
        Self(binding)
    }
    pub fn name(&self) -> &Id {
        &self.0.name
    }
    pub fn arms(&self) -> &[Arm<Id, V>] {
        &self.0.arms[..]
    }
    pub fn arms_iter(&self) -> std::slice::Iter<'_, Arm<Id, V>> {
        self.0.arms.iter()
    }
    pub fn arms_iter_mut(&mut self) -> std::slice::IterMut<'_, Arm<Id, V>> {
        self.0.arms.iter_mut()
    }
    pub fn signature(&self) -> &Signature<Id, V> {
        &self.0.tsig
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Declaration<Id = SpannedIdent, V = SpannedIdent> {
    Data(DataDecl<Id, V>),
    Alias(AliasDecl<Id, V>),
    Fixity(FixityDecl<Id>),
    Class(ClassDecl<Id, V>),
    Instance(InstDecl<Id, V>),
    Function(FnDecl<Id, V>),
    Newtype(NewtypeDecl<Id, V>),
}

wy_common::variant_preds! {
    Declaration
    | is_data => Data(_)
    | is_alias => Alias(_)
    | is_fixity => Fixity(_)
    | is_class => Class(_)
    | is_instance => Instance(_)
    | is_function => Function(_)
    | is_newtype => Newtype(_)
}

impl<Id, V> Declaration<Id, V> {
    pub fn name(&self) -> &Id {
        match self {
            Declaration::Data(d) => &d.tdef.con(),
            Declaration::Alias(a) => &a.ldef.con(),
            Declaration::Fixity(f) => &f.infixes[0],
            Declaration::Class(c) => c.cdef.con(),
            Declaration::Instance(i) => &i.name,
            Declaration::Function(f) => &f.name,
            Declaration::Newtype(n) => n.tdef.con(),
        }
    }

    pub fn extend_pragmas(&mut self, pragmas: Vec<Pragma<Id, V>>) {
        match self {
            Declaration::Data(d) => d.prag.extend(pragmas),
            Declaration::Alias(a) => a.prag.extend(pragmas),
            Declaration::Fixity(_f) => (), // f.prag.extend(pragmas),
            Declaration::Class(cl) => cl.prag.extend(pragmas),
            Declaration::Instance(i) => i.prag.extend(pragmas),
            Declaration::Function(f) => f.prag.extend(pragmas),
            Declaration::Newtype(n) => n.prag.extend(pragmas),
        }
    }
}
