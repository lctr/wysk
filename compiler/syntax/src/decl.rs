use serde::{Deserialize, Serialize};
use wy_common::functor::{Functor, MapFst, MapSnd};

pub use wy_lexer::{
    comment::{self, Comment},
    Literal,
};
use wy_span::{Span, Spanned};

use crate::{attr::*, fixity::*, stmt::*, tipo::*, SpannedIdent};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixityDecl<Id = SpannedIdent> {
    pub span: Span,
    pub infixes: Vec<Id>,
    pub fixity: Fixity,
}

impl<Id> FixityDecl<Id> {
    pub fn mapf<F, X>(self, f: &mut wy_common::functor::Func<'_, F>) -> FixityDecl<X>
    where
        F: FnMut(Id) -> X,
    {
        FixityDecl {
            span: self.span,
            infixes: Functor::fmap(self.infixes, f),
            fixity: self.fixity,
        }
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
    pub tdef: SimpleType<Id, V>,
    pub pred: Vec<Predicate<Id, V>>,
    pub vnts: Vec<Variant<Id, V>>,
    pub with: Vec<Id>,
}

wy_common::struct_field_iters! {
    |Id, V| DataDecl<Id, V>
    | pred => context_iter :: Predicate<Id, V>
    | vnts => variants_iter :: Variant<Id, V>
    | with => derives_iter :: Id
}

impl<Id, V, X> MapFst<Id, X> for DataDecl<Id, V> {
    type WrapFst = DataDecl<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let DataDecl {
            span,
            tdef,
            pred,
            vnts,
            with,
        } = self;
        let tdef = tdef.map_fst(f);
        let pred = pred.map_fst(f);
        let vnts = vnts.map_fst(f);
        let with = with.into_iter().map(|id| f.apply(id)).collect();
        DataDecl {
            span,
            tdef,
            pred,
            vnts,
            with,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for DataDecl<Id, V> {
    type WrapSnd = DataDecl<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let DataDecl {
            span,
            tdef,
            pred,
            vnts,
            with,
        } = self;
        let tdef = tdef.map_snd(f);
        let pred = pred.map_snd(f);
        let vnts = vnts.map_snd(f);
        DataDecl {
            span,
            tdef,
            pred,
            vnts,
            with,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Selector<Id = SpannedIdent, V = SpannedIdent> {
    pub name: Id,
    pub tipo: Type<Id, V>,
}

impl<Id, V, X> MapFst<Id, X> for Selector<Id, V> {
    type WrapFst = Selector<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        Selector {
            name: f.apply(self.name),
            tipo: self.tipo.map_fst(f),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Selector<Id, V> {
    type WrapSnd = Selector<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        Selector {
            name: self.name,
            tipo: self.tipo.map_snd(f),
        }
    }
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

impl<Id, V, X> MapFst<Id, X> for TypeArg<Id, V> {
    type WrapFst = TypeArg<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            TypeArg::Empty(_) => TypeArg::Empty(std::marker::PhantomData),
            TypeArg::Type(t) => TypeArg::Type(t.map_fst(f)),
            TypeArg::Selector(sel) => TypeArg::Selector(sel.map_fst(f)),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for TypeArg<Id, V> {
    type WrapSnd = TypeArg<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            TypeArg::Empty(_) => TypeArg::Empty(std::marker::PhantomData),
            TypeArg::Type(t) => TypeArg::Type(t.map_snd(f)),
            TypeArg::Selector(sel) => TypeArg::Selector(sel.map_snd(f)),
        }
    }
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

    // pub fn iter(
    //     &self,
    // ) -> impl Iterator<Item = TypeArg<Id, V, &Type<Id, V>, &Selector<Id, V>>> + '_ {
    //     todo!()
    // }
}

impl<Id, V, X> MapFst<Id, X> for TypeArgs<Id, V> {
    type WrapFst = TypeArgs<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            TypeArgs::Curried(t) => TypeArgs::Curried(t.map_fst(f)),
            TypeArgs::Record(sel) => TypeArgs::Record(sel.map_fst(f)),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for TypeArgs<Id, V> {
    type WrapSnd = TypeArgs<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            TypeArgs::Curried(t) => TypeArgs::Curried(t.map_snd(f)),
            TypeArgs::Record(sel) => TypeArgs::Record(sel.map_snd(f)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Variant<Id = SpannedIdent, V = SpannedIdent> {
    pub name: Id,
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

impl<Id, V, X> MapFst<Id, X> for Variant<Id, V> {
    type WrapFst = Variant<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let Variant { name, args } = self;
        let name = f.apply(name);
        let args = args.map_fst(f);
        Variant { name, args }
    }
}

impl<Id, V, X> MapSnd<V, X> for Variant<Id, V> {
    type WrapSnd = Variant<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let Variant { name, args } = self;
        let args = args.map_snd(f);
        Variant { name, args }
    }
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
    pub ldef: SimpleType<Id, V>,
    pub tipo: Type<Id, V>,
}

impl<Id, V, X> MapFst<Id, X> for AliasDecl<Id, V> {
    type WrapFst = AliasDecl<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        AliasDecl {
            span: self.span,
            ldef: self.ldef.map_fst(f),
            tipo: self.tipo.map_fst(f),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for AliasDecl<Id, V> {
    type WrapSnd = AliasDecl<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        AliasDecl {
            span: self.span,
            ldef: self.ldef.map_snd(f),
            tipo: self.tipo.map_snd(f),
        }
    }
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
    pub tdef: SimpleType<Id, V>,
    pub ctor: Id,
    pub narg: TypeArg<Id, V>,
    pub with: Vec<Id>,
}

impl<Id, V> NewtypeDecl<Id, V> {
    pub fn name(&self) -> &Id {
        self.tdef.con()
    }

    pub fn vars(&self) -> &[V] {
        self.tdef.vars()
    }
}

wy_common::struct_field_iters! {
    |Id, V| NewtypeDecl<Id, V>
    | with => derives_iter :: Id
}

impl<Id, V, X> MapFst<Id, X> for NewtypeDecl<Id, V> {
    type WrapFst = NewtypeDecl<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let NewtypeDecl {
            span,
            tdef,
            ctor,
            narg,
            with,
        } = self;
        let tdef = tdef.map_fst(f);
        let ctor = f.apply(ctor);
        let narg = narg.map_fst(f);
        let with = with.into_iter().map(|id| f.apply(id)).collect();
        NewtypeDecl {
            span,
            tdef,
            ctor,
            narg,
            with,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for NewtypeDecl<Id, V> {
    type WrapSnd = NewtypeDecl<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let NewtypeDecl {
            span,
            tdef,
            ctor,
            narg,
            with,
        } = self;
        let tdef = tdef.map_snd(f);
        let narg = narg.map_snd(f);
        NewtypeDecl {
            span,
            tdef,
            ctor,
            narg,
            with,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassDecl<Id = SpannedIdent, V = SpannedIdent> {
    pub span: Span,
    pub cdef: SimpleType<Id, V>,
    pub pred: Vec<Predicate<Id, V>>,
    pub defs: Vec<MethodDef<Id, V>>,
}

wy_common::struct_field_iters! {
    |Id, V| ClassDecl<Id, V>
    | pred => pred_iter :: Predicate<Id, V>
    | defs => defs_iter :: MethodDef<Id, V>
}

impl<Id, V> ClassDecl<Id, V> {
    pub fn item_names(&self) -> impl Iterator<Item = &Id> + '_ {
        self.defs.iter().map(|MethodDef { name, .. }| name)
    }
}

impl<Id, V, X> MapFst<Id, X> for ClassDecl<Id, V> {
    type WrapFst = ClassDecl<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let ClassDecl {
            span,
            cdef,
            pred,
            defs,
        } = self;
        let cdef = cdef.map_fst(f);
        let pred = pred.map_fst(f);
        let defs = defs.map_fst(f);
        ClassDecl {
            span,
            cdef,
            pred,
            defs,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for ClassDecl<Id, V> {
    type WrapSnd = ClassDecl<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let ClassDecl {
            span,
            cdef,
            pred,
            defs,
        } = self;
        let cdef = cdef.map_snd(f);
        let pred = pred.map_snd(f);
        let defs = defs.map_snd(f);
        ClassDecl {
            span,
            cdef,
            pred,
            defs,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InstDecl<Id = SpannedIdent, V = SpannedIdent> {
    pub span: Span,
    pub name: Id,
    pub tipo: Type<Id, V>,
    pub pred: Vec<Predicate<Id, V>>,
    pub defs: Vec<Binding<Id, V>>,
}

wy_common::struct_field_iters! {
    |Id, V| InstDecl<Id, V>
    | pred => pred_iter :: Predicate<Id, V>
    | defs => defs_iter :: Binding<Id, V>
}

impl<Id, V, X> MapFst<Id, X> for InstDecl<Id, V> {
    type WrapFst = InstDecl<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let InstDecl {
            span,
            name,
            tipo,
            pred,
            defs,
        } = self;
        let name = f.apply(name);
        let tipo = tipo.map_fst(f);
        let pred = pred.map_fst(f);
        let defs = defs.map_fst(f);
        InstDecl {
            span,
            name,
            tipo,
            pred,
            defs,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for InstDecl<Id, V> {
    type WrapSnd = InstDecl<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let InstDecl {
            span,
            name,
            tipo,
            pred,
            defs,
        } = self;
        let tipo = tipo.map_snd(f);
        let pred = pred.map_snd(f);
        let defs = defs.map_snd(f);
        InstDecl {
            span,
            name,
            tipo,
            pred,
            defs,
        }
    }
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
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FnDecl<Id = SpannedIdent, V = SpannedIdent> {
    pub span: Span,
    pub name: Id,
    pub sign: Signature<Id, V>,
    pub defs: Vec<Match<Id, V>>,
}

wy_common::struct_field_iters! {
    |Id, V| FnDecl<Id, V>
    | defs => defs_iter :: Match<Id, V>
}

impl<Id, V, X> MapFst<Id, X> for FnDecl<Id, V> {
    type WrapFst = FnDecl<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let FnDecl {
            span,
            name,
            sign,
            defs,
        } = self;
        let name = f.apply(name);
        let sign = sign.map_fst(f);
        let defs = defs.map_fst(f);
        FnDecl {
            span,
            name,
            sign,
            defs,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for FnDecl<Id, V> {
    type WrapSnd = FnDecl<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let FnDecl {
            span,
            name,
            sign,
            defs,
        } = self;
        let sign = sign.map_snd(f);
        let defs = defs.map_snd(f);
        FnDecl {
            span,
            name,
            sign,
            defs,
        }
    }
}

impl<Id, V> FnDecl<Id, V> {
    pub fn has_tysig(&self) -> bool {
        !self.sign.is_implicit()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MethodBody<Id = SpannedIdent, V = SpannedIdent> {
    Unimplemented,
    Default(Vec<Match<Id, V>>),
}

impl<Id, V, X> MapFst<Id, X> for MethodBody<Id, V> {
    type WrapFst = MethodBody<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            MethodBody::Unimplemented => MethodBody::Unimplemented,
            MethodBody::Default(arms) => MethodBody::Default(arms.map_fst(f)),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for MethodBody<Id, V> {
    type WrapSnd = MethodBody<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            MethodBody::Unimplemented => MethodBody::Unimplemented,
            MethodBody::Default(arms) => MethodBody::Default(arms.map_snd(f)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodDef<Id = SpannedIdent, V = SpannedIdent> {
    pub span: Span,
    pub name: Id,
    pub annt: Annotation<Id, V>,
    pub body: MethodBody<Id, V>,
}

// wy_common::struct_field_iters! {
//     |Id, V| MethodDef<Id, V>
//     | body => body_iter :: Match<Id, V>
// }

impl<Id, V, X> MapFst<Id, X> for MethodDef<Id, V> {
    type WrapFst = MethodDef<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let MethodDef {
            span,
            name,
            annt,
            body,
        } = self;
        let name = f.apply(name);
        let annt = annt.map_fst(f);
        let body = body.map_fst(f);
        MethodDef {
            span,
            name,
            annt,
            body,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for MethodDef<Id, V> {
    type WrapSnd = MethodDef<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let MethodDef {
            span,
            name,
            annt,
            body,
        } = self;
        let annt = annt.map_snd(f);
        let body = body.map_snd(f);
        MethodDef {
            span,
            name,
            annt,
            body,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodImpl<Id = SpannedIdent, V = SpannedIdent>(pub Binding<Id, V>);
impl<Id, V> MethodImpl<Id, V> {
    pub fn new(binding: Binding<Id, V>) -> Self {
        Self(binding)
    }
    pub fn name(&self) -> &Id {
        &self.0.name
    }
    pub fn arms(&self) -> &[Match<Id, V>] {
        &self.0.arms[..]
    }
    pub fn arms_iter(&self) -> std::slice::Iter<'_, Match<Id, V>> {
        self.0.arms.iter()
    }
    pub fn arms_iter_mut(&mut self) -> std::slice::IterMut<'_, Match<Id, V>> {
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
    Attribute(Attribute<Id, V>),
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
    | is_attribute => Attribute(_)
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
            Declaration::Attribute(a) => a.name(),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Declaration<Id, V> {
    type WrapFst = Declaration<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Declaration::Data(d) => Declaration::Data(d.map_fst(f)),
            Declaration::Alias(d) => Declaration::Alias(d.map_fst(f)),
            Declaration::Fixity(d) => Declaration::Fixity(d.mapf(f)),
            Declaration::Class(d) => Declaration::Class(d.map_fst(f)),
            Declaration::Instance(d) => Declaration::Instance(d.map_fst(f)),
            Declaration::Function(d) => Declaration::Function(d.map_fst(f)),
            Declaration::Newtype(d) => Declaration::Newtype(d.map_fst(f)),
            Declaration::Attribute(d) => Declaration::Attribute(d.map_fst(f)),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Declaration<Id, V> {
    type WrapSnd = Declaration<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Declaration::Data(d) => Declaration::Data(d.map_snd(f)),
            Declaration::Alias(d) => Declaration::Alias(d.map_snd(f)),
            Declaration::Fixity(d) => Declaration::Fixity(d),
            Declaration::Class(d) => Declaration::Class(d.map_snd(f)),
            Declaration::Instance(d) => Declaration::Instance(d.map_snd(f)),
            Declaration::Function(d) => Declaration::Function(d.map_snd(f)),
            Declaration::Newtype(d) => Declaration::Newtype(d.map_snd(f)),
            Declaration::Attribute(d) => Declaration::Attribute(d.map_snd(f)),
        }
    }
}
