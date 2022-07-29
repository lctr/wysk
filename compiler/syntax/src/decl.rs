use serde::{Deserialize, Serialize};
use wy_common::Map;
use wy_name::ident::{Ident, Identifier};

pub use wy_lexer::{
    comment::{self, Comment},
    Literal,
};

use crate::{attr::*, fixity::*, stmt::*, tipo::*};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixityDecl<Id = Ident> {
    pub infixes: Vec<Id>,
    pub fixity: Fixity,
}

macro_rules! get_dupe_ids {
    (for $ex:expr) => {{
        let mut dupes = vec![];
        let mut seen = vec![];
        for (idx, item) in $ex {
            if seen.contains(&item) {
                dupes.push((idx, *item))
            } else {
                seen.push(item)
            }
        }
        if dupes.is_empty() {
            None
        } else {
            Some(dupes)
        }
    }};
}

impl<Id> FixityDecl<Id> {
    pub fn new(assoc: Assoc, prec: Prec, infixes: Vec<Id>) -> Self {
        Self {
            infixes,
            fixity: Fixity { assoc, prec },
        }
    }
    pub fn infixes_iter(&self) -> std::slice::Iter<'_, Id> {
        self.infixes.iter()
    }

    pub fn duplicates(&self) -> Option<Vec<(usize, Id)>>
    where
        Id: Copy + PartialEq,
    {
        get_dupe_ids!(for self.infixes_iter().enumerate())
    }

    pub fn contains_id(&self, infix_id: &Id) -> bool
    where
        Id: PartialEq,
    {
        self.infixes.contains(infix_id)
    }
    pub fn map<F, T>(self, f: F) -> FixityDecl<T>
    where
        F: FnMut(Id) -> T,
    {
        FixityDecl {
            infixes: self.infixes.into_iter().map(f).collect(),
            fixity: self.fixity,
        }
    }

    pub fn map_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> FixityDecl<X> {
        FixityDecl {
            infixes: self.infixes_iter().map(|id| f(id)).collect(),
            fixity: self.fixity,
        }
    }

    /// Returns an iterator of (infix, fixity) pairs.
    pub fn distribute(&self) -> impl Iterator<Item = (Id, Fixity)> + '_
    where
        Id: Copy,
    {
        self.infixes.iter().map(|infix| (*infix, self.fixity))
    }
}

impl<Id: Copy + Eq + std::hash::Hash> From<&[FixityDecl<Id>]> for FixityTable<Id> {
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Constructor<Id, T> {
    pub parent: Id,
    pub name: Id,
    pub tag: Tag,
    pub arity: Arity,
    pub tipo: Type<Id, T>,
}

wy_common::struct_getters! {
    |Id, T| Constructor<Id, T>
    | parent => get_parent :: Id
    | name => get_name :: Id
    | tag => get_tag :: Tag
    | arity => get_arity :: Arity
    | tipo => get_tipo :: Type<Id, T>
}

impl<Id, T> Constructor<Id, T> {
    pub fn ty_vars(&self) -> impl Iterator<Item = Var<T>>
    where
        T: Eq + Copy,
    {
        self.tipo.enumerate()
    }

    pub fn var_map(&self) -> Map<T, Tv>
    where
        T: Eq + Copy + std::hash::Hash,
    {
        self.ty_vars().map(Var::as_pair).collect()
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
/// | `ctxt` | classes of which type variables must be instances     |
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
/// ~~    ctxt name poly
/// ~~     🡓   🡓  🡓
/// data |A a| Foo a
///     = Bar a          ~~ variant 0
///     | Baz a (Foo a)  ~~ variant 1
///     with (A, B, C);  ~~ with (deriving) clause
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DataDecl<Id = Ident, T = Ident> {
    pub name: Id,
    pub poly: Vec<T>,
    pub ctxt: Vec<Context<Id, T>>,
    pub vnts: Vec<Variant<Id, T>>,
    pub with: Vec<Id>,
}

wy_common::struct_field_iters! {
    |Id, T| DataDecl<Id, T>
    | poly => poly_iter :: T
    | ctxt => context_iter :: Context<Id, T>
    | vnts => variants_iter :: Variant<Id, T>
    | with => derives_iter :: Id
}

pub const TAG_MIN: u32 = 1;

impl<Id, T> DataDecl<Id, T> {
    pub fn constructor_types(&self) -> Vec<Constructor<Id, T>>
    where
        Id: Copy,
        T: Copy,
    {
        let data_ty = Type::Con(
            Con::Data(self.name),
            self.poly_iter().map(|t| Type::Var(*t)).collect(),
        );
        self.variants_iter()
            .map(|variant| {
                let tipo = variant.fun_ty(data_ty.clone());
                Constructor {
                    parent: self.name,
                    name: variant.name,
                    tag: variant.tag,
                    arity: variant.arity,
                    tipo,
                }
            })
            .collect()
    }

    /// Checks whether every data constructor is polymorphic over at *most* the
    /// type variables in the `poly` field, i.e.,  every type variable in every
    /// variant in the `vnts` field, as well as every type variable in the
    /// `ctxt` field, is contained in the `poly` field.
    pub fn no_unbound_tyvars(&self) -> bool
    where
        T: Copy + PartialEq,
        Id: Identifier,
    {
        self.class_vars().all(|tv| self.depends_on(&tv))
            && self.variants_iter().all(|vnt| {
                vnt.args_iter()
                    .all(|ty| ty.fv().iter().all(|tv| self.depends_on(tv)))
            })
    }

    /// Identifies whether the data type defined by this data declaration is
    /// parametrized over the given type variable, i.e., whether a type variable
    /// is contained in the `poly` field by testing a reference for containment.
    #[inline]
    pub fn depends_on(&self, var: &T) -> bool
    where
        T: PartialEq,
    {
        self.poly.contains(var)
    }

    #[inline]
    pub fn get_ctxt(&self, id: &Id) -> Option<&Context<Id, T>>
    where
        Id: PartialEq,
    {
        self.ctxt.iter().find(|c| c.class == *id)
    }

    #[inline]
    pub fn get_variant(&self, id: &Id) -> Option<&Variant<Id, T>>
    where
        Id: PartialEq,
    {
        self.vnts.iter().find(|v| v.name == *id)
    }

    #[inline]
    pub fn find_variant<F>(&self, f: F) -> Option<&Variant<Id, T>>
    where
        F: FnMut(&&Variant<Id, T>) -> bool,
    {
        self.vnts.iter().find(f)
    }

    pub fn get_variant_by_tag(&self, tag: &Tag) -> Option<&Variant<Id, T>> {
        let idx = tag.0 as usize;
        if self.vnts.len() <= idx {
            None
        } else {
            Some(&self.vnts[idx - (TAG_MIN as usize)])
        }
    }

    #[inline]
    pub fn variant_names(&self) -> impl Iterator<Item = &Id> + '_ {
        self.vnts.iter().map(|v| &v.name)
    }

    #[inline]
    pub fn class_names(&self) -> impl Iterator<Item = &Id> + '_ {
        self.ctxt.iter().map(|c| &c.class)
    }

    #[inline]
    pub fn class_vars(&self) -> impl Iterator<Item = &T> + '_ {
        self.context_iter().map(|Context { head: tyvar, .. }| tyvar)
    }

    #[inline]
    pub fn derived_names(&self) -> impl Iterator<Item = &Id> + '_ {
        self.with.iter()
    }

    pub fn enumer_tags(mut self) -> Self {
        for (n, Variant { tag, .. }) in self.vnts.iter_mut().enumerate() {
            *tag = Tag(n as u32 + TAG_MIN);
        }
        self
    }

    pub fn duplicates(&self) -> Option<Vec<(usize, Id)>>
    where
        Id: Copy + PartialEq,
    {
        get_dupe_ids!(for self.variant_names().enumerate())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Variant<Id = Ident, T = Ident> {
    pub name: Id,
    pub args: Vec<Type<Id, T>>,
    pub tag: Tag,
    pub arity: Arity,
}

impl<Id, T> Variant<Id, T> {
    /// Returns the function type corresponding to this data constructor. Note
    /// that it requires the  "constructed" type.
    ///
    /// A constructed datatype `T a1 a2 ... an`, where `a1`, `a2`, ..., `an` are
    /// type variables (if any) over which the type `T` is parametrized, may be
    /// constructed by any of its data constructors `C` and their respective
    /// arguments.
    ///
    /// A data constructor `C` has an *arity* equal to the number of arguments
    /// it takes, *regardless* of how many type variables it may range over.
    /// Furthermore, every data constructor is effectively a *function* from its
    /// arguments (curried) to the data type they construct.
    ///
    /// The data type `Foo a b` defined below is constructed with *four*
    /// variants, each funtions of their arguments.
    /// ```wysk
    /// data Foo a b = Zero | One a | Two a b | Three a b (a, b)
    /// ~~: Zero :: Foo a b
    /// ~~: One :: a -> Foo a b
    /// ~~: Two :: a -> b -> Foo a b
    /// ~~: Three :: a -> b -> (a, b) -> Foo a b
    /// ```
    pub fn fun_ty(&self, data_ty: Type<Id, T>) -> Type<Id, T>
    where
        Id: Clone,
        T: Copy,
    {
        if self.args.is_empty() {
            return data_ty;
        };

        self.args
            .clone()
            .into_iter()
            .rev()
            .fold(data_ty, |a, c| Type::Fun(Box::new(c), Box::new(a)))
    }

    /// Same as `con_ty`, but for the concrete type with `Id = Ident` and `T =
    /// Tv`. Hence it requires a reference to the data type `Type<Ident, Tv>`
    /// and will return another `Type<Ident, Tv>` corresponding to the function
    /// type of this variant/constructor.
    pub fn function_type(
        variant: Variant<Ident, Tv>,
        data_type: &Type<Ident, Tv>,
    ) -> Type<Ident, Tv> {
        variant
            .args
            .into_iter()
            .rev()
            .fold(data_type.clone(), |a, c| {
                Type::Fun(Box::new(c), Box::new(a))
            })
    }

    pub fn args_iter(&self) -> std::slice::Iter<'_, Type<Id, T>> {
        self.args.iter()
    }

    pub fn args_iter_mut(&mut self) -> std::slice::IterMut<'_, Type<Id, T>> {
        self.args.iter_mut()
    }

    pub fn find_arg(&self, predicate: impl FnMut(&&Type<Id, T>) -> bool) -> Option<&Type<Id, T>> {
        self.args_iter().find(predicate)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Tag(pub u32);

impl Default for Tag {
    fn default() -> Self {
        Self(0)
    }
}

impl std::fmt::Debug for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Tag({})", &self.0)
    }
}

impl std::fmt::Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Tag({})", &self.0)
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

    /// Shortcut to check whether a given item takes a *single* argument.
    pub fn is_one(self) -> bool {
        self.0 == 1
    }

    /// Shortcut for checking whether the `Arity` of a given item is larger than
    /// one. If so, then it is implied that whatever this `Arity` belongs to
    /// must be curried.
    pub fn curries(self) -> bool {
        self.0 > 1
    }

    /// Since `Arity` is essentially a `usize` wrapper corresponding to the
    /// *number of __arguments__*, this method makes it easy to compare an arity
    /// with any type `T` that implements `ExactSizeIterator` (i.e., has a `len`
    /// method).
    pub fn cmp_len<I>(&self, iter: I) -> std::cmp::Ordering
    where
        I: ExactSizeIterator,
    {
        let n = self.0;
        n.cmp(&iter.len())
    }

    pub fn increment(&mut self) {
        self.0 += 1;
    }

    pub fn decrement(&mut self) {
        if !self.is_zero() {
            self.0 -= 1
        }
    }
}

// make it easy to compare Arity using usizes by implementing PartialEq<usize>
// and PartialOrd<usize>
wy_common::newtype!(Arity | usize | PartialEq);
wy_common::newtype!(Arity | usize | PartialOrd);
wy_common::newtype!(Arity | usize | (+= usize |rhs| rhs) );

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AliasDecl<Id = Ident, T = Ident> {
    pub name: Id,
    pub poly: Vec<T>,
    pub sign: Signature<Id, T>,
}

wy_common::struct_field_iters! {
    |Id, T| AliasDecl<Id, T>
    | poly => poly_iter :: T
}

impl<Id, T> AliasDecl<Id, T> {
    pub fn get_contexts_iter(&self) -> std::slice::Iter<'_, Context<Id, T>> {
        self.sign.ctxt.iter()
    }

    pub fn duplicate_tyvars(&self) -> Option<Vec<(usize, T)>>
    where
        T: Copy + PartialEq,
    {
        get_dupe_ids!(for self.poly.iter().enumerate())
    }

    pub fn enumerate_tyvars(&self) -> impl Iterator<Item = (usize, &T)> + '_ {
        self.poly.iter().enumerate()
    }

    pub fn no_unused_tyvars(&self) -> bool
    where
        T: Copy + PartialEq,
        Id: Identifier,
    {
        let fvs = self.sign.tipo.fv();
        self.poly.iter().all(|tv| fvs.contains(tv))
    }

    pub fn no_unused_tyvars_in_ctxts(&self) -> bool
    where
        T: Copy + PartialEq,
        Id: Identifier,
    {
        let fvs = self.sign.tipo.fv();
        self.sign.ctxt.iter().all(|ctx| fvs.contains(&ctx.head))
    }

    /// Checks whether all type variables in the `Type` (right-hand-side) are
    /// declared as type variables for the type alias.
    ///
    /// For example, `type Foo a b = |Baz a| (a -> b) -> c` would fail and this method
    /// would return `false`, as `c` is not included in the left-hand-side of
    /// the type alias declaration.
    pub fn no_new_tyvar_in_type(&self) -> bool
    where
        T: Copy + PartialEq,
        Id: Identifier,
    {
        self.sign
            .tipo
            .fv()
            .into_iter()
            .chain(self.sign.ctxt.iter().map(|ctx| ctx.head))
            .all(|t| self.poly.contains(&t))
    }
}

/// `Newtype`s allow for *renaming* of types. Ideally little to no overhead is
/// involved in working with newtypes, as the "type renaming" of a newtype is
/// effectively forgotten post-typechecking. A newtype declaration is helpful
/// for discriminating against various "uses" of a single type. For example, it
/// is perfectly acceptable to use a type alias to distinguish between numerical
/// units, however this does not provide a safeguard against inconsistencies!
///
/// Like data variants, `Newtype` variants define constructors -- HOWEVER, *only
/// one* constructor is accepted! A `Product` variant corresponds to a single
/// data constructor with (arbitrarily many) arguments, while a `Record` variant
/// corresponds to a single constructor *associated with* a selector function,
/// whose signature is included in the variant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NewtypeArg<Id = Ident, T = Ident> {
    /// Used when the newtype constructor is *not* a record and instead takes
    /// multiple type arguments, such as `newtype Foo a = Bar a`
    Stacked(Vec<Type<Id, T>>),
    /// Used when the newtype constructor is a single-entry record. The label
    /// for this constructor defines the function used to "lift" a computation
    /// or value into the newtype, such as `newtype Foo a = Foo { foo :: a }`
    Record(Id, Signature<Id, T>),
}

wy_common::variant_preds! {
    NewtypeArg
    | is_stacked => Stacked(_)
    | is_record => Record(..)
}

impl<Id, T> NewtypeArg<Id, T> {}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NewtypeDecl<Id = Ident, T = Ident> {
    pub name: Id,
    pub poly: Vec<T>,
    pub ctor: Id,
    pub narg: NewtypeArg<Id, T>,
    pub with: Vec<Id>,
}

wy_common::struct_field_iters! {
    |Id, T| NewtypeDecl<Id, T>
    | poly => poly_iter :: T
    | with => derives_iter :: Id
}

impl<Id, T> NewtypeDecl<Id, T> {}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassDecl<Id = Ident, T = Ident> {
    pub name: Id,
    pub poly: Vec<T>,
    pub ctxt: Vec<Context<Id, T>>,
    pub defs: Vec<MethodDef<Id, T>>,
}

wy_common::struct_field_iters! {
    |Id, T| ClassDecl<Id, T>
    | poly => poly_iter :: T
    | ctxt => context_iter :: Context<Id, T>
    | defs => methods_iter :: MethodDef<Id, T>
}

impl<Id, T> ClassDecl<Id, T> {
    pub fn item_names(&self) -> impl Iterator<Item = &Id> + '_ {
        self.defs.iter().map(|MethodDef { name, .. }| name)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InstDecl<Id = Ident, T = Ident> {
    pub name: Id,
    pub tipo: Type<Id, T>,
    pub ctxt: Vec<Context<Id, T>>,
    pub defs: Vec<Binding<Id, T>>,
}

wy_common::struct_field_iters! {
    |Id, T| InstDecl<Id, T>
    | ctxt => context_iter :: Context<Id, T>
    | defs => bindings_iter :: Binding<Id, T>
}

impl<Id, T> InstDecl<Id, T> {
    pub fn item_names(&self) -> impl Iterator<Item = &Id> + '_ {
        self.defs.iter().map(|Binding { name, .. }| name)
    }
    pub fn get_ctxt(&self, id: &Id) -> Option<&Context<Id, T>>
    where
        Id: PartialEq,
    {
        self.ctxt.iter().find(|ctx| ctx.class == *id)
    }

    pub fn get_def(&self, id: &Id) -> Option<&Binding<Id, T>>
    where
        Id: PartialEq,
    {
        self.defs.iter().find(|b| b.name == *id)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FnDecl<Id = Ident, T = Ident> {
    pub name: Id,
    pub sign: Option<Signature<Id, T>>,
    pub defs: Vec<Match<Id, T>>,
}

wy_common::struct_field_iters! {
    |Id, T| FnDecl<Id, T>
    | defs => defs_iter :: Match<Id, T>
}

impl<Id, T> FnDecl<Id, T> {
    pub fn has_tysig(&self) -> bool {
        self.sign.is_some()
    }

    pub fn sign_iter(&self) -> std::option::Iter<'_, Signature<Id, T>> {
        self.sign.iter()
    }
}

/// Equivalent to a subset of a `MethodDef` instance, flattening all data
/// structures, i.e., moving fields from `Signature` directly to `Interface`
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Interface<Id = Ident, T = Id> {
    pub name: Id,
    pub each: Vec<T>,
    pub ctxt: Vec<Context<Id, T>>,
    pub tipo: Type<Id, T>,
}

wy_common::struct_field_iters! {
    |Id, T| Interface<Id, T>
    | each => quant_iter :: T
    | ctxt => ctxt_iter :: Context<Id, T>
}

impl<Id, T> From<MethodDef<Id, T>> for (Interface<Id, T>, Vec<Match<Id, T>>) {
    fn from(method: MethodDef<Id, T>) -> Self {
        (
            Interface {
                name: method.name,
                each: method.sign.each,
                ctxt: method.sign.ctxt,
                tipo: method.sign.tipo,
            },
            method.body,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodDef<Id = Ident, T = Ident> {
    pub name: Id,
    pub sign: Signature<Id, T>,
    pub body: Vec<Match<Id, T>>,
}

wy_common::struct_field_iters! {
    |Id, T| MethodDef<Id, T>
    | body => body_iter :: Match<Id, T>
    | sign.ctxt => context_iter :: Context<Id, T>
}

impl<Id, T> MethodDef<Id, T> {
    pub fn context_iter_mut(&mut self) -> std::slice::IterMut<'_, Context<Id, T>> {
        self.sign.ctxt_iter_mut()
    }

    pub fn into_method(self) -> Method<Id, T> {
        Method::Sig(self.name, self.sign)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MethodImpl<Id = Ident, T = Ident>(pub Binding<Id, T>);
impl<Id, T> MethodImpl<Id, T> {
    pub fn new(binding: Binding<Id, T>) -> Self {
        Self(binding)
    }
    pub fn name(&self) -> &Id {
        &self.0.name
    }
    pub fn arms(&self) -> &[Match<Id, T>] {
        &self.0.arms[..]
    }
    pub fn arms_iter(&self) -> std::slice::Iter<'_, Match<Id, T>> {
        self.0.arms.iter()
    }
    pub fn arms_iter_mut(&mut self) -> std::slice::IterMut<'_, Match<Id, T>> {
        self.0.arms.iter_mut()
    }
    pub fn signature(&self) -> Option<&Signature<Id, T>> {
        self.0.tipo.as_ref()
    }
    pub fn into_method(self) -> Method<Id, T> {
        Method::Impl(self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Method<Id = Ident, T = Ident> {
    Sig(Id, Signature<Id, T>),
    Impl(Binding<Id, T>),
}

wy_common::variant_preds! {
    Method
    | is_sig => Sig(..)
    | is_impl => Impl(_)
}

impl<Id, T> Method<Id, T> {
    #[inline]
    pub fn is_signature(&self) -> bool {
        matches!(self, Self::Sig(..))
    }

    #[inline]
    pub fn name(&self) -> &Id {
        match self {
            Method::Sig(id, _) | Method::Impl(Binding { name: id, .. }) => id,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Declaration<Id = Ident, T = Ident> {
    Data(DataDecl<Id, T>),
    Alias(AliasDecl<Id, T>),
    Fixity(FixityDecl<Id>),
    Class(ClassDecl<Id, T>),
    Instance(InstDecl<Id, T>),
    Function(FnDecl<Id, T>),
    Newtype(NewtypeDecl<Id, T>),
    Attribute(Attribute<Id, T>),
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

impl<Id, T> Declaration<Id, T> {
    pub fn name(&self) -> &Id {
        match self {
            Declaration::Data(d) => &d.name,
            Declaration::Alias(a) => &a.name,
            Declaration::Fixity(f) => &f.infixes[0],
            Declaration::Class(c) => &c.name,
            Declaration::Instance(i) => &i.name,
            Declaration::Function(f) => &f.name,
            Declaration::Newtype(n) => &n.name,
            Declaration::Attribute(a) => a.name(),
        }
    }
}
