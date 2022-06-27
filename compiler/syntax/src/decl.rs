use wy_common::{Map, Mappable};
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> Constructor<X, T> {
        Constructor {
            parent: f(self.parent),
            name: f(self.name),
            tag: self.tag,
            arity: self.arity,
            tipo: self.tipo.map_id(&mut f),
        }
    }
    pub fn map_id_ref<X>(&self, mut f: impl FnMut(&Id) -> X) -> Constructor<X, T>
    where
        T: Copy,
    {
        Constructor {
            parent: f(&self.parent),
            name: f(&self.name),
            tag: self.tag,
            arity: self.arity,
            tipo: self.tipo.map_id_ref(&mut f),
        }
    }
    pub fn map_t<X>(self, mut f: impl FnMut(T) -> X) -> Constructor<Id, X> {
        Constructor {
            parent: self.parent,
            name: self.name,
            tag: self.tag,
            arity: self.arity,
            tipo: self.tipo.map_t(&mut f),
        }
    }
    pub fn map_t_ref<X>(&self, f: &mut impl FnMut(&T) -> X) -> Constructor<Id, X>
    where
        Id: Copy,
    {
        Constructor {
            parent: self.parent,
            name: self.name,
            tag: self.tag,
            arity: self.arity,
            tipo: self.tipo.map_t_ref(f),
        }
    }
}

///
/// ```wysk
/// ~~        `name` `poly`
/// ~~           V   /
/// data |A a| Foo a
/// ~~    ^^^
/// ~~   `ctxt`
///     = Bar a
/// ~~    ^^^^^
/// ~~   `vnts[0]`
///     | Baz a (Foo a)
/// ~~    ^^^^^^^^^^^^^
/// ~~   `vnts[1]`
///     with (B, C, D);
/// ~~       ^^^^^^^^
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
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

    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> DataDecl<X, T> {
        DataDecl {
            name: f(self.name),
            poly: self.poly,
            ctxt: self.ctxt.fmap(|ctxt| ctxt.map_id(|id| f(id))),
            vnts: self.vnts.fmap(|v| v.map_id(|id| f(id))),
            with: self.with.fmap(|id| f(id)),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> DataDecl<X, T>
    where
        T: Copy,
    {
        DataDecl {
            name: f(&self.name),
            poly: self.poly.clone(),
            ctxt: self.context_iter().map(|ctxt| ctxt.map_id_ref(f)).collect(),
            vnts: self.variants_iter().map(|v| v.map_id_ref(f)).collect(),
            with: self.derives_iter().map(|id| f(id)).collect(),
        }
    }

    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> DataDecl<Id, U> {
        DataDecl {
            name: self.name,
            poly: self.poly.fmap(|t| f(t)),
            ctxt: self.ctxt.fmap(|c| c.map_t(|t| f(t))),
            vnts: self.vnts.fmap(|v| v.map_t(|t| f(t))),
            with: self.with,
        }
    }
    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> DataDecl<Id, U>
    where
        Id: Copy,
    {
        DataDecl {
            name: self.name,
            poly: self.poly_iter().map(|t| f(t)).collect(),
            ctxt: self
                .context_iter()
                .map(|Context { class, head: tyvar }| Context {
                    class: *class,
                    head: f(tyvar),
                })
                .collect(),
            vnts: self
                .variants_iter()
                .map(
                    |Variant {
                         name,
                         tag,
                         arity,
                         args,
                     }| Variant {
                        name: *name,
                        arity: *arity,
                        tag: *tag,
                        args: args.into_iter().map(|ty| ty.map_t_ref(f)).collect(),
                    },
                )
                .collect(),
            with: self.with.clone(),
        }
    }

    pub fn duplicates(&self) -> Option<Vec<(usize, Id)>>
    where
        Id: Copy + PartialEq,
    {
        get_dupe_ids!(for self.variant_names().enumerate())
    }
}

impl DataDecl {
    pub fn normalize(self) -> DataDecl<Ident, Tv> {
        let DataDecl {
            name,
            poly,
            ctxt,
            vnts,
            with,
        } = self;
        let pair = poly
            .into_iter()
            .zip(0..)
            .map(|(v, i)| (Tv::from_ident(v), Tv(i)))
            .collect::<Map<_, _>>();
        let ctxt = ctxt.fmap(|Context { class, head: tyvar }| Context {
            class,
            head: pair[&Tv::from_ident(tyvar)],
        });
        let vnts = vnts.fmap(
            |Variant {
                 name,
                 arity,
                 tag,
                 args,
             }| Variant {
                name,
                arity,
                tag,
                args: args.fmap(|ty| ty.map_t(&mut |f| pair[&Tv::from_ident(f)])),
            },
        );
        let mut poly = pair.into_iter().map(|(_, tv)| tv).collect::<Vec<_>>();
        poly.sort();
        DataDecl {
            name,
            with,
            poly,
            vnts,
            ctxt,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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

    /// Apply a closure to inner values of type parameter `Id`, mapping a
    /// `Variant<Id, T>` to a `Variant<Id, U>` for some given closure `f :: T ->
    /// U`. This type parameter corresponds to the *identifier representation*,
    /// and ranges over the `name` and `args` field.r
    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> Variant<X, T> {
        Variant {
            name: f(self.name),
            args: self.args.into_iter().map(|ty| ty.map_id(&mut f)).collect(),
            tag: self.tag,
            arity: self.arity,
        }
    }

    pub fn map_id_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> Variant<U, T>
    where
        T: Copy,
    {
        Variant {
            name: f(&self.name),
            args: self.args_iter().map(|ty| ty.map_id_ref(f)).collect(),
            tag: self.tag,
            arity: self.arity,
        }
    }

    /// Apply a closure to inner values of type parameter `T`, mapping a
    /// `Variant<Id, T>` to a `Variant<Id, U>` for some given closure `f :: T ->
    /// U`. This type parameter corresponds to the *type variable
    /// representation* of the underlying `Type` arguments in the field `args`.
    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> Variant<Id, U> {
        Variant {
            name: self.name,
            args: self.args.into_iter().map(|ty| ty.map_t(&mut f)).collect(),
            tag: self.tag,
            arity: self.arity,
        }
    }

    /// Alternative version of `map_t` that takes the receiver by reference
    /// instead of by value. This allows for mapping (and effectively copying)
    /// without taking ownership of `Self`.
    ///
    /// Note that in order for this method to be available, both type parameters
    /// `Id` and `T` must implement `Copy`.
    pub fn map_t_ref<F, U>(&self, mut f: F) -> Variant<Id, U>
    where
        F: FnMut(&T) -> U,
        Id: Copy,
        T: Copy,
    {
        let Variant {
            name,
            args,
            tag,
            arity,
        } = self;
        let args = args.into_iter().map(|ty| ty.map_t_ref(&mut f)).collect();
        Variant {
            name: *name,
            args,
            tag: *tag,
            arity: *arity,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

    pub fn map_id<F, X>(self, mut f: F) -> AliasDecl<X, T>
    where
        F: FnMut(Id) -> X,
    {
        AliasDecl {
            name: f(self.name),
            poly: self.poly,
            sign: self.sign.map_id(f),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> AliasDecl<X, T>
    where
        T: Copy,
    {
        AliasDecl {
            name: f(&self.name),
            poly: self.poly.clone(),
            sign: self.sign.map_id_ref(f),
        }
    }

    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> AliasDecl<Id, U> {
        AliasDecl {
            name: self.name,
            poly: self.poly.into_iter().map(|t| f(t)).collect(),
            sign: self.sign.map_t(&mut f),
        }
    }
    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> AliasDecl<Id, U>
    where
        Id: Copy,
    {
        AliasDecl {
            name: self.name,
            poly: self.poly_iter().map(|t| f(t)).collect(),
            sign: self.sign.map_t_ref(f),
        }
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
#[derive(Clone, Debug, PartialEq, Eq)]
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

impl<Id, T> NewtypeArg<Id, T> {
    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> NewtypeArg<X, T> {
        match self {
            NewtypeArg::Stacked(ts) => {
                NewtypeArg::Stacked(ts.into_iter().map(|ty| ty.map_id(&mut f)).collect())
            }
            NewtypeArg::Record(k, ss) => NewtypeArg::Record(f(k), ss.map_id(|id| f(id))),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> NewtypeArg<X, T>
    where
        T: Copy,
    {
        match self {
            NewtypeArg::Stacked(ts) => {
                NewtypeArg::Stacked(ts.into_iter().map(|t| t.map_id_ref(f)).collect())
            }
            NewtypeArg::Record(k, v) => NewtypeArg::Record(f(k), v.map_id_ref(f)),
        }
    }

    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> NewtypeArg<Id, U> {
        match self {
            NewtypeArg::Stacked(ts) => {
                NewtypeArg::Stacked(ts.into_iter().map(|ty| ty.map_t(&mut f)).collect())
            }
            NewtypeArg::Record(k, sig) => NewtypeArg::Record(k, sig.map_t(&mut f)),
        }
    }

    pub fn map_t_ref<X>(&self, f: &mut impl FnMut(&T) -> X) -> NewtypeArg<Id, X>
    where
        Id: Copy,
    {
        match self {
            NewtypeArg::Stacked(ts) => {
                NewtypeArg::Stacked(ts.into_iter().map(|t| t.map_t_ref(f)).collect())
            }
            NewtypeArg::Record(k, v) => NewtypeArg::Record(*k, v.map_t_ref(f)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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

impl<Id, T> NewtypeDecl<Id, T> {
    pub fn map_id<U>(self, mut f: impl FnMut(Id) -> U) -> NewtypeDecl<U, T> {
        NewtypeDecl {
            name: f(self.name),
            poly: self.poly,
            ctor: f(self.ctor),
            narg: self.narg.map_id(|id| f(id)),
            with: self.with.fmap(|id| f(id)),
        }
    }
    pub fn map_id_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> NewtypeDecl<U, T>
    where
        T: Copy,
    {
        NewtypeDecl {
            name: f(&self.name),
            poly: self.poly.clone(),
            ctor: f(&self.ctor),
            narg: self.narg.map_id_ref(f),
            with: self.derives_iter().map(|id| f(id)).collect(),
        }
    }
    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> NewtypeDecl<Id, U> {
        NewtypeDecl {
            name: self.name,
            poly: self.poly.into_iter().map(|t| f(t)).collect(),
            ctor: self.ctor,
            narg: self.narg.map_t(f),
            with: self.with,
        }
    }
    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> NewtypeDecl<Id, U>
    where
        Id: Copy,
    {
        NewtypeDecl {
            name: self.name,
            poly: self.poly_iter().map(|t| f(t)).collect(),
            ctor: self.ctor,
            narg: self.narg.map_t_ref(f),
            with: self.with.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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

    pub fn map_id<X>(self, f: &mut impl FnMut(Id) -> X) -> ClassDecl<X, T> {
        ClassDecl {
            name: f(self.name),
            poly: self.poly,
            ctxt: self.ctxt.fmap(|ctx| ctx.map_id(|id| f(id))),
            defs: self.defs.fmap(|defs| defs.map_id(f)),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> ClassDecl<X, T>
    where
        T: Copy,
    {
        ClassDecl {
            name: f(&self.name),
            poly: self.poly.clone(),
            ctxt: self.context_iter().map(|ctx| ctx.map_id_ref(f)).collect(),
            defs: self.methods_iter().map(|defs| defs.map_id_ref(f)).collect(),
        }
    }

    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> ClassDecl<Id, U> {
        ClassDecl {
            name: self.name,
            poly: self.poly.into_iter().map(|t| f(t)).collect(),
            ctxt: self
                .ctxt
                .into_iter()
                .map(|ctx| ctx.map_t(|t| f(t)))
                .collect(),
            defs: self.defs.into_iter().map(|m| m.map_t(|t| f(t))).collect(),
        }
    }

    pub fn map_t_ref<X>(&self, f: &mut impl FnMut(&T) -> X) -> ClassDecl<Id, X>
    where
        Id: Copy,
    {
        ClassDecl {
            name: self.name,
            poly: self.poly_iter().map(|t| f(t)).collect(),
            ctxt: self.context_iter().map(|ctx| ctx.map_t_ref(f)).collect(),
            defs: self
                .methods_iter()
                .map(|method| method.map_t_ref(f))
                .collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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

    pub fn map_id<X>(self, f: &mut impl FnMut(Id) -> X) -> InstDecl<X, T> {
        InstDecl {
            name: f(self.name),
            tipo: self.tipo.map_id(f),
            ctxt: self
                .ctxt
                .into_iter()
                .map(|ctx| ctx.map_id(|id| f(id)))
                .collect(),
            defs: self.defs.into_iter().map(|bind| bind.map_id(f)).collect(),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> InstDecl<X, T>
    where
        T: Copy,
    {
        InstDecl {
            name: f(&self.name),
            tipo: self.tipo.map_id_ref(f),
            ctxt: self.context_iter().map(|ctx| ctx.map_id_ref(f)).collect(),
            defs: self
                .bindings_iter()
                .map(|bind| bind.map_id_ref(f))
                .collect(),
        }
    }

    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> InstDecl<Id, U> {
        InstDecl {
            name: self.name,
            tipo: self.tipo.map_t(&mut f),
            ctxt: self
                .ctxt
                .into_iter()
                .map(|ctx| ctx.map_t(|t| f(t)))
                .collect(),
            defs: self.defs.into_iter().map(|b| b.map_t(&mut f)).collect(),
        }
    }

    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> InstDecl<Id, U>
    where
        Id: Copy,
    {
        InstDecl {
            name: self.name,
            tipo: self.tipo.map_t_ref(f),
            ctxt: self.context_iter().map(|ctx| ctx.map_t_ref(f)).collect(),
            defs: self.bindings_iter().map(|bind| bind.map_t_ref(f)).collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
    pub fn map_id<U>(self, f: &mut impl FnMut(Id) -> U) -> FnDecl<U, T> {
        FnDecl {
            name: f(self.name),
            sign: self.sign.map(|sig| sig.map_id(|id| f(id))),
            defs: self.defs.into_iter().map(|m| m.map_id(f)).collect(),
        }
    }

    pub fn has_tysig(&self) -> bool {
        self.sign.is_some()
    }

    pub fn sign_iter(&self) -> std::option::Iter<'_, Signature<Id, T>> {
        self.sign.iter()
    }

    pub fn map_id_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> FnDecl<U, T>
    where
        T: Copy,
    {
        FnDecl {
            name: f(&self.name),
            sign: self.sign.as_ref().map(|sig| sig.map_id_ref(f)),
            defs: self.defs_iter().map(|m| m.map_id_ref(f)).collect(),
        }
    }
    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> FnDecl<Id, U> {
        FnDecl {
            name: self.name,
            sign: self.sign.map(|sig| sig.map_t(&mut |t| f(t))),
            defs: self
                .defs
                .into_iter()
                .map(|m| m.map_t(&mut |t| f(t)))
                .collect(),
        }
    }

    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> FnDecl<Id, U>
    where
        Id: Copy,
    {
        FnDecl {
            name: self.name,
            sign: if let Some(sig) = &self.sign {
                Some(sig.map_t_ref(f))
            } else {
                None
            },
            defs: self.defs_iter().map(|m| m.map_t_ref(f)).collect(),
        }
    }
}

/// Equivalent to a subset of a `MethodDef` instance, flattening all data
/// structures, i.e., moving fields from `Signature` directly to `Interface`
#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

    pub fn map_id<U>(self, f: &mut impl FnMut(Id) -> U) -> MethodDef<U, T> {
        MethodDef {
            name: f(self.name),
            sign: self.sign.map_id(|id| f(id)),
            body: self.body.fmap(|m| m.map_id(f)),
        }
    }

    pub fn map_id_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> MethodDef<U, T>
    where
        T: Copy,
    {
        MethodDef {
            name: f(&self.name),
            sign: self.sign.map_id_ref(f),
            body: self.body_iter().map(|m| m.map_id_ref(f)).collect(),
        }
    }

    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> MethodDef<Id, U> {
        MethodDef {
            name: self.name,
            sign: self.sign.map_t(&mut f),
            body: self.body.fmap(|m| m.map_t(&mut f)),
        }
    }

    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> MethodDef<Id, U>
    where
        Id: Copy,
    {
        MethodDef {
            name: self.name,
            sign: self.sign.map_t_ref(f),
            body: self.body_iter().map(|m| m.map_t_ref(f)).collect(),
        }
    }

    pub fn into_method(self) -> Method<Id, T> {
        Method::Sig(self.name, self.sign)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
    pub fn map_id<U>(self, f: &mut impl FnMut(Id) -> U) -> MethodImpl<U, T> {
        MethodImpl(self.0.map_id(f))
    }
    pub fn map_id_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> MethodImpl<U, T>
    where
        T: Copy,
    {
        MethodImpl(self.0.map_id_ref(f))
    }
    pub fn map_t<U>(self, f: &mut impl FnMut(T) -> U) -> MethodImpl<Id, U> {
        MethodImpl(self.0.map_t(f))
    }
    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> MethodImpl<Id, U>
    where
        Id: Copy,
    {
        MethodImpl(self.0.map_t_ref(f))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
    pub fn map_id<X, F>(self, f: &mut impl FnMut(Id) -> X) -> Method<X, T> {
        match self {
            Method::Sig(id, sig) => Method::Sig(f(id), sig.map_id(|id| f(id))),
            Method::Impl(binding) => Method::Impl(binding.map_id(f)),
        }
    }
    pub fn map_id_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> Method<U, T>
    where
        T: Copy,
    {
        match self {
            Method::Sig(id, sig) => Method::Sig(f(id), sig.map_id_ref(f)),
            Method::Impl(binding) => Method::Impl(binding.map_id_ref(f)),
        }
    }
    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> Method<Id, U> {
        match self {
            Method::Sig(id, sig) => Method::Sig(id, sig.map_t(&mut f)),
            Method::Impl(binding) => Method::Impl(binding.map_t(&mut f)),
        }
    }
    pub fn map_t_ref<F, U>(&self, f: &mut impl FnMut(&T) -> U) -> Method<Id, U>
    where
        Id: Copy,
    {
        match self {
            Method::Sig(id, sig) => Method::Sig(*id, sig.map_t_ref(f)),
            Method::Impl(binding) => Method::Impl(binding.map_t_ref(f)),
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
