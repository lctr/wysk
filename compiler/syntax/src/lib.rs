use wy_common::{deque, newtypes::Newtype, Map, Mappable};
use wy_intern::symbol::{self, Symbol};

pub use wy_lexer::{
    comment::{self, Comment},
    Literal,
};

pub mod expr;
pub mod fixity;
pub mod ident;
pub mod mapper;
pub mod pattern;
pub mod stmt;
pub mod tipo;
pub mod visit;

use expr::*;
use fixity::*;
use ident::*;
use pattern::*;
use stmt::*;
use tipo::*;

// TODO: documentation; potential split-up of definitions into separate files?

wy_common::newtype!({ u64 in Uid | Show (+= usize |rhs| rhs as u64) });

#[derive(Clone, Debug)]
pub struct Ast {
    pub programs: Vec<Program>,
}

#[derive(Clone, Debug)]
pub struct Program<Id = Ident, U = (), T = Ident> {
    pub module: Module<Id, U, T>,
    pub fixities: FixityTable,
    pub comments: Vec<Comment>,
}

pub type RawProgram = Program<Ident, Option<std::path::PathBuf>, Ident>;
pub type FreshProgram<U = ()> = Program<Ident, U, Tv>;

macro_rules! impl_program {
    (
        $(
            $(|)? $field:ident : $typ:ident<$g0:tt $(,$gs:tt)?>, $method_name_iter:ident
            & $method_name_slice:ident
            $(: $map_t:ident)?
        )+
    ) => {
        $(
            impl<Id, U, T> Program<Id, U, T> {
                impl_program! {
                    # Iter<$typ<$g0 $(, $gs)*>>
                    | $field : $method_name_iter
                }
                impl_program! {
                    # [$typ<$g0 $(, $gs)*>]
                    | $field : $method_name_slice
                }
            }
        )+
    };
    (# Iter<$typ:ty> | $field:ident : $method_name:ident) => {
        pub fn $method_name(&self) -> std::slice::Iter<'_, $typ> {
            self.module.$field.iter()
        }
    };
    (# [$typ:ty] | $field:ident : $method_name:ident) => {
        pub fn $method_name(&self) -> &[$typ] {
            self.module.$field.as_slice()
        }
    };
}

impl_program! {
    | imports: ImportSpec<Id>, get_imports_iter & get_imports
    | infixes: FixityDecl<Id>, get_infixes_iter & get_infixes
    | fundefs: FnDecl<Id, T>, get_fundefs_iter & get_fundefs :map_t_fn_decl
    | datatys: DataDecl<Id, T>, get_datatys_iter & get_datatys
    | classes: ClassDecl<Id, T>, get_classes_iter & get_classes
    | implems: InstDecl<Id, T>, get_implems_iter & get_implems
    | aliases: AliasDecl<Id, T>, get_aliases_iter & get_aliases
    | newtyps: NewtypeDecl<Id, T>, get_newtyps_iter & get_newtyps
}

impl<Id, U, T> Program<Id, U, T> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module<Id = Ident, Uid = (), T = Ident> {
    pub uid: Uid,
    pub modname: Chain<Id>,
    pub imports: Vec<ImportSpec<Id>>,
    pub infixes: Vec<FixityDecl<Id>>,
    pub datatys: Vec<DataDecl<Id, T>>,
    pub classes: Vec<ClassDecl<Id, T>>,
    pub implems: Vec<InstDecl<Id, T>>,
    pub fundefs: Vec<FnDecl<Id, T>>,
    pub aliases: Vec<AliasDecl<Id, T>>,
    pub newtyps: Vec<NewtypeDecl<Id, T>>,
}

macro_rules! impl_functor {
    ($mapper:ident for struct
        #header $this:ident
        #arrow $ty_in:tt -> $ty_out:tt
        $(#params
            [$p0:tt $(, $prs:tt)*]
            [$gen:ty $(, $gens:ty)*]
            [$out:ty $(, $outs:ty)*]
        )?
        $(#bounds |
            $b0:ty : $tr0:ident $(+ $trs0:ident)*
            $(, $bs:ty: $tr1:ident $(+ $trs1:ident)*)*
            |
        )?
        #methods {
            $($field:ident $($tails:ident)* => $method_name:ident -> $ret_ty:ty)+
        }
        $(#fixed $id0:ident $(, $ids:ident)*)?
    ) => {
        impl $(<$p0 $(, $prs)*>)? $this $(<$gen $(, $gens)*>)?
        $(
            where
                $b0 : $tr0 $(+ $trs0)*
                $(, $bs: $tr1 $(+ $trs1)*)*
        )? {
            $(
                pub fn $method_name <$ty_out>(
                    self,
                    f: &mut impl FnMut($ty_in) -> $ty_out
                ) -> $ret_ty {
                    self.$field $(.$tails)* .fmap(|item| item.$mapper(|t| f(t)))
                }
            )+
            pub fn map_t<$ty_out>(self, mut f: impl FnMut($ty_in) -> $ty_out) -> $this $(<$out $(, $outs)*>)? {
                $(let $field = self.$field.fmap(|item| item.$mapper(&mut f));)+
                $(
                    let $id0 = self.$id0;
                    $(let $ids = self.$ids;)*
                )?
                $this {
                    $($id0 $(, $ids)*,)?
                    $($field ,)+
                }
            }
        }
    };
}

impl_functor! {
    map_t for struct
        #header Module
        #arrow T -> X
        #params [U, T] [Ident, U, T] [Ident, U, X]
        #bounds |T: Copy|
        #methods {
            datatys => map_t_datatys -> Vec<DataDecl<Ident, X>>
            classes => map_t_classes -> Vec<ClassDecl<Ident, X>>
            implems => map_t_implems -> Vec<InstDecl<Ident, X>>
            fundefs => map_t_fundefs -> Vec<FnDecl<Ident, X>>
            aliases => map_t_aliases -> Vec<AliasDecl<Ident, X>>
            newtyps => map_t_newtyps -> Vec<NewtypeDecl<Ident, X>>
        }
        #fixed uid, modname, imports, infixes
}

impl Default for Module {
    fn default() -> Self {
        Self {
            uid: (),
            modname: Chain::new(Ident::Upper(symbol::intern_once("Main")), deque![]),
            imports: vec![],
            infixes: vec![],
            datatys: vec![],
            classes: vec![],
            implems: vec![],
            fundefs: vec![],
            aliases: vec![],
            newtyps: vec![],
        }
    }
}

impl<Id, U, T> Module<Id, U, T> {
    pub fn with_uid<V>(self, uid: V) -> Module<Id, V, T> {
        Module {
            uid,
            modname: self.modname,
            imports: self.imports,
            infixes: self.infixes,
            datatys: self.datatys,
            classes: self.classes,
            implems: self.implems,
            fundefs: self.fundefs,
            aliases: self.aliases,
            newtyps: self.newtyps,
        }
    }
}

/// Describe the declared dependencies on other modules within a given module.
/// Every import spec brings into scope the entities corresponding to the
/// identifiers included.
///
/// When a module `A` imports entities from another module `B`, the items
/// imported from `B` are brought into scope for module `A`. Additionally,
/// module `A` will export by default imports from `B` unless the `ImportSpec`
/// for imports from `B` has a `hidden` value of `true`.
///
/// The module from which items are imported from may be *qualified* and/or
/// *renamed*. When a module is *qualified*, its imports are no longer
/// accessible without prefixing the module name. When a module is *qualified*
/// __and__ *renamed*, the module prefix necessary to access its imports is
/// restricted to matching the new name only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportSpec<Id = Ident> {
    pub name: Chain<Id>,
    pub qualified: bool,
    pub rename: Option<Id>,
    pub hidden: bool,
    pub imports: Vec<Import<Id>>,
}

impl<Id> ImportSpec<Id> {
    pub fn map<F, T>(self, mut f: F) -> ImportSpec<T>
    where
        F: FnMut(Id) -> T,
    {
        ImportSpec {
            name: self.name.map(|t| f(t)),
            qualified: self.qualified,
            rename: self.rename.map(|t| f(t)),
            hidden: self.hidden,
            imports: self
                .imports
                .into_iter()
                .map(|import| import.map(|i| f(i)))
                .collect(),
        }
    }

    pub fn get_imports(&self) -> &[Import<Id>] {
        self.imports.as_slice()
    }

    pub fn get_imports_iter(&self) -> std::slice::Iter<'_, Import<Id>> {
        self.imports.iter()
    }

    pub fn infix_deps(&self) -> impl Iterator<Item = &Import<Id>> {
        self.imports
            .iter()
            .filter(|imp| matches!(imp, Import::Operator(..)))
    }
}

/// Describe the named entity to be imported. When contained by an `ImportSpec`,
/// these imports may either be *public* if the `ImportSpec` has its `hidden`
/// field set to `false`. Otherwise, the imports will become accessible through
/// *multiple* namespaces. E.g., suppose module `A` imports the function `bar`,
/// the data type `Baz` along with all of its constructors from the module `B`,
/// and assume that the module `B` is not hidden. Then the function `bar` will
/// be accessible via the identifiers `B.bar` and `bar`, as well as having the
/// absolute path `A.B.bar`.
///
/// Note: At the parsing level, it is generally impossible to distinguish
/// between type imports, type constructor imports, and class imports, as they
/// all begin with uppercase letters. However, semantic context allows for bare
/// patterns that *may* indicate the specific kind an import may be. The terms
/// `Operator`, `Function`, `Abstract`, `Total`, and `Partial`
/// * Type aliases are always `Abstract`
///
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Import<Id = Ident> {
    /// Infix imports
    Operator(Id),
    Function(Id),
    /// Importing a type (without any of its constructors) or a class (without
    /// any of its methods).
    Abstract(Id),
    /// Data type imports that include *all* of their constructors
    Total(Id),
    /// Data type imports that include only the specified constructors, OR
    Partial(Id, Vec<Id>),
}

impl<Id> Import<Id> {
    pub fn map<F, T>(self, mut f: F) -> Import<T>
    where
        F: FnMut(Id) -> T,
    {
        match self {
            Import::Operator(id) => Import::Operator(f(id)),
            Import::Function(id) => Import::Function(f(id)),
            Import::Abstract(id) => Import::Abstract(f(id)),
            Import::Total(id) => Import::Total(f(id)),
            Import::Partial(root, rest) => {
                Import::Partial(f(root), rest.into_iter().map(f).collect())
            }
        }
    }
    /// If the import corresponds to an infix operator, then return the
    /// identifier wrapped in a `Some` variant. Otherwise, return `None`.
    pub fn infix_id(&self) -> Option<&Id> {
        if let Self::Operator(id) = self {
            Some(id)
        } else {
            None
        }
    }

    pub fn idents(&self) -> Vec<Id>
    where
        Id: Copy,
    {
        match self {
            Import::Operator(id)
            | Import::Function(id)
            | Import::Abstract(id)
            | Import::Total(id) => vec![*id],
            Import::Partial(head, ids) => {
                let mut h = Vec::with_capacity(ids.len() + 1);
                h.push(*head);
                h.extend(ids.iter().copied());
                h
            }
        }
    }
}

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

impl<Id, T> DataDecl<Id, T> {
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
                vnt.iter_args()
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
            Some(&self.vnts[idx])
        }
    }

    #[inline]
    pub fn poly_iter(&self) -> std::slice::Iter<'_, T> {
        self.poly.iter()
    }

    #[inline]
    pub fn variants_iter(&self) -> std::slice::Iter<'_, Variant<Id, T>> {
        self.vnts.iter()
    }

    #[inline]
    pub fn context_iter(&self) -> std::slice::Iter<'_, Context<Id, T>> {
        self.ctxt.iter()
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
        self.context_iter().map(|Context { tyvar, .. }| tyvar)
    }

    #[inline]
    pub fn derived_names(&self) -> impl Iterator<Item = &Id> + '_ {
        self.with.iter()
    }

    pub fn enumer_tags(mut self) -> Self {
        let mut i = 0;
        for Variant { tag, .. } in self.vnts.iter_mut() {
            *tag = Tag(i);
            i += 1;
        }
        self
    }

    pub fn map_id<F, X>(self, mut f: F) -> DataDecl<X, T>
    where
        F: FnMut(Id) -> X,
    {
        DataDecl {
            name: f(self.name),
            poly: self.poly,
            ctxt: self
                .ctxt
                .into_iter()
                .map(|ctxt| ctxt.map_id(|id| f(id)))
                .collect(),
            vnts: self
                .vnts
                .into_iter()
                .map(|v| v.map_id(|id| f(id)))
                .collect(),
            with: self.with.into_iter().map(|id| f(id)).collect(),
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
        let ctxt = ctxt.fmap(|Context { class, tyvar }| Context {
            class,
            tyvar: pair[&Tv::from_ident(tyvar)],
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

impl<T> DataDecl<Ident, T> {
    pub fn map_t<F, U>(self, mut f: F) -> DataDecl<Ident, U>
    where
        F: FnMut(T) -> U,
        T: Copy,
    {
        DataDecl {
            name: self.name,
            poly: self.poly.into_iter().map(|t| f(t)).collect(),
            ctxt: self.ctxt.into_iter().map(|c| c.map_t(|t| f(t))).collect(),
            vnts: self.vnts.into_iter().map(|v| v.map_t(|t| f(t))).collect(),
            with: self.with,
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

    pub fn iter_args(&self) -> std::slice::Iter<'_, Type<Id, T>> {
        self.args.iter()
    }

    pub fn iter_mut_args(&mut self) -> std::slice::IterMut<'_, Type<Id, T>> {
        self.args.iter_mut()
    }

    pub fn find_arg(&self, predicate: impl FnMut(&&Type<Id, T>) -> bool) -> Option<&Type<Id, T>> {
        self.iter_args().find(predicate)
    }

    /// Apply a closure to inner values of type parameter `Id`, mapping a
    /// `Variant<Id, T>` to a `Variant<Id, U>` for some given closure `f :: T ->
    /// U`. This type parameter corresponds to the *identifier representation*,
    /// and ranges over the `name` and `args` field.r
    pub fn map_id<F, X>(self, mut f: F) -> Variant<X, T>
    where
        F: FnMut(Id) -> X,
    {
        Variant {
            name: f(self.name),
            args: self.args.into_iter().map(|ty| ty.map_id(&mut f)).collect(),
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

impl<T> Variant<Ident, T> {
    /// Apply a closure to inner values of type parameter `T`, mapping a
    /// `Variant<Id, T>` to a `Variant<Id, U>` for some given closure `f :: T ->
    /// U`. This type parameter corresponds to the *type variable
    /// representation* of the underlying `Type` arguments in the field `args`.
    pub fn map_t<F, U>(self, mut f: F) -> Variant<Ident, U>
    where
        F: FnMut(T) -> U,
        T: Copy,
    {
        Variant {
            name: self.name,
            args: self.args.into_iter().map(|ty| ty.map_t(&mut f)).collect(),
            tag: self.tag,
            arity: self.arity,
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
}

// make it easy to compare Arity using usizes by implementing PartialEq<usize>
// and PartialOrd<usize>
wy_common::newtype!(Arity | usize | PartialEq);
wy_common::newtype!(Arity | usize | PartialOrd);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AliasDecl<Id = Ident, T = Ident> {
    pub name: Id,
    pub poly: Vec<T>,
    pub sign: Signature<Id, T>,
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
        self.sign.ctxt.iter().all(|ctx| fvs.contains(&ctx.tyvar))
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
            .chain(self.sign.ctxt.iter().map(|ctx| ctx.tyvar))
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

    pub fn map_t_ref<F, U>(&self, mut f: F) -> AliasDecl<Id, U>
    where
        F: FnMut(&T) -> U,
        Id: Copy,
        T: Copy,
    {
        AliasDecl {
            name: self.name,
            poly: self.poly.iter().map(|t| f(&t)).collect(),
            sign: self.sign.map_t_ref(|t| f(t)),
        }
    }
}

impl<T> AliasDecl<Ident, T> {
    pub fn map_t<F, U>(self, mut f: F) -> AliasDecl<Ident, U>
    where
        F: FnMut(T) -> U,
        T: Copy,
    {
        AliasDecl {
            name: self.name,
            poly: self.poly.into_iter().map(|t| f(t)).collect(),
            sign: self.sign.map_t(&mut f),
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

impl<Id, T> NewtypeArg<Id, T> {
    pub fn map_id<F, X>(self, mut f: F) -> NewtypeArg<X, T>
    where
        F: FnMut(Id) -> X,
    {
        match self {
            NewtypeArg::Stacked(ts) => {
                NewtypeArg::Stacked(ts.into_iter().map(|ty| ty.map_id(&mut f)).collect())
            }
            NewtypeArg::Record(k, ss) => NewtypeArg::Record(f(k), ss.map_id(|id| f(id))),
        }
    }
}

impl<T> NewtypeArg<Ident, T> {
    pub fn map_t<F, U>(self, mut f: F) -> NewtypeArg<Ident, U>
    where
        F: FnMut(T) -> U,
        T: Copy,
    {
        match self {
            NewtypeArg::Stacked(ts) => {
                NewtypeArg::Stacked(ts.into_iter().map(|ty| ty.map_t(&mut f)).collect())
            }
            NewtypeArg::Record(k, sig) => NewtypeArg::Record(k, sig.map_t(&mut f)),
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

impl<T> NewtypeDecl<Ident, T> {
    pub fn map_t<F, U>(self, mut f: F) -> NewtypeDecl<Ident, U>
    where
        F: FnMut(T) -> U,
        T: Copy,
    {
        NewtypeDecl {
            name: self.name,
            poly: self.poly.into_iter().map(|t| f(t)).collect(),
            ctor: self.ctor,
            narg: self.narg.map_t(f),
            with: self.with,
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

impl<Id, T> ClassDecl<Id, T> {
    pub fn item_names(&self) -> impl Iterator<Item = &Id> + '_ {
        self.defs.iter().map(|MethodDef { name, .. }| name)
    }
}

impl<T> ClassDecl<Ident, T> {
    pub fn map_t<F, U>(self, mut f: F) -> ClassDecl<Ident, U>
    where
        F: FnMut(T) -> U,
        T: Copy,
    {
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstDecl<Id = Ident, T = Ident> {
    pub name: Id,
    pub tipo: Type<Id, T>,
    pub ctxt: Vec<Context<Id, T>>,
    pub defs: Vec<Binding<Id, T>>,
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

    pub fn map_id<F, X>(self, mut f: F) -> InstDecl<X, T>
    where
        F: FnMut(Id) -> X,
    {
        InstDecl {
            name: f(self.name),
            tipo: self.tipo.map_id(&mut f),
            ctxt: self
                .ctxt
                .into_iter()
                .map(|ctx| ctx.map_id(|id| f(id)))
                .collect(),
            defs: self
                .defs
                .into_iter()
                .map(|bind| bind.map_id(|id| f(id)))
                .collect(),
        }
    }
}

impl<T> InstDecl<Ident, T> {
    pub fn map_t<F, U>(self, mut f: F) -> InstDecl<Ident, U>
    where
        F: FnMut(T) -> U,
        T: Copy,
    {
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnDecl<Id = Ident, T = Ident> {
    pub name: Id,
    pub sign: Option<Signature<Id, T>>,
    pub defs: Vec<Match<Id, T>>,
}

impl<T> FnDecl<Ident, T> {
    pub fn map_t<F, U>(self, mut f: F) -> FnDecl<Ident, U>
    where
        F: FnMut(T) -> U,
        T: Copy,
    {
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MethodDef<Id = Ident, T = Ident> {
    pub name: Id,
    pub sign: Signature<Id, T>,
    pub body: Vec<Match<Id, T>>,
}
impl<Id, T> MethodDef<Id, T> {
    pub fn ctxt_iter(&self) -> std::slice::Iter<'_, Context<Id, T>> {
        self.sign.ctxt_iter()
    }

    pub fn ctxt_iter_mut(&mut self) -> std::slice::IterMut<'_, Context<Id, T>> {
        self.sign.ctxt_iter_mut()
    }

    pub fn map_ctxt<'x, X>(
        &'x self,
        f: impl FnMut(&'x Context<Id, T>) -> X + 'x,
    ) -> impl Iterator<Item = X> + 'x {
        self.ctxt_iter().map(f)
    }

    pub fn map_id<U>(self, mut f: impl FnMut(Id) -> U) -> MethodDef<U, T> {
        MethodDef {
            name: f(self.name),
            sign: Signature {
                each: self.sign.each.into_iter().map(|id| f(id)).collect(),
                ctxt: self
                    .sign
                    .ctxt
                    .into_iter()
                    .map(|Context { class, tyvar }| Context {
                        class: f(class),
                        tyvar,
                    })
                    .collect(),
                tipo: self.sign.tipo.map_id(&mut f),
            },
            body: self.body.into_iter().map(|m| m.map_id(|t| f(t))).collect(),
        }
    }
    pub fn into_method(self) -> Method<Id, T> {
        Method::Sig(self.name, self.sign)
    }
}

impl<T> MethodDef<Ident, T> {
    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> MethodDef<Ident, U>
    where
        T: Copy,
    {
        MethodDef {
            name: self.name,
            sign: Signature {
                each: self.sign.each,
                ctxt: self
                    .sign
                    .ctxt
                    .into_iter()
                    .map(|Context { class, tyvar }| Context {
                        class,
                        tyvar: f(tyvar),
                    })
                    .collect(),
                tipo: self.sign.tipo.map_t(&mut |t| f(t)),
            },
            body: self.body.into_iter().map(|m| m.map_t(&mut f)).collect(),
        }
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Method<Id = Ident, T = Ident> {
    Sig(Id, Signature<Id, T>),
    Impl(Binding<Id, T>),
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
    pub fn map_id<F, X>(self, mut f: F) -> Method<X, T>
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Method::Sig(id, sig) => Method::Sig(f(id), sig.map_id(|id| f(id))),
            Method::Impl(binding) => Method::Impl(binding.map_id(|id| f(id))),
        }
    }
}

impl<T> Method<Ident, T> {
    pub fn map_t<F, U>(self, mut f: F) -> Method<Ident, U>
    where
        F: FnMut(T) -> U,
        T: Copy,
    {
        match self {
            Method::Sig(id, sig) => Method::Sig(id, sig.map_t(&mut f)),
            Method::Impl(binding) => Method::Impl(binding.map_t(&mut f)),
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
}

/// Not all possible combinations of AST nodes are valid, and in fact many may
/// be accepted *syntactically* but not *semantically* by the parser (or later
/// phases of analysis). `SynRule` ties in potential semantic errors
/// *stemming from* syntactic invariants not being upheld.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SynRule {
    /// Generalization of the rules requiring syntactic instance be unique.
    NoDuplicates,
    /// Each function declaration may contain multiple match arms, *however*
    /// these match arms must all appear contiguously within the function's
    /// declaration body. This rule is broken when more than one function
    /// declaration with the *same name* is found.
    NoDuplicateFuncs,
    /// As with `NoDuplicateFuncs`, this rule requires that no duplicate methods
    /// (either definitions or implementations) be found in any declaration that
    /// contains them, i.e., class or impl declarations.
    NoDuplicateMethods,
    /// All methods defined within the body of a class declaration are required
    /// to be annotated with their corresponding type signatures
    ClassMethodAnnotated,
    /// A more general version of the invariant requiring function declarations
    /// to preserve arities across match arms. Generalized since match arms are
    /// found not only in function declarations, but also in `let` expressions
    /// and `where` clauses.
    ///
    /// For example, the following `let`-declaration for `foo` contains two
    /// arms, the first with a single pattern (and hence arity `1`) and the
    /// second with two patterns (and hence arity `2`).
    /// ```wysk
    ///     let foo
    ///     | a = 3 ~~ 1 arg => arity = 1
    ///     | b c = 12 ~~ contradiction! 2 args => arity = 2 but arity = 1!
    ///     in ...
    /// ```
    /// Since the arities aren't equal for the same binding (`foo`), this would
    /// be a compile time error.
    ///
    /// NOTE: the same applies for types! A type constructor has an arity `A` if
    /// it is fully saturated with `A` type arguments, though this is caught in
    /// a rule specific to type application arities
    ///
    BindingAritiesEqual,
    /// A binding must not have more argument patterns than denoted by its type
    /// signature. Since *Wysk* uses *currying semantics*, it is possible for a
    /// function or binding to have a type signature indicating a function with
    /// arity `K` and have `N` arguments for `N < K`, though this *does* require
    /// that the right-hand side (= body definition) resolve to a function of `K
    /// - N` parameters.
    ///
    /// For example, a function `hello :: a -> b -> c -> (a, b, c)` may have a
    /// body accepting *1*, *2*, or *3* parameters:
    /// 1. if only 1 parameter is included in the binding then the right hand
    ///    side must output what resolves to being a function of the *rest* of
    ///    the arguments, such as in the declaration below
    /// ```wysk
    ///         fn hello :: a -> b -> c -> (a, b, c)
    ///         | x = \y z -> (x, y, z)
    /// ```
    ///
    /// If `f` is a function with a signature indicating an arity of *n*, i.e.
    /// ```wysk
    /// f :: a1 -> a2 -> ... -> an -> b
    /// ```
    /// then *the number of patterns* allowed in its bindings __must not
    /// exceed__ *n*. For example, the following function declaration for `foo`
    /// is invalid, as the signature `a -> b -> c` indicates an arity of 2,
    /// while the match arm `| x y z = ...` contains *3* argument patterns.
    ///
    /// ```wysk
    /// fn foo :: a -> b -> c
    /// | x y z = ... ~~ invalid!
    /// ```
    BindingAritiesMatchType,
    /// While *data constructors* may possess distinct arities (compare `Some ::
    /// a -> Option a` with `None :: Option a`), the *arity of a type
    /// application*, defined as the number of types over which a type
    /// constructor is parametrized, must stay the same!
    ///
    /// Consider the type `Result a b`
    /// ```wysk
    /// data Result a b = Ok a | Err b
    /// ```
    /// parameterized over the type variables `a` and `b`. We can see that its
    /// *data* constructors each have arity `1`, but as a *type application*
    /// `Result a b` has arity `2`. Thus the form `Result a` in any type
    /// signature is __invalid__, as it is missing the *second* type parameter.
    TyAppAritiesEqual,
    /// In a type signature with a non-trivial context (i.e., a context is
    /// included), *all* type variables in the context must appear at least once
    /// in the type annotation that follows.
    ///
    /// Note that type variables need not occur in the context! It is only for
    /// type variables in contexts that must occur in the type annotation.
    /// * `|Show a, Show b| a -> ()`
    ///    - Invalid due to `b` occurring in the context but not the annotation
    /// * Valid: `|Show a, Show b| a -> (a, b, c)
    ///   - Valid since all type variables (`a`, `b`) in the context `|Show a,
    ///   Show b|` occur in the type annotation `(a, b, c)`
    NoUnusedCtxTyVars,
    /// The contexts in a given type signature may include the same type
    /// variable ONLY IF the corresponding type classes are NOT repeated. It is
    /// invalid for the *same* context to appear more than once in a list of
    /// contexts.
    /// * `|Show a, Show a|`
    ///     - Invalid due to duplicate instances of `Show a`
    /// * `|Show a, Show a'|`
    ///     - Valid since `a` is lexicographically distinct from `a'`
    NoDuplicatesInCtx,
}
