use wy_common::{deque, Map};
use wy_intern::symbol::{self, Symbol};

pub use wy_lexer::{
    comment::{self, Comment},
    Literal,
};

pub mod expr;
pub mod fixity;
pub mod ident;
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
pub struct Program<Id = Ident> {
    pub module: Module<Id>,
    pub fixities: FixityTable,
    pub comments: Vec<Comment>,
}

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
    pub fn get_imports(&self) -> &[Import<Id>] {
        self.imports.as_slice()
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

impl<Id> FixityDecl<Id> {
    pub fn new(assoc: Assoc, prec: Prec, infixes: Vec<Id>) -> Self {
        Self {
            infixes,
            fixity: Fixity { assoc, prec },
        }
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
    pub fn enumer_tags(mut self) -> Self {
        let mut i = 0;
        for Variant { tag, .. } in self.vnts.iter_mut() {
            *tag = Tag(i);
            i += 1;
        }
        self
    }

    pub fn map_t<F, U>(self, mut f: F) -> DataDecl<Id, U>
    where
        F: FnMut(T) -> U,
    {
        let DataDecl {
            name,
            poly,
            ctxt,
            vnts,
            with,
        } = self;
        let poly = poly.into_iter().map(|t| f(t)).collect();
        let ctxt = ctxt.into_iter().map(|c| c.map_t(|t| f(t))).collect();
        let vnts = vnts.into_iter().map(|v| v.map_t(|t| f(t))).collect();
        DataDecl {
            name,
            poly,
            ctxt,
            vnts,
            with,
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
    pub fn map_t<F, U>(self, mut f: F) -> Variant<Id, U>
    where
        F: FnMut(T) -> U,
    {
        let Variant {
            name,
            args,
            tag,
            arity,
        } = self;
        let args = args.into_iter().map(|ty| ty.map_t(&mut f)).collect();
        Variant {
            name,
            args,
            tag,
            arity,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Tag(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Arity(pub usize);

impl Arity {
    pub fn from_len<T>(ts: &[T]) -> Self {
        Self(ts.len())
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AliasDecl<Id = Ident, T = Ident> {
    pub name: Id,
    pub poly: Vec<T>,
    pub sign: Signature<Id, T>,
}

impl<Id, T> AliasDecl<Id, T> {
    pub fn map_t<F, U>(self, mut f: F) -> AliasDecl<Id, U>
    where
        F: FnMut(T) -> U,
    {
        let AliasDecl { name, poly, sign } = self;
        let poly = poly.into_iter().map(|t| f(t)).collect();
        let sign = sign.map_t(|t| f(t));
        AliasDecl { name, poly, sign }
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
    Product(Vec<Type<Id, T>>),
    Record(Id, Signature<Id, T>),
}

impl<Id, T> NewtypeArg<Id, T> {
    pub fn map_t<F, U>(self, mut f: F) -> NewtypeArg<Id, U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            NewtypeArg::Product(ts) => {
                NewtypeArg::Product(ts.into_iter().map(|ty| ty.map_t(&mut f)).collect())
            }
            NewtypeArg::Record(k, sig) => NewtypeArg::Record(k, sig.map_t(f)),
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

impl<Id, T> NewtypeDecl<Id, T> {
    pub fn map_t<F, U>(self, mut f: F) -> NewtypeDecl<Id, U>
    where
        F: FnMut(T) -> U,
    {
        let NewtypeDecl {
            name,
            poly,
            ctor,
            narg,
            with,
        } = self;
        let poly = poly.into_iter().map(|t| f(t)).collect();
        let narg = narg.map_t(f);
        NewtypeDecl {
            name,
            poly,
            ctor,
            narg,
            with,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassDecl<Id = Ident, T = Ident> {
    pub name: Id,
    pub poly: Vec<T>,
    pub ctxt: Vec<Context<Id, T>>,
    pub defs: Vec<Method<Id, T>>,
}

impl<Id, T> ClassDecl<Id, T> {
    pub fn map_t<F, U>(self, mut f: F) -> ClassDecl<Id, U>
    where
        F: FnMut(T) -> U,
    {
        let ClassDecl {
            name,
            poly,
            ctxt,
            defs,
        } = self;
        let poly = poly.into_iter().map(|t| f(t)).collect();
        let ctxt = ctxt.into_iter().map(|ctx| ctx.map_t(|t| f(t))).collect();
        let defs = defs.into_iter().map(|m| m.map_t(|t| f(t))).collect();
        ClassDecl {
            name,
            poly,
            ctxt,
            defs,
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
    pub fn map_t<F, U>(self, mut f: F) -> InstDecl<Id, U>
    where
        F: FnMut(T) -> U,
    {
        let InstDecl {
            name,
            tipo,
            ctxt,
            defs,
        } = self;
        let tipo = tipo.map_t(&mut f);
        let ctxt = ctxt.into_iter().map(|ctx| ctx.map_t(|t| f(t))).collect();
        let defs = defs.into_iter().map(|b| b.map_t(|t| f(t))).collect();
        InstDecl {
            name,
            tipo,
            ctxt,
            defs,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnDecl<Id = Ident, T = Ident> {
    pub name: Id,
    pub sign: Option<Signature<Id, T>>,
    pub defs: Vec<Match<Id, T>>,
}

impl<Id, T> FnDecl<Id, T> {
    pub fn map_t<F, U>(self, mut f: F) -> FnDecl<Id, U>
    where
        F: FnMut(T) -> U,
    {
        let FnDecl { name, sign, defs } = self;
        let sign = sign.map(|sig| sig.map_t(|t| f(t)));
        let defs = defs.into_iter().map(|m| m.map_t(|t| f(t))).collect();
        FnDecl { name, sign, defs }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Method<Id = Ident, T = Ident> {
    Sig(Id, Signature<Id, T>),
    Impl(Binding<Id, T>),
}

impl<Id, T> Method<Id, T> {
    pub fn name(&self) -> Id
    where
        Id: Copy,
    {
        match self {
            Method::Sig(id, _) | Method::Impl(Binding { name: id, .. }) => *id,
        }
    }
    pub fn map_t<F, U>(self, f: F) -> Method<Id, U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Method::Sig(id, sig) => Method::Sig(id, sig.map_t(f)),
            Method::Impl(binding) => Method::Impl(binding.map_t(f)),
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
