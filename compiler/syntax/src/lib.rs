use attr::Attribute;
use wy_common::{deque, struct_field_iters, Map, Mappable};
use wy_intern::symbol::{self, Symbol};
use wy_name::{ident::*, module::ModuleId};

pub use wy_lexer::{
    comment::{self, Comment},
    literal::Literal,
};

pub mod attr;
pub mod decl;
pub mod expr;
pub mod fixity;
pub mod pattern;
pub mod pretty;
pub mod stmt;
pub mod tipo;
pub mod visit;

use decl::*;
use expr::*;
use fixity::*;
use pattern::*;
use stmt::*;
use tipo::*;

#[derive(Clone, Debug)]
pub struct SyntaxTree<I> {
    programs: Vec<Program<I, ModuleId, Tv>>,
    packages: Map<ModuleId, Chain<I>>,
}

pub type Ast = SyntaxTree<Ident>;

wy_common::struct_field_iters!(
    |I| SyntaxTree<I>
    | programs => programs_iter :: Program<I, ModuleId, Tv>
);

impl<I> SyntaxTree<I> {
    pub fn new() -> Self {
        Self {
            programs: Vec::new(),
            packages: Map::new(),
        }
    }
    pub fn program_count(&self) -> usize {
        self.programs.len()
    }

    pub fn packages_iter(&self) -> std::collections::hash_map::Iter<'_, ModuleId, Chain<I>> {
        self.packages.iter()
    }

    pub fn get_uid_chain(&self, uid: &ModuleId) -> Option<&Chain<I>> {
        self.packages.get(uid)
    }

    pub fn with_program<M, T>(program: Program<I, M, T>) -> Self
    where
        I: Copy,
        Tv: From<T>,
    {
        let program = program.map_t(|t| Tv::from(t)).map_u(|_| ModuleId::new(0));
        let packages = Map::from([(ModuleId::new(0), program.module.modname.clone())]);
        Self {
            programs: vec![program],
            packages,
        }
    }
    pub fn add_program<M, T>(&mut self, program: Program<I, M, T>) -> ModuleId
    where
        I: Copy,
        Tv: From<T>,
    {
        let uid = ModuleId::new(self.programs.len() as u32);
        let chain = program.module.modname.clone();
        let program = program.map_t(|t| Tv::from(t)).map_u(|_| uid);
        self.programs.push(program);
        self.packages.insert(uid, chain);
        uid
    }

    pub fn add_programs<M, T>(
        &mut self,
        programs: impl IntoIterator<Item = Program<I, M, T>>,
    ) -> Vec<ModuleId>
    where
        I: Copy,
        Tv: From<T>,
    {
        programs
            .into_iter()
            .map(|program| self.add_program(program))
            .collect()
    }

    pub fn imported_modules(&self) -> Vec<(ModuleId, Chain<I>)>
    where
        I: Copy,
    {
        self.programs_iter()
            .enumerate()
            .flat_map(|(u, prog)| {
                prog.get_imports_iter()
                    .map(move |import| (ModuleId::new(u as u32), import.name.clone()))
            })
            .collect()
    }

    pub fn map_id<X>(self, mut f: impl FnMut(I) -> X) -> SyntaxTree<X>
    where
        I: std::hash::Hash + Eq,
        X: std::hash::Hash + Eq,
    {
        SyntaxTree {
            programs: self.programs.fmap(|prog| prog.map_id(|id| f(id))),
            packages: self
                .packages
                .into_iter()
                .map(|(mid, chain)| (mid, chain.map(|id| f(id))))
                .collect(),
        }
    }

    pub fn map_id_ref<X>(&self, mut f: impl FnMut(&I) -> X) -> SyntaxTree<X>
    where
        I: std::hash::Hash + Eq + Copy,
        X: std::hash::Hash + Eq,
    {
        SyntaxTree {
            programs: self
                .programs_iter()
                .map(|prog| prog.map_id_ref(&mut |id| f(id)))
                .collect(),
            packages: self
                .packages_iter()
                .map(|(mid, chain)| (*mid, chain.map_ref(|id| f(id))))
                .collect(),
        }
    }
}

pub fn enumerate_programs<Id, U: Copy, T, I: IntoIterator<Item = Program<Id, U, T>>>(
    progs: I,
) -> impl Iterator<Item = Program<Id, ModuleId, T>> {
    progs
        .into_iter()
        .enumerate()
        .map(|(n, prog)| prog.map_u(|_| ModuleId::new(n as u32)))
}

pub fn enumerate_modules(
    modules: impl IntoIterator<Item = Module>,
) -> impl Iterator<Item = (ModuleId, Module)> {
    modules
        .into_iter()
        .enumerate()
        .map(|(id, mdl)| (ModuleId::new(id as u32), mdl))
}

#[derive(Clone, Debug)]
pub struct Program<Id, U, T> {
    pub module: Module<Id, U, T>,
    pub fixities: FixityTable<Id>,
    pub comments: Vec<Comment>,
}

pub type RawProgram = Program<Ident, Option<std::path::PathBuf>, Ident>;
pub type FreshProgram<U = ()> = Program<Ident, U, Tv>;

macro_rules! impl_program {
    (
        $(
            $(|)? $field:ident : $typ:ident<$g0:tt $(,$gs:tt)?>, $method_name_iter:ident
            & $method_name_slice:ident
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
    | fundefs: FnDecl<Id, T>, get_fundefs_iter & get_fundefs
    | datatys: DataDecl<Id, T>, get_datatys_iter & get_datatys
    | classes: ClassDecl<Id, T>, get_classes_iter & get_classes
    | implems: InstDecl<Id, T>, get_implems_iter & get_implems
    | aliases: AliasDecl<Id, T>, get_aliases_iter & get_aliases
    | newtyps: NewtypeDecl<Id, T>, get_newtyps_iter & get_newtyps
}

impl<Id, U, T> Program<Id, U, T> {
    pub fn modname(&self) -> &Chain<Id> {
        &self.module.modname
    }

    pub fn module_id(&self) -> &U {
        &self.module.uid
    }

    pub fn map_u<V>(self, mut f: impl FnMut(U) -> V) -> Program<Id, V, T> {
        let Program {
            module,
            fixities,
            comments,
        } = self;
        let Module {
            uid,
            modname,
            imports,
            infixes,
            datatys,
            classes,
            implems,
            fundefs,
            aliases,
            newtyps,
            pragmas,
        } = module;
        let module = Module {
            uid: f(uid),
            modname,
            imports,
            infixes,
            datatys,
            classes,
            implems,
            fundefs,
            aliases,
            newtyps,
            pragmas,
        };
        Program {
            module,
            fixities,
            comments,
        }
    }
    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> Program<X, U, T>
    where
        X: Eq + std::hash::Hash,
        Id: Eq + std::hash::Hash,
    {
        Program {
            module: self.module.map_id(|id| f(id)),
            fixities: self.fixities.map(f),
            comments: self.comments,
        }
    }
    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> Program<X, U, T>
    where
        U: Copy,
        T: Copy,
        X: Eq + std::hash::Hash,
        Id: Copy + Eq + std::hash::Hash,
    {
        Program {
            module: self.module.map_id_ref(f),
            fixities: FixityTable(
                self.fixities
                    .iter()
                    .map(|(id, fixity)| (f(id), *fixity))
                    .collect(),
            ),
            comments: self.comments.clone(),
        }
    }
    pub fn map_t<X>(self, mut f: impl FnMut(T) -> X) -> Program<Id, U, X> {
        Program {
            module: self.module.map_t(|t| f(t)),
            fixities: self.fixities,
            comments: self.comments,
        }
    }
    pub fn map_t_ref<X>(&self, f: &mut impl FnMut(&T) -> X) -> Program<Id, U, X>
    where
        Id: Copy,
        U: Copy,
    {
        Program {
            module: self.module.map_t_ref(f),
            fixities: self.fixities.clone(),
            comments: self.comments.clone(),
        }
    }
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
    pub pragmas: Vec<Attribute<Id, T>>,
}

pub type RawModule = Module<Ident, Option<std::path::PathBuf>, Ident>;
pub type FreshModule = Module<Ident, ModuleId, Tv>;

struct_field_iters! {
    |Id, U, T| Module<Id, U, T>
    | imports => imports_iter :: ImportSpec<Id>
    | infixes => infixes_iter :: FixityDecl<Id>
    | datatys => datatys_iter :: DataDecl<Id, T>
    | classes => classes_iter :: ClassDecl<Id, T>
    | implems => implems_iter :: InstDecl<Id, T>
    | fundefs => fundefs_iter :: FnDecl<Id, T>
    | aliases => aliases_iter :: AliasDecl<Id, T>
    | newtyps => newtyps_iter :: NewtypeDecl<Id, T>
    | pragmas => pragmas_iter :: Attribute<Id, T>
}

impl Default for RawModule {
    fn default() -> Self {
        Self {
            uid: None,
            modname: Chain::new(Ident::Upper(*symbol::reserved::MAIN_MOD), deque![]),
            imports: vec![],
            infixes: vec![],
            datatys: vec![],
            classes: vec![],
            implems: vec![],
            fundefs: vec![],
            aliases: vec![],
            newtyps: vec![],
            pragmas: vec![],
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
            pragmas: self.pragmas,
        }
    }

    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> Module<X, U, T> {
        Module {
            uid: self.uid,
            modname: self.modname.map(|id| f(id)),
            imports: self.imports.fmap(|imp| imp.map(|id| f(id))),
            infixes: self.infixes.fmap(|decl| decl.map(|id| f(id))),
            datatys: self.datatys.fmap(|decl| decl.map_id(|id| f(id))),
            classes: self.classes.fmap(|decl| decl.map_id(|id| f(id))),
            implems: self.implems.fmap(|decl| decl.map_id(|id| f(id))),
            fundefs: self.fundefs.fmap(|decl| decl.map_id(|id| f(id))),
            aliases: self.aliases.fmap(|decl| decl.map_id(|id| f(id))),
            newtyps: self.newtyps.fmap(|decl| decl.map_id(|id| f(id))),
            pragmas: self.pragmas.fmap(|decl| decl.map_id(|id| f(id))),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> Module<X, U, T>
    where
        U: Copy,
        T: Copy,
    {
        Module {
            uid: self.uid,
            modname: self.modname.map_ref(|id| f(id)),
            imports: self
                .imports_iter()
                .map(|imp| imp.map_ref(&mut |id| f(id)))
                .collect(),
            infixes: self
                .infixes_iter()
                .map(|fixities| fixities.map_ref(f))
                .collect(),
            datatys: self
                .datatys_iter()
                .map(|datatys| datatys.map_id_ref(f))
                .collect(),
            classes: self
                .classes_iter()
                .map(|classes| classes.map_id_ref(f))
                .collect(),
            implems: self
                .implems_iter()
                .map(|implems| implems.map_id_ref(f))
                .collect(),
            fundefs: self
                .fundefs_iter()
                .map(|fundefs| fundefs.map_id_ref(f))
                .collect(),
            aliases: self
                .aliases_iter()
                .map(|aliases| aliases.map_id_ref(f))
                .collect(),
            newtyps: self
                .newtyps_iter()
                .map(|newtyps| newtyps.map_id_ref(f))
                .collect(),
            pragmas: self
                .pragmas_iter()
                .map(|pragmas| pragmas.map_id_ref(f))
                .collect(),
        }
    }

    pub fn map_t<X>(self, mut f: impl FnMut(T) -> X) -> Module<Id, U, X> {
        Module {
            uid: self.uid,
            modname: self.modname,
            imports: self.imports,
            infixes: self.infixes,
            datatys: self.datatys.fmap(|decl| decl.map_t(|t| f(t))),
            classes: self.classes.fmap(|decl| decl.map_t(|t| f(t))),
            implems: self.implems.fmap(|decl| decl.map_t(|t| f(t))),
            fundefs: self.fundefs.fmap(|decl| decl.map_t(|t| f(t))),
            aliases: self.aliases.fmap(|decl| decl.map_t(|t| f(t))),
            newtyps: self.newtyps.fmap(|decl| decl.map_t(|t| f(t))),
            pragmas: self.pragmas.fmap(|decl| decl.map_t(|t| f(t))),
        }
    }

    pub fn map_t_ref<X>(&self, f: &mut impl FnMut(&T) -> X) -> Module<Id, U, X>
    where
        Id: Copy,
        U: Copy,
    {
        Module {
            uid: self.uid,
            modname: self.modname.clone(),
            imports: self.imports.clone(),
            infixes: self.infixes.clone(),
            datatys: self
                .datatys_iter()
                .map(|datatys| datatys.map_t_ref(f))
                .collect(),
            classes: self
                .classes_iter()
                .map(|classes| classes.map_t_ref(f))
                .collect(),
            implems: self
                .implems_iter()
                .map(|implems| implems.map_t_ref(f))
                .collect(),
            fundefs: self
                .fundefs_iter()
                .map(|fundefs| fundefs.map_t_ref(f))
                .collect(),
            aliases: self
                .aliases_iter()
                .map(|aliases| aliases.map_t_ref(f))
                .collect(),
            newtyps: self
                .newtyps_iter()
                .map(|newtyps| newtyps.map_t_ref(f))
                .collect(),
            pragmas: self
                .pragmas_iter()
                .map(|pragma| pragma.map_t_ref(f))
                .collect(),
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

struct_field_iters! {
    |Id| ImportSpec<Id>
    | imports => imports :: Import<Id>
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

    pub fn map_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> ImportSpec<U> {
        ImportSpec {
            name: self.name.map_ref(|id| f(id)),
            qualified: self.qualified,
            rename: self.rename.as_ref().map(|id| f(id)),
            hidden: self.hidden,
            imports: self.imports_iter().map(|imp| imp.map_ref(f)).collect(),
        }
    }

    pub fn get_imports(&self) -> &[Import<Id>] {
        self.imports.as_slice()
    }

    pub fn imports_iter(&self) -> std::slice::Iter<'_, Import<Id>> {
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

wy_common::variant_preds! {
    Import
    | is_operator => Operator (_)
    | is_function => Function (_)
    | is_abstract => Abstract (_)
    | is_total => Total (_)
    | is_partial => Partial (..)
}

impl<Id> Import<Id> {
    pub fn map<T>(self, mut f: impl FnMut(Id) -> T) -> Import<T> {
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
    pub fn map_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> Import<U> {
        match self {
            Import::Operator(id) => Import::Operator(f(id)),
            Import::Function(id) => Import::Function(f(id)),
            Import::Abstract(id) => Import::Abstract(f(id)),
            Import::Total(id) => Import::Total(f(id)),
            Import::Partial(root, rest) => Import::Partial(f(root), rest.iter().map(f).collect()),
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
    /// Prohibits infinitely sized types introduced by
    /// self-referential/recursive type aliases. This is because type aliases
    /// are replaced with their definition at compile time, and with the same
    /// type on both sides of the equation, applkying substitution would fail to
    /// arrive at a solution due to an unbounded strictly monotonic increase in
    /// terms.
    ///
    /// For example, consider the alias `type Foo = Foo Bar`. Since type aliases
    /// are erased at compile time, we first derive the substitution `{ a := Foo
    /// }` and replace `Foo` with `a` on both sides to get `a = a Bar`, which is
    /// impossible since that would imply `a = a (a (a ... (a ...)))`, with
    /// `Bar` infinitely unattainable ad infinitum. The same does not hold
    /// however for `data` definitions, which provide a level of indirection
    /// necessary to deal with isorecursive types.
    NoRecursiveAliases,
}
