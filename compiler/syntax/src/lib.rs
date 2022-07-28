#![feature(generic_associated_types)]

use attr::Attribute;
use wy_common::{deque, struct_field_iters, HashMap, Mappable};
use wy_intern::symbol::{self, Symbol};
use wy_name::{
    ident::{Chain, Ident},
    module::ModuleId,
};

pub use wy_lexer::{
    comment::{self, Comment},
    literal::Literal,
};

pub mod attr;
pub mod decl;
pub mod expr;
pub mod fixity;
pub mod pattern;
pub mod record;
pub mod stmt;
pub mod tipo;
pub mod visit;

use decl::*;
use expr::*;
use fixity::*;
use pattern::*;
use record::*;
use stmt::*;
use tipo::*;

#[derive(Clone, Debug)]
pub struct SyntaxTree<I> {
    programs: Vec<Program<I, ModuleId, Tv>>,
    packages: HashMap<ModuleId, Chain<I>>,
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
            packages: HashMap::new(),
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
        let packages = HashMap::from([(ModuleId::new(0), program.module.modname.clone())]);
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

    pub fn imported_modules_iter(&self) -> impl Iterator<Item = (&ModuleId, &Chain<I>)>
    where
        I: Copy,
    {
        self.programs_iter().flat_map(|prog| {
            prog.get_imports_iter()
                .map(|impf| (prog.module_id(), impf.module_name()))
        })
    }

    pub fn map_id<X>(self, f: &mut impl FnMut(I) -> X) -> SyntaxTree<X>
    where
        I: std::hash::Hash + Eq,
        X: std::hash::Hash + Eq,
    {
        SyntaxTree {
            programs: self.programs.fmap(|prog| prog.map_id(f)),
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

impl Ast {
    pub fn qualify_chain_idents(self) -> SyntaxTree<Chain<Ident>> {
        let SyntaxTree { programs, packages } = self;
        let programs = programs
            .into_iter()
            .map(|program| program.qualify_chain_idents())
            .collect();
        let packages = packages
            .into_iter()
            .map(|(mid, chs)| (mid, Chain::new(chs, deque![])))
            .collect();
        SyntaxTree { programs, packages }
    }
    pub fn qualify_unique_idents(self) -> SyntaxTree<wy_name::Unique> {
        let SyntaxTree { programs, packages } = self;
        let programs = programs
            .into_iter()
            .map(|program| program.qualify_unique_idents())
            .collect();
        let packages = packages
            .into_iter()
            .map(|(mid, chs)| (mid, Chain::new(wy_name::intern_chain(chs), deque![])))
            .collect();
        SyntaxTree { programs, packages }
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
    pub fn map_id<X>(self, f: &mut impl FnMut(Id) -> X) -> Program<X, U, T>
    where
        X: Eq + std::hash::Hash,
        Id: Eq + std::hash::Hash,
    {
        Program {
            module: self.module.map_id(f),
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

impl Program<Ident, ModuleId, Tv> {
    pub fn qualify_chain_idents(self) -> Program<Chain<Ident>, ModuleId, Tv> {
        let Program {
            module,
            fixities,
            comments,
        } = self;
        let name = module.module_name().clone();
        let module = qualify_module_chain_idents(module);
        let fixities = fixities
            .into_iter()
            .map(|(id, fix)| (name.with_suffix(id), fix))
            .collect();
        Program {
            module,
            fixities,
            comments,
        }
    }

    pub fn qualify_unique_idents(self) -> Program<wy_name::Unique, ModuleId, Tv> {
        let Program {
            module,
            fixities,
            comments,
        } = self;
        let name = module.modname.clone();
        let module = qualify_unique_module_idents(module);
        let fixities = fixities
            .into_iter()
            .map(|(id, fix)| (wy_name::intern_chain(name.with_suffix(id)), fix))
            .collect();
        Program {
            module,
            fixities,
            comments,
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
    pub fn module_name(&self) -> &Chain<Id> {
        &self.modname
    }
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

    pub fn map_id<X>(self, f: &mut impl FnMut(Id) -> X) -> Module<X, U, T> {
        Module {
            uid: self.uid,
            modname: self.modname.map(|id| f(id)),
            imports: self.imports.fmap(|imp| imp.map(|id| f(id))),
            infixes: self.infixes.fmap(|decl| decl.map(|id| f(id))),
            datatys: self.datatys.fmap(|decl| decl.map_id(|id| f(id))),
            classes: self.classes.fmap(|decl| decl.map_id(f)),
            implems: self.implems.fmap(|decl| decl.map_id(f)),
            fundefs: self.fundefs.fmap(|decl| decl.map_id(f)),
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

pub fn qualify_module_chain_idents(
    mdl: Module<Ident, ModuleId, Tv>,
) -> Module<Chain<Ident>, ModuleId, Tv> {
    let root_name = mdl.module_name();
    mdl.map_id_ref(&mut |id| root_name.with_suffix(*id))
}

/// Replaces every identifier in a module with a chain consisting of the module
/// name prefixed to the identifier.
pub fn qualify_unique_module_idents(
    mdl: Module<Ident, ModuleId, Tv>,
) -> Module<wy_name::Unique, ModuleId, Tv> {
    let root_name = mdl.modname.clone();
    mdl.map_id_ref(&mut |id| wy_name::intern_chain(root_name.with_suffix(*id)))
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

    pub fn module_name(&self) -> &Chain<Id> {
        &self.name
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
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

    pub fn idents<'i>(&'i self) -> impl Iterator<Item = &'i Id> + '_ {
        match self {
            Import::Operator(id)
            | Import::Function(id)
            | Import::Abstract(id)
            | Import::Total(id) => std::iter::once(id).chain(&[]),
            Import::Partial(head, ids) => std::iter::once(head).chain(ids),
        }
    }
}
