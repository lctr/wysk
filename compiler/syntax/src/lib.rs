use attr::Attribute;
use wy_common::{
    deque,
    functor::{MapFst, MapSnd, MapThrd},
    struct_field_iters, HashMap,
};
use wy_intern::symbol::{self, Symbol};
use wy_name::{module::ModuleId, Chain, Ident};

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
pub mod types;
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
    pub fn map_idents<X>(self, f: impl FnMut(I) -> X) -> SyntaxTree<X>
    where
        I: Eq + std::hash::Hash,
        X: Eq + std::hash::Hash,
    {
        use wy_common::functor::Func;
        let mut ph = Func::Fresh(f);
        let SyntaxTree { programs, packages } = self;
        let programs = programs
            .into_iter()
            .map(|program| program.map_fst(&mut ph))
            .collect();
        let packages = packages
            .into_iter()
            .map(|(mid, chain)| (mid, chain.mapf(&mut ph)))
            .collect();
        SyntaxTree { programs, packages }
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

    pub fn add_program<M>(&mut self, program: Program<I, M, Tv>) -> ModuleId
    where
        I: Copy,
    {
        let uid = ModuleId::new(self.programs.len() as u32);
        let chain = program.module.modname.clone();
        let program = program.map_u(|_| uid);
        self.programs.push(program);
        self.packages.insert(uid, chain);
        uid
    }

    pub fn add_programs<M>(
        &mut self,
        programs: impl IntoIterator<Item = Program<I, M, Tv>>,
    ) -> Vec<ModuleId>
    where
        I: Copy,
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
}

impl Ast {}

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
}

impl<Id, U, T, A> MapFst<Id, A> for Program<Id, U, T>
where
    Id: Eq + std::hash::Hash,
    A: Eq + std::hash::Hash,
{
    type WrapFst = Program<A, U, T>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> A,
    {
        let Program {
            module,
            fixities,
            comments,
        } = self;
        let module = module.map_fst(f);
        let fixities = fixities.into_iter().map(|pair| pair.map_fst(f)).collect();
        Program {
            module,
            fixities,
            comments,
        }
    }
}

impl<Id, U, T, A> MapSnd<U, A> for Program<Id, U, T> {
    type WrapSnd = Program<Id, A, T>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(U) -> A,
    {
        let Program {
            module,
            fixities,
            comments,
        } = self;
        let module = module.map_snd(f);
        Program {
            module,
            fixities,
            comments,
        }
    }
}

impl<Id, U, T, A> MapThrd<T, A> for Program<Id, U, T> {
    type WrapThrd = Program<Id, U, A>;

    fn map_thrd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapThrd
    where
        F: FnMut(T) -> A,
    {
        let Program {
            module,
            fixities,
            comments,
        } = self;
        let module = module.map_thrd(f);
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

impl<Id, U, T, X> MapFst<Id, X> for Module<Id, U, T> {
    type WrapFst = Module<X, U, T>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
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
        } = self;
        let modname = modname.mapf(f);
        let imports = imports.into_iter().map(|i| i.mapf(f)).collect();
        let infixes = infixes.into_iter().map(|d| d.mapf(f)).collect();
        let datatys = datatys.map_fst(f);
        let classes = classes.map_fst(f);
        let implems = implems.map_fst(f);
        let fundefs = fundefs.map_fst(f);
        let aliases = aliases.map_fst(f);
        let newtyps = newtyps.map_fst(f);
        let pragmas = pragmas.map_fst(f);
        Module {
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
        }
    }
}

impl<Id, U, T, X> MapSnd<U, X> for Module<Id, U, T> {
    type WrapSnd = Module<Id, X, T>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(U) -> X,
    {
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
        } = self;
        let uid = f.apply(uid);
        Module {
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
        }
    }
}

impl<Id, U, T, X> MapThrd<T, X> for Module<Id, U, T> {
    type WrapThrd = Module<Id, U, X>;

    fn map_thrd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapThrd
    where
        F: FnMut(T) -> X,
    {
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
        } = self;
        let datatys = datatys.map_snd(f);
        let classes = classes.map_snd(f);
        let implems = implems.map_snd(f);
        let fundefs = fundefs.map_snd(f);
        let aliases = aliases.map_snd(f);
        let newtyps = newtyps.map_snd(f);
        let pragmas = pragmas.map_snd(f);
        Module {
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
        }
    }
}

impl<U, T> Default for Module<Ident, U, T>
where
    U: Default,
{
    fn default() -> Self {
        Self {
            uid: U::default(),
            modname: Chain::new(Ident::Upper(wy_intern::sym::MAIN_MOD), deque![]),
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
    pub fn mapf<F, X>(self, f: &mut wy_common::functor::Func<'_, F>) -> ImportSpec<X>
    where
        F: FnMut(Id) -> X,
    {
        let ImportSpec {
            name,
            qualified,
            rename,
            hidden,
            imports,
        } = self;
        let name = name.mapf(f);
        let rename = rename.map(|id| f.apply(id));
        let imports = imports.into_iter().map(|i| i.mapf(f)).collect();
        ImportSpec {
            name,
            qualified,
            rename,
            hidden,
            imports,
        }
    }
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

    pub fn mapf<F, X>(self, f: &mut wy_common::functor::Func<'_, F>) -> Import<X>
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Import::Operator(id) => Import::Operator(f.apply(id)),
            Import::Function(id) => Import::Function(f.apply(id)),
            Import::Abstract(id) => Import::Abstract(f.apply(id)),
            Import::Total(id) => Import::Total(f.apply(id)),
            Import::Partial(root, rest) => Import::Partial(
                f.apply(root),
                rest.into_iter().map(|id| f.apply(id)).collect(),
            ),
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
