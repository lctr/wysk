use attr::Pragma;
use wy_common::{
    deque,
    functor::{MapFst, MapSnd, MapThrd},
    struct_field_iters, HashMap,
};
use wy_failure::SrcPath;
use wy_intern::symbol::Symbol;
use wy_name::{Chain, Ident};

pub use wy_lexer::{
    comment::{self, Comment},
    literal::Literal,
};

pub mod ast;
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

use wy_span::{Spanned, Unspan};

pub type SpannedIdent = Spanned<Ident>;
pub type VecIter<'a, X> = std::slice::Iter<'a, X>;
pub type VecIterMut<'a, X> = std::slice::IterMut<'a, X>;

#[derive(Clone, Debug)]
pub struct Program<Id, T, U> {
    pub module: Module<Id, T, U>,
    pub fixities: FixityTable<Id>,
    pub comments: Vec<Comment>,
}

impl<Id, T, U> Program<Id, T, U> {
    pub fn modname(&self) -> &Chain<Id> {
        &self.module.modname
    }

    pub fn module_srcpath(&self) -> &U {
        &self.module.srcpath
    }

    pub fn map_srcpath<V>(self, mut f: impl FnMut(U) -> V) -> Program<Id, T, V> {
        let Program {
            module,
            fixities,
            comments,
        } = self;
        let Module {
            srcpath: uid,
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
            srcpath: f(uid),
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

    pub fn imports_iter(&self) -> VecIter<'_, ImportSpec<Spanned<Id>>> {
        self.module.imports_iter()
    }
    pub fn imports_iter_mut(&mut self) -> VecIterMut<'_, ImportSpec<Spanned<Id>>> {
        self.module.imports_iter_mut()
    }
    pub fn infixes_iter(&self) -> VecIter<'_, FixityDecl<Spanned<Id>>> {
        self.module.infixes_iter()
    }
    pub fn datatys_iter(&self) -> VecIter<'_, DataDecl<Spanned<Id>, Spanned<T>>> {
        self.module.datatys_iter()
    }
    pub fn classes_iter(&self) -> VecIter<'_, ClassDecl<Spanned<Id>, Spanned<T>>> {
        self.module.classes_iter()
    }
    pub fn implems_iter(&self) -> VecIter<'_, InstDecl<Spanned<Id>, Spanned<T>>> {
        self.module.implems_iter()
    }
    pub fn fundefs_iter(&self) -> VecIter<'_, FnDecl<Spanned<Id>, Spanned<T>>> {
        self.module.fundefs_iter()
    }
    pub fn aliases_iter(&self) -> VecIter<'_, AliasDecl<Spanned<Id>, Spanned<T>>> {
        self.module.aliases_iter()
    }
    pub fn newtyps_iter(&self) -> VecIter<'_, NewtypeDecl<Spanned<Id>, Spanned<T>>> {
        self.module.newtyps_iter()
    }
}

impl<Id, T, U, A> MapFst<Id, A> for Program<Id, T, U>
where
    Id: Eq + std::hash::Hash,
    A: Eq + std::hash::Hash,
{
    type WrapFst = Program<A, T, U>;

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

impl<Id, U, T, A> MapSnd<T, A> for Program<Id, T, U> {
    type WrapSnd = Program<Id, A, U>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(T) -> A,
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

impl<Id, U, T, A> MapThrd<U, A> for Program<Id, T, U> {
    type WrapThrd = Program<Id, T, A>;

    fn map_thrd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapThrd
    where
        F: FnMut(U) -> A,
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
pub struct Module<Id = Ident, T = Ident, P = SrcPath> {
    pub srcpath: P,
    pub modname: Chain<Id>,
    pub imports: Vec<ImportSpec<Spanned<Id>>>,
    pub infixes: Vec<FixityDecl<Spanned<Id>>>,
    pub datatys: Vec<DataDecl<Spanned<Id>, Spanned<T>>>,
    pub classes: Vec<ClassDecl<Spanned<Id>, Spanned<T>>>,
    pub implems: Vec<InstDecl<Spanned<Id>, Spanned<T>>>,
    pub fundefs: Vec<FnDecl<Spanned<Id>, Spanned<T>>>,
    pub aliases: Vec<AliasDecl<Spanned<Id>, Spanned<T>>>,
    pub newtyps: Vec<NewtypeDecl<Spanned<Id>, Spanned<T>>>,
    pub pragmas: Vec<Pragma<Spanned<Id>, Spanned<T>>>,
}

struct_field_iters! {
    |Id, T, U| Module<Id, T, U>
    | imports => imports_iter :: ImportSpec<Spanned<Id>>
    | infixes => infixes_iter :: FixityDecl<Spanned<Id>>
    | datatys => datatys_iter :: DataDecl<Spanned<Id>, Spanned<T>>
    | classes => classes_iter :: ClassDecl<Spanned<Id>, Spanned<T>>
    | implems => implems_iter :: InstDecl<Spanned<Id>, Spanned<T>>
    | fundefs => fundefs_iter :: FnDecl<Spanned<Id>, Spanned<T>>
    | aliases => aliases_iter :: AliasDecl<Spanned<Id>, Spanned<T>>
    | newtyps => newtyps_iter :: NewtypeDecl<Spanned<Id>, Spanned<T>>
    | pragmas => pragmas_iter :: Pragma<Spanned<Id>, Spanned<T>>
}

impl<Id, T, U, X> MapFst<Id, X> for Module<Id, T, U> {
    type WrapFst = Module<X, T, U>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let Module {
            srcpath: uid,
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
        let f = &mut wy_common::functor::Func::Fresh(|spanned: Spanned<Id>| spanned.mapf(f));
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
            srcpath: uid,
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

impl<Id, T, U, X> MapThrd<U, X> for Module<Id, T, U> {
    type WrapThrd = Module<Id, T, X>;

    fn map_thrd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapThrd
    where
        F: FnMut(U) -> X,
    {
        let Module {
            srcpath: uid,
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
            srcpath: uid,
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

impl<Id, T, U, X> MapSnd<T, X> for Module<Id, T, U> {
    type WrapSnd = Module<Id, X, U>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(T) -> X,
    {
        let Module {
            srcpath,
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
        let f = &mut wy_common::functor::Func::Fresh(|spanned: Spanned<T>| spanned.mapf(f));
        let datatys = datatys.map_snd(f);
        let classes = classes.map_snd(f);
        let implems = implems.map_snd(f);
        let fundefs = fundefs.map_snd(f);
        let aliases = aliases.map_snd(f);
        let newtyps = newtyps.map_snd(f);
        let pragmas = pragmas.map_snd(f);
        Module {
            srcpath,
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

impl<U, T> Default for Module<Ident, T, U>
where
    U: Default,
{
    fn default() -> Self {
        Self {
            srcpath: U::default(),
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

impl<Id, T, P> Module<Id, T, P> {
    pub fn module_name(&self) -> &Chain<Id> {
        &self.modname
    }
    pub fn map_srcpath<V>(self, uid: V) -> Module<Id, T, V> {
        Module {
            srcpath: uid,
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

    pub fn imports_iter_mut(&mut self) -> VecIterMut<'_, ImportSpec<Spanned<Id>>> {
        self.imports.iter_mut()
    }

    pub fn infixes_iter_mut(&mut self) -> VecIterMut<'_, FixityDecl<Spanned<Id>>> {
        self.infixes.iter_mut()
    }

    pub fn datatys_iter_mut(&mut self) -> VecIterMut<'_, DataDecl<Spanned<Id>, Spanned<T>>> {
        self.datatys.iter_mut()
    }

    pub fn classes_iter_mut(&mut self) -> VecIterMut<'_, ClassDecl<Spanned<Id>, Spanned<T>>> {
        self.classes.iter_mut()
    }

    pub fn implems_iter_mut(&mut self) -> VecIterMut<'_, InstDecl<Spanned<Id>, Spanned<T>>> {
        self.implems.iter_mut()
    }

    pub fn fundefs_iter_mut(&mut self) -> VecIterMut<'_, FnDecl<Spanned<Id>, Spanned<T>>> {
        self.fundefs.iter_mut()
    }

    pub fn aliases_iter_mut(&mut self) -> VecIterMut<'_, AliasDecl<Spanned<Id>, Spanned<T>>> {
        self.aliases.iter_mut()
    }

    pub fn newtyps_iter_mut(&mut self) -> VecIterMut<'_, NewtypeDecl<Spanned<Id>, Spanned<T>>> {
        self.newtyps.iter_mut()
    }

    pub fn pragmas_iter_mut(&mut self) -> VecIterMut<'_, Pragma<Spanned<Id>, Spanned<T>>> {
        self.pragmas.iter_mut()
    }

    pub fn push_decl(&mut self, decl: Declaration<Spanned<Id>, Spanned<T>>) {
        match decl {
            Declaration::Data(data) => self.datatys.push(data),
            Declaration::Alias(alias) => self.aliases.push(alias),
            Declaration::Fixity(fixity) => self.infixes.push(fixity),
            Declaration::Class(class) => self.classes.push(class),
            Declaration::Instance(inst) => self.implems.push(inst),
            Declaration::Function(fun) => self.fundefs.push(fun),
            Declaration::Newtype(newty) => self.newtyps.push(newty),
        }
    }

    pub fn spanless(self) -> SpanlessModule<Id, T, P> {
        let Module {
            srcpath,
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

        let fid = &mut wy_common::functor::Func::Fresh(|spanned: Spanned<Id>| spanned.unspan());
        let ftv = &mut wy_common::functor::Func::Fresh(|spanned: Spanned<T>| spanned.unspan());
        let imports = imports
            .into_iter()
            .map(|impspec| impspec.mapf(fid))
            .collect();
        let infixes = infixes
            .into_iter()
            .map(|impspec| impspec.mapf(fid))
            .collect();
        let datatys = datatys
            .into_iter()
            .map(|decl| decl.map_fst(fid).map_snd(ftv))
            .collect();
        let classes = classes
            .into_iter()
            .map(|decl| decl.map_fst(fid).map_snd(ftv))
            .collect();
        let implems = implems
            .into_iter()
            .map(|decl| decl.map_fst(fid).map_snd(ftv))
            .collect();
        let fundefs = fundefs
            .into_iter()
            .map(|decl| decl.map_fst(fid).map_snd(ftv))
            .collect();
        let aliases = aliases
            .into_iter()
            .map(|decl| decl.map_fst(fid).map_snd(ftv))
            .collect();
        let newtyps = newtyps
            .into_iter()
            .map(|decl| decl.map_fst(fid).map_snd(ftv))
            .collect();
        let pragmas = pragmas
            .into_iter()
            .map(|decl| decl.map_fst(fid).map_snd(ftv))
            .collect();
        SpanlessModule {
            srcpath,
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

/// Same general structure as a `Module`, but without the identifier
/// and type variable parameters being wrapped in a `Spanned` type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpanlessModule<Id, T, P> {
    pub srcpath: P,
    pub modname: Chain<Id>,
    pub imports: Vec<ImportSpec<Id>>,
    pub infixes: Vec<FixityDecl<Id>>,
    pub datatys: Vec<DataDecl<Id, T>>,
    pub classes: Vec<ClassDecl<Id, T>>,
    pub implems: Vec<InstDecl<Id, T>>,
    pub fundefs: Vec<FnDecl<Id, T>>,
    pub aliases: Vec<AliasDecl<Id, T>>,
    pub newtyps: Vec<NewtypeDecl<Id, T>>,
    pub pragmas: Vec<Pragma<Id, T>>,
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
pub struct ImportSpec<Id = SpannedIdent> {
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

impl<Id> PartialEq<ImportSpec<Id>> for ImportSpec<Spanned<Id>>
where
    Id: PartialEq,
{
    fn eq(&self, other: &ImportSpec<Id>) -> bool {
        self.name.len() == other.name.len()
            && self
                .name
                .iter()
                .zip(other.name.iter())
                .all(|(sp, id)| sp.item() == id)
            && self.qualified == other.qualified
            && self.rename.as_ref().map(|sp| sp.item()) == other.rename.as_ref()
            && self.hidden == other.hidden
            // already implemented within imports
            && self.imports == other.imports
    }
}

impl<Id> PartialEq<ImportSpec<Spanned<Id>>> for ImportSpec<Id>
where
    Id: PartialEq,
{
    fn eq(&self, other: &ImportSpec<Spanned<Id>>) -> bool {
        self.name.len() == other.name.len()
            && self
                .name
                .iter()
                .zip(other.name.iter())
                .all(|(id, sp)| sp.item() == id)
            && self.qualified == other.qualified
            && self.rename.as_ref() == other.rename.as_ref().map(|sp| sp.item())
            && self.hidden == other.hidden
            && self.imports == other.imports
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
pub enum Import<Id = SpannedIdent> {
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

impl<Id> PartialEq<Import<Id>> for Import<Spanned<Id>>
where
    Id: PartialEq,
{
    fn eq(&self, other: &Import<Id>) -> bool {
        match (self, other) {
            (Self::Operator(l0), Import::Operator(r0))
            | (Self::Function(l0), Import::Function(r0))
            | (Self::Abstract(l0), Import::Abstract(r0))
            | (Self::Total(l0), Import::Total(r0)) => l0.item() == r0,
            (Self::Partial(l0, l1), Import::Partial(r0, r1)) => {
                l0.item() == r0
                    && l1.len() == r1.len()
                    && l1.into_iter().zip(r1).all(|(sp, id)| sp.item() == id)
            }
            _ => false,
        }
    }
}

impl<Id> PartialEq<Import<Spanned<Id>>> for Import<Id>
where
    Id: PartialEq,
{
    fn eq(&self, other: &Import<Spanned<Id>>) -> bool {
        match (self, other) {
            (Self::Operator(l0), Import::Operator(r0))
            | (Self::Function(l0), Import::Function(r0))
            | (Self::Abstract(l0), Import::Abstract(r0))
            | (Self::Total(l0), Import::Total(r0)) => l0 == r0.item(),
            (Self::Partial(l0, l1), Import::Partial(r0, r1)) => {
                l0 == r0.item()
                    && l1.len() == r1.len()
                    && l1.into_iter().zip(r1).all(|(id, sp)| id == sp.item())
            }
            _ => false,
        }
    }
}
