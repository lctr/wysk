use module::{ImportSpec, Module};
use serde::{Deserialize, Serialize};

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
pub mod module;
pub mod node;
pub mod pattern;
pub mod record;
pub mod stmt;
pub mod tipo;
pub mod visit;

use decl::*;
use expr::*;
use fixity::*;
use pattern::*;
use stmt::*;

#[allow(unused)]
use node::*;

use wy_span::Spanned;

pub type SpannedIdent = Spanned<Ident>;
pub type VecIter<'a, X> = std::slice::Iter<'a, X>;
pub type VecIterMut<'a, X> = std::slice::IterMut<'a, X>;

#[derive(Clone, Serialize, Deserialize)]
pub struct Program<Id, T, U> {
    pub module: Module<Id, T, U>,
    pub fixities: Fixities<Id>,
    pub comments: Vec<Comment>,
}

impl<Id, T, U> Program<Id, T, U> {
    pub fn modname(&self) -> &Chain<Id> {
        &self.module.modname
    }

    pub fn module_srcpath(&self) -> &U {
        &self.module.srcpath
    }

    pub fn fixities_iter(&self) -> std::slice::Iter<'_, (Id, fixity::Fixity)> {
        self.fixities.iter()
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

impl<Id, T, U> std::fmt::Debug for Program<Id, T, U>
where
    Id: std::fmt::Debug,
    T: std::fmt::Debug,
    U: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Program")
            .field("module", &self.module)
            .field("fixities", &self.fixities)
            .finish_non_exhaustive()
        // .field("comments", &self.comments)
        // .finish()
    }
}
