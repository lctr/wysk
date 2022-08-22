use std::{path::Path, sync::Arc};

use wy_failure::SrcPath;
use wy_name::Ident;
use wy_parser::error::ParseFailure;
use wy_sources::{files::File, paths::FilePath, Project};
use wy_syntax::{ast::respan::ReSpan, Program};

/// Syntax trees will have varying representations based on their
/// parameterized (identifier) types. We start with `Raw`, the very
/// same type returned by the `Parser`, and then work our way to a
/// more refined AST, eventually aiming to reduce it to a simpler
/// representation.
#[derive(Clone, Debug)]
pub enum Tree {
    Raw(Program<Ident, Ident, SrcPath>),
}

impl Tree {
    pub fn get_srcpath(&self) -> &SrcPath {
        match self {
            Tree::Raw(prog) => prog.module_srcpath(),
        }
    }

    pub fn get_path(&self) -> Option<&Path> {
        match self {
            Tree::Raw(prog) => prog.module_srcpath().as_path(),
        }
    }
}

#[derive(Debug)]
pub struct Session {
    project: Project,
    trees: Vec<Tree>,
    failed_parses: Vec<(FilePath, ParseFailure)>,
}

impl Session {
    pub fn new(project: Project) -> Self {
        Session {
            project,
            trees: vec![],
            failed_parses: vec![],
        }
    }

    pub fn trees_iter(&self) -> std::slice::Iter<'_, Tree> {
        self.trees.iter()
    }

    pub fn tree_paths<'a>(&'a self) -> impl Iterator<Item = &'a Path> + 'a {
        self.trees_iter()
            .flat_map(|tree| tree.get_path().into_iter())
    }

    pub fn unread_files(&self) -> Vec<Arc<File>> {
        let paths = self.tree_paths().collect::<Vec<_>>();
        self.project
            .stored_files()
            .filter_map(move |file| {
                if !paths.contains(&file.src_path().path()) {
                    Some(file.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
    }

    pub fn parse_unread(&mut self) -> (usize, usize) {
        let mut successful = 0;
        let mut failures = 0;
        self.unread_files().into_iter().for_each(|file| {
            let byte_offset = file.start_pos();
            match wy_parser::parse_file(&file) {
                Ok(mut prog) => {
                    prog.module.respan(byte_offset);
                    self.trees.push(Tree::Raw(prog));
                    successful += 1;
                }
                Err(mut fail) => {
                    fail.respan(byte_offset);
                    self.failed_parses.push((file.src_path().clone(), fail));
                    failures += 1;
                }
            }
        });
        (successful, failures)
    }
}

#[cfg(test)]
mod test {
    #![allow(unused)]
    use super::*;
    use wy_common::functor::{Func, MapFst, MapThrd};
    use wy_syntax::tipo::Tv;

    #[test]
    fn load_and_parse_prelude() {
        let mut sess = Session::new(wy_sources::prelude_project());
        let (succeeded, failed) = sess.parse_unread();
        println!("`{succeeded}` prelude modules successfully parsed. `{failed}` prelude modules failed to parse.");
        assert!(failed == 0);
        assert!(sess.project.stored_files().count() == succeeded);
        println!("{:?}", &sess)
    }
}
