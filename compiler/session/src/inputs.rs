use std::{path::Path, sync::Arc};

use serde::{Deserialize, Serialize};
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
#[derive(Clone, Debug, Serialize, Deserialize)]
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
                    // shorten the path displayed by providing the project root
                    // the `SrcPath` variant will change if it is a file, to a
                    // variant that shows only the portion of the path beginning
                    // in the directory of the root
                    fail = fail.with_srcpath_root(self.project.root_dir());
                    eprintln!("{fail}");
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
    use std::{io::Write, path::PathBuf};

    use super::*;
    use bincode;
    use serde_json;

    // A NOTE RE: SERIALIZING AND DESERIALIZING: `Symbol`s will be
    // serialized as newtypes around `u32`, losing string/identifier
    // information, therefore any valid serialization of types
    // containing `Symbol`s must also include a serialization of the
    // global symbol table/interner...
    #[allow(unused)]
    fn serialize_bincode_to(trees: &[Tree], p: &str) {
        let path = PathBuf::from(p);
        match bincode::serialize(trees) {
            Ok(bytes) => match std::fs::File::create(path) {
                Ok(mut file) => match file.write(&bytes[..]) {
                    Ok(n) => println!("{n} bytes written to `{p}`"),
                    Err(e) => eprintln!("error writing serialized prelude ast: {e}"),
                },
                Err(e) => eprintln!("error creating file: {e}"),
            },
            Err(err) => eprintln!("error serializing prelude AST to binary: {err}"),
        };
    }

    #[allow(unused)]
    fn serialize_json_to(trees: &[Tree], p: &str) {
        let path = PathBuf::from(p);
        match std::fs::File::create(path) {
            Ok(file) => match serde_json::to_writer_pretty(file, trees) {
                Ok(_) => println!("AST serialized to JSON format and written to file `{p}`"),
                Err(e) => eprintln!("error serializing prelude AST to json: {e}"),
            },
            Err(e) => eprintln!("error creating file: {e}"),
        }
    }

    #[test]
    fn load_and_parse_prelude() {
        let mut sess = Session::new(wy_sources::prelude_project());
        let (succeeded, failed) = sess.parse_unread();
        println!("`{succeeded}` prelude modules successfully parsed.\n`{failed}` prelude modules failed to parse.");
        assert!(failed == 0);
        assert!(sess.project.stored_files().count() == succeeded);
        // serialize_bincode_to(&sess.trees[..], "../../tmp/prelude_ast_binser");
        // serialize_json_to(&sess.trees[..], "../../tmp/prelude_ast.json")
    }
}
