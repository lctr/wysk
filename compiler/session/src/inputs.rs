use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

use serde::{Deserialize, Serialize};
use wy_common::VecDeque;
use wy_failure::SrcPath;
use wy_intern::Symbol;
use wy_name::{Chain, Ident};
use wy_parser::error::ParseFailure;
use wy_sources::{files::File, paths::FileId, Project};
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
    trees: Vec<(FileId, Tree)>,
    failed_parses: Vec<(FileId, ParseFailure)>,
}

impl Session {
    pub fn new(project: Project) -> Self {
        Session {
            project,
            trees: vec![],
            failed_parses: vec![],
        }
    }

    pub fn trees_iter(&self) -> std::slice::Iter<'_, (FileId, Tree)> {
        self.trees.iter()
    }

    pub fn tree_paths<'a>(&'a self) -> impl Iterator<Item = &'a Path> + 'a {
        self.trees_iter()
            .flat_map(|tree| tree.1.get_path().into_iter())
    }

    pub fn atlas_has_path(&self, p: impl AsRef<Path>) -> bool {
        let path = p.as_ref();
        self.project.filepaths().any(|fp| fp.path() == path)
    }

    pub fn has_file_for_path(&self, p: impl AsRef<Path>) -> bool {
        let path = p.as_ref();
        self.project
            .stored_files()
            .any(|file| file.src_path().path() == path)
    }

    pub fn file_id_is_parsed(&self, file_id: &FileId) -> bool {
        self.trees_iter().any(|(id, _)| id == file_id)
    }

    pub fn path_is_parsed(&self, p: impl AsRef<Path>) -> bool {
        let file_id_is_parsed = self
            .project
            .get_file_id_for_stored(p)
            .as_ref()
            .map(|id| self.file_id_is_parsed(id));
        matches!(file_id_is_parsed, Some(true))
    }

    pub fn unread_files(&self) -> VecDeque<Arc<File>> {
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
            .collect::<VecDeque<_>>()
    }

    pub fn parse_unread(&mut self) -> (usize, usize) {
        let mut successful = 0;
        let mut failures = 0;
        self.unread_files().into_iter().for_each(|file| {
            if self.parse_file_store_ast(file) {
                successful += 1
            } else {
                failures += 1
            }
        });
        (successful, failures)
    }

    pub fn parse_file_store_ast(&mut self, file: Arc<File>) -> bool {
        let byte_offset = file.start_pos();
        match wy_parser::parse_file(&file) {
            Ok(mut prog) => {
                prog.module.respan(byte_offset);
                self.trees.push((file.id(), Tree::Raw(prog)));
                true
            }
            Err(mut fail) => {
                fail = fail.with_srcpath_root(self.project.root_dir());
                fail.respan(byte_offset);
                self.failed_parses.push((file.id(), fail));
                false
            }
        }
    }

    pub fn parse_file(
        &mut self,
        file: Arc<File>,
    ) -> (
        Arc<File>,
        Result<Program<Ident, Ident, SrcPath>, ParseFailure>,
    ) {
        let byte_offset = file.start_pos();
        let result = match wy_parser::parse_file(&file) {
            Ok(mut prog) => {
                prog.module.respan(byte_offset);
                Ok(prog)
            }
            Err(mut fail) => {
                fail = fail.with_srcpath_root(self.project.root_dir());
                fail.respan(byte_offset);
                Err(fail)
            }
        };
        (file, result)
    }

    pub fn store_parsed_ast(
        &mut self,
        file_id: FileId,
        program: Program<Ident, Ident, SrcPath>,
    ) -> usize {
        if let Some(n) = self.trees_iter().position(|(id, _)| id == &file_id) {
            n
        } else {
            let n = self.trees.len();
            self.trees.push((file_id, Tree::Raw(program)));
            n
        }
    }

    pub fn store_parse_error(&mut self, file_id: FileId, failure: ParseFailure) {
        self.failed_parses.push((file_id, failure))
    }

    pub fn print_parse_failures(&self) {
        self.failed_parses
            .iter()
            .for_each(|(_, err)| eprintln!("{err}"))
    }
}

pub fn parsed_file_deps(
    sess: &mut Session,
    file: Arc<File>,
    tree: &Program<Ident, Ident, SrcPath>,
) -> (FileId, Vec<(Symbol, PathBuf)>, Option<SessError>) {
    let srcpath = tree.module_srcpath().clone();
    let dir = srcpath
        .as_path()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| sess.project.root_dir().path().join("src"));
    let (queue, missing) = tree
        .module
        .imported_modules()
        .map(|chain| {
            let sym_chain = chain.map(|id| id.symbol());
            let path = sym_chain.as_file_in(&dir);
            (sym_chain, path)
        })
        .fold(
            (vec![], vec![]),
            |(mut paths, mut missing), (import_name, import_path)| {
                match import_path {
                    Some(p) => paths.push((import_name.flattened_symbol(), p)),
                    None => missing.push(import_name),
                };
                (paths, missing)
            },
        );
    (
        file.id(),
        queue,
        if missing.is_empty() {
            None
        } else {
            Some(SessError::UnresolvedImport(file.id(), missing))
        },
    )
}

pub fn parse_next_by_dependencies(
    sess: &mut Session,
    file: Arc<File>,
    tree: Program<Ident, Ident, SrcPath>,
) -> (Vec<(Symbol, FileId)>, Vec<SessError>) {
    let mut trees = vec![(file, tree)];
    let mut parsed = vec![];
    let mut unparsed = vec![];
    let mut missing = vec![];
    let mut failed_ids = vec![];
    while let Some((file, program)) = trees.pop() {
        let (file_id, deps, errs) = parsed_file_deps(sess, file, &program);
        if !wy_common::iter::has_snd(&mut parsed.iter(), &file_id) {
            parsed.push((program.modname().flattened_symbol(), file_id));
        }
        sess.store_parsed_ast(file_id, program);
        if let Some(err) = errs {
            missing.push(err);
        }
        println!("parsed file deps for {file_id}: {:#?}", &deps);
        for (dep_name, dep_path) in deps {
            let dp = dep_path.as_path();
            if let Some(file) = sess
                .unread_files()
                .into_iter()
                .find(|file| file.src_path().path() == dp)
            {
                if !wy_common::iter::has_snd(&mut parsed.iter(), &file.id()) {
                    parsed.push((dep_name, file.id()));
                }
                if !unparsed.contains(&file) {
                    unparsed.push(file)
                }
            }
        }
        for file in std::mem::take(&mut unparsed) {
            let file_id = file.id();
            if !failed_ids.contains(&file_id) {
                let (file, result) = sess.parse_file(file);
                match result {
                    Ok(prog) => {
                        if !trees.iter().any(|(a, _)| a.src_path().id() == file_id)
                            && parsed.iter().any(|(_, b)| b == &file_id)
                        {
                            trees.push((file, prog))
                        }
                    }
                    Err(failure) => {
                        sess.store_parse_error(file_id, failure);
                        if failed_ids.contains(&file_id) {
                            failed_ids.push(file_id);
                        }
                    }
                }
            }
        }
    }
    (parsed, missing)
}

#[derive(Debug)]
pub enum SessError {
    UnresolvedImport(FileId, Vec<Chain<Symbol>>),
    SyntaxError(ParseFailure),
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
        if failed > 0 {
            sess.print_parse_failures()
        }
        assert!(failed == 0);
        assert!(sess.project.stored_files().count() == succeeded);
        // serialize_bincode_to(&sess.trees[..], "../../tmp/prelude_ast_binser");
        // serialize_json_to(&sess.trees[..], "../../tmp/prelude_ast.json")
    }

    #[test]
    fn parse_one_file_and_get_dependencies() {
        let mut sess = Session::new(wy_sources::prelude_project());
        let mut unparsed = sess.unread_files();
        let first = unparsed.pop_front();
        assert!(first.is_some());
        let first = first.unwrap();
        let (file, result) = sess.parse_file(first);
        assert!(result.is_ok());
        println!("parse results: {:#?}", &result);
        let (file_id, upcoming, missing) =
            parsed_file_deps(&mut sess, file.clone(), result.as_ref().unwrap());
        println!("file: {file_id}");
        println!("next_deps: {:#?}", &upcoming);
        if let Some(not_found) = missing {
            println!("the following imports were not found: {:#?}", not_found);
        } else {
            println!("all declared imports exist in the workspace!");
        }
    }

    #[test]
    fn parse_by_dependencies() {
        let mut sess = Session::new(wy_sources::prelude_project());
        let mut unparsed = sess.unread_files();
        let first = unparsed.pop_front();
        assert!(first.is_some());
        let first = first.unwrap();
        let (file, result) = sess.parse_file(first);
        assert!(result.is_ok());
        // println!("parse results: {:#?}", &result);
        let (parsed, missing) = parse_next_by_dependencies(&mut sess, file, result.unwrap());
        println!("parsed: {:#?}", parsed);
        println!("missing dependencies: {:#?}", missing);
        println!("parsed trees:");
        for (file_id, tree) in sess.trees_iter() {
            print!("  {file_id}, ");
            match tree {
                Tree::Raw(prog) => print!("{}\n", prog.modname()),
            }
        }
        if !sess.failed_parses.is_empty() {
            sess.print_parse_failures()
        }
    }
}
