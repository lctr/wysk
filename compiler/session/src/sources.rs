use wy_check::typed::envr::{self, Environment};
use wy_failure::Outcome;
use wy_parser::error::ParseError;
use wy_sources::paths::Atlas;
use wy_syntax::Ast;

/// Blindly finds all wysk files contained within a directory, then parsing each
/// file in the order in which they were found regardless as to whether they are
/// referenced/are used as dependencies at all.
pub fn parse_atlas(atlas: &Atlas) -> Outcome<Ast, ParseError> {
    atlas.sources_iter().fold(Ok(Ast::new()), |tree, src| {
        tree.and_then(|mut ast| {
            wy_parser::try_parse_file(src).map(|program| {
                ast.add_program(program);
                ast
            })
        })
    })
}

pub fn parse_prelude() -> Outcome<Ast, ParseError> {
    let atlas = Atlas::new_within_dir("../../language")
        .map_err(wy_failure::normalize_io_err::<ParseError>)?;
    parse_atlas(&atlas)
}

pub fn prelude_environment() -> Outcome<(Ast, Environment), ParseError> {
    parse_prelude().map(|tree| {
        let env = envr::ast_environment(&tree);
        (tree, env)
    })
}

#[cfg(test)]
mod test {

    use wy_common::{push_if_absent, Map};
    use wy_syntax::Program;

    use super::*;

    #[test]
    fn test_prim_uniques_write() {
        if let Ok(tree) = parse_prelude() {
            let tree = tree.qualify_idents();
            println!(
                "size of tree after uniquifying: {} bytes",
                std::mem::size_of_val(&tree)
            );
            let data = format!("{:#?}", &tree);
            let _ = std::fs::write("../../tmp/prelude_ast_debug.txt", data);
        }
    }

    #[test]
    fn test_prelude_tyenv() {
        match prelude_environment() {
            Ok(env) => println!("{:#?}", env),
            Err(e) => eprintln!("{}", e),
        }
    }

    #[test]
    fn inspect_prelude_deps() {
        match parse_prelude() {
            Err(e) => eprintln!("{}", e),

            Ok(tree) => {
                let imports = tree
                    .programs_iter()
                    .map(|prog| {
                        let ims = prog.get_imports_iter().fold(vec![], push_if_absent);
                        (prog.module_id(), prog.modname(), ims)
                    })
                    .collect::<Vec<_>>();
                println!("Program Imports");
                imports.iter().for_each(|(mid, mname, ims)| {
                    println!("\n  {} = {}", mid, mname);
                    ims.iter().enumerate().for_each(|(n, imp)| {
                        println!(
                            "    | #{}. {} {}",
                            n,
                            &imp.name,
                            if let Some(rename) = &imp.rename {
                                format!("@ {}", rename)
                            } else {
                                String::new()
                            }
                        )
                    });
                });
            }
        }
    }
}
