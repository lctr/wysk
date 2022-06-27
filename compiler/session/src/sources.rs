use wy_check::typed::envr::{self, Environment};
use wy_failure::{Failure, Outcome};
use wy_parser::error::ParseError;
use wy_sources::paths::Atlas;
use wy_syntax::Ast;

pub fn parse_atlas(atlas: &Atlas) -> Result<Ast, Failure<ParseError>> {
    let mut tree = Ast::new();

    for src in atlas.sources_iter() {
        let program = wy_parser::try_parse_file(src)?;
        tree.add_program(program);
    }

    Ok(tree)
}

pub fn parse_prelude() -> Outcome<Ast, ParseError> {
    let atlas = Atlas::new_within_dir("../../language")
        .map_err(wy_failure::normalize_io_err::<ParseError>)?;
    // let atlas = Atlas::with_prelude()
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
}
