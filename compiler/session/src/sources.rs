use wy_failure::Failure;
use wy_parser::error::ParseError;
use wy_sources::Atlas;
use wy_syntax::Ast;

pub fn parse_atlas(atlas: &Atlas) -> Result<Ast, Failure<ParseError>> {
    let mut tree = Ast::new();

    for src in atlas.sources_iter() {
        let program = wy_parser::try_parse_file(src)?;
        tree.add_program(program);
    }

    Ok(tree)
}

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn test_prim_() {
        match Atlas::walk_path("../../language") {
            Err(e) => eprintln!("{}", e),
            Ok(paths) => {
                let mut atlas = Atlas::new();
                atlas.add_paths(paths);
                match parse_atlas(&atlas) {
                    Err(e) => eprintln!("{}", e),
                    Ok(tree) => {
                        println!("Success!");
                        println!("{:?}", &tree)
                    }
                }
            }
        }
    }
}
