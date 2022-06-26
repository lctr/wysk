use wy_failure::Failure;
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

pub fn parse_prelude() -> Result<Ast, Failure<ParseError>> {
    let atlas = Atlas::new_within_dir("../../language")?;
    parse_atlas(&atlas)
}

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn test_prim_() {
        if let Ok(tree) = parse_prelude() {
            let data = format!("{:#?}", &tree);
            let _ = std::fs::write("prelude_ast_debug.txt", data);
        }
    }
}
