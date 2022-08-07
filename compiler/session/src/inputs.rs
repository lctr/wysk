#[cfg(test)]
mod test {
    use wy_common::functor::{Func, MapFst, MapThrd};
    use wy_syntax::tipo::Tv;

    #[test]
    fn qualify_prelude_ast_ids() {
        let qualified = wy_parser::parse_standalone_file("../../language/prelude/src/container.wy")
            .map(|program| {
                let modname = program.modname().clone();
                program
                    .map_fst(&mut Func::Fresh(|id| modname.with_suffix(id).as_ident()))
                    .map_thrd(&mut Func::Fresh(|t| Tv::from_ident(t)))
            });
        match qualified {
            Ok(res) => println!("{res:#?}"),
            Err(e) => eprintln!("{e}"),
        }
    }
}
