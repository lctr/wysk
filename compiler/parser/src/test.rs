#![cfg(test)]
use wy_intern::{symbol, Symbol, Symbolic};
use wy_lexer::Literal;
use wy_syntax::{expr::Expression, pattern::Pattern, stmt::Alternative};

use super::*;
use decl::*;
use expr::ExprParser;
use fixity::*;

#[test]
fn parse_imports() {
    let src = r#"
import A.thing.from.Somewhere @ A { foo, bar }
| B.things.elsewhere @ B { baz }
"#;
    let program = Parser::from_str(src).imports();
    let [a_con, thing, from, somewhere_con, foo, bar, b_con, things, elsewhere, baz] =
        wy_intern::intern_many([
            "A",
            "thing",
            "from",
            "Somewhere",
            "foo",
            "bar",
            "B",
            "things",
            "elsewhere",
            "baz",
        ]);
    let expected = vec![
        ImportSpec {
            name: Chain::new(
                Ident::Upper(a_con),
                vec![
                    Ident::Lower(thing),
                    Ident::Lower(from),
                    Ident::Upper(somewhere_con),
                ]
                .into_iter()
                .collect(),
            ),
            qualified: false,
            rename: Some(Ident::Upper(a_con)),
            hidden: false,
            imports: vec![
                Import::Function(Ident::Lower(foo)),
                Import::Function(Ident::Lower(bar)),
            ],
        },
        ImportSpec {
            name: Chain::new(
                Ident::Upper(b_con),
                vec![Ident::Lower(things), Ident::Lower(elsewhere)]
                    .into_iter()
                    .collect(),
            ),
            qualified: false,
            rename: Some(Ident::Upper(b_con)),
            hidden: false,
            imports: vec![Import::Function(Ident::Lower(baz))]
                .into_iter()
                .collect(),
        },
    ];
    assert_eq!(Ok(expected), program)
}

#[test]
fn parse_prim_module() {
    let src = include_str!("../../../language/prim.wy");
    let result = Parser::from_str(src).parse();
    // let dcons = result.as_ref().map(|prog| prog.module.data_ctors());
    match result {
        Ok(program) => {
            println!("showing prim.wy: {:?}", program.module)
        }
        Err(err) => {
            println!("{}", err)
        }
    }
}
