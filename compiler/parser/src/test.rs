#![cfg(test)]
use wy_intern::Symbol;

use super::*;

fn infixed(left: Expression, infix: wy_intern::Symbol, right: Expression) -> Expression {
    Expression::Infix {
        infix: Ident::Infix(infix),
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn tuplex<const N: usize>(subexps: [Expression; N]) -> Expression {
    Expression::Tuple(subexps.to_vec())
}

#[test]
fn test_infix_exprs() {
    use Expression::Lit;
    let [op1, op2, plus, times, minus, fun] =
        wy_intern::intern_many(["<>", "><", "+", "*", "-", "fun"]);
    let int = |n| Lit(Literal::Int(n));

    let tests = [
        (
            "1 + 2 * 3 - 4",
            infixed(
                int(1),
                plus,
                infixed(int(2), times, infixed(int(3), minus, int(4))),
            ),
        ),
        (
            "(1, 2, 3) <> (4, 5, 6) >< (7, 8, 9)",
            infixed(
                tuplex([int(1), int(2), int(3)]),
                op1,
                infixed(
                    tuplex([int(4), int(5), int(6)]),
                    op2,
                    tuplex([int(7), int(8), int(9)]),
                ),
            ),
        ),
        (
            "fun 1 2",
            Expression::App(
                Box::new(Expression::App(
                    Box::new(Expression::Ident(Ident::Lower(fun))),
                    Box::new(int(1)),
                )),
                Box::new(int(2)),
            ),
        ),
    ];

    for (src, expected) in tests {
        assert_eq!(Parser::from_str(src).expression().unwrap(), expected);
    }

    println!(
        "{:#?}",
        Parser::from_str(
            r#"
fn foo :: a -> (a, a)
| x = (x, x)
| _ = let some x y if x > y = Some (x, y) 
| x y = Some (y, x) in some 1 1
"#
        )
        .function_decl()
    )
}

#[test]
fn let_expr() {
    let src = r#"
    let foo | 1 = 2 
            | 3 = 4
      , bar | x y = (x, y) where y = x + 2
    in bar (foo 1) (foo 2)
"#;
    let result = Parser::from_str(src).expression();
    println!("{:#?}", &result)
}

#[test]
fn case_expr() {
    let src = r#"
case f x of {
A c -> c;
B d if c d -> h;
y -> y;
}
"#;
    let [a, b, c, d, h, f, x, y] = wy_intern::intern_many(["A", "B", "c", "d", "h", "f", "x", "y"]);
    let expr = Parser::from_str(src).case_expr();
    println!("{:#?}", &expr);
    let expected = Expression::Case(
        Box::new(Expression::App(
            Box::new(Expression::Ident(Ident::Lower(f))),
            Box::new(Expression::Ident(Ident::Lower(x))),
        )),
        vec![
            Alternative {
                pat: Pattern::Dat(Ident::Upper(a), vec![Pattern::Var(Ident::Lower(c))]),
                pred: None,
                body: Expression::Ident(Ident::Lower(c)),
                wher: vec![],
            },
            Alternative {
                pat: Pattern::Dat(Ident::Upper(b), vec![Pattern::Var(Ident::Lower(d))]),
                pred: Some(Expression::App(
                    Box::new(Expression::Ident(Ident::Lower(c))),
                    Box::new(Expression::Ident(Ident::Lower(d))),
                )),
                body: Expression::Ident(Ident::Lower(h)),
                wher: vec![],
            },
            Alternative {
                pat: Pattern::Var(Ident::Lower(y)),
                pred: None,
                body: Expression::Ident(Ident::Lower(y)),
                wher: vec![],
            },
        ],
    );
    assert_eq!(expr, Ok(expected))
}

const fn var(s: Symbol) -> Pattern<Ident> {
    Pattern::Var(Ident::Lower(s))
}

#[test]
fn test_pattern() {
    let int = |n| Pattern::Lit(Literal::Int(n));
    let [a, b, c, d] = wy_intern::intern_many(["a", "b", "c", "d"]);
    let id = |s| Pattern::Var(Ident::Lower(s));
    let pairs = [
        ("(a, b)", Pattern::Tup(vec![id(a), id(b)])),
        (
            "(a:b:(c:d))",
            Pattern::Vec(vec![id(a), id(b), Pattern::Vec(vec![id(c), id(d)])]),
        ),
        (
            "a @ [1, 2, 3]",
            Pattern::At(
                Ident::Lower(a),
                Box::new(Pattern::Vec(vec![int(1), int(2), int(3)])),
            ),
        ),
        (
            "(a:b:[c, d])",
            Pattern::Vec(vec![id(a), id(b), id(c), id(d)]),
        ),
        ("(a:[])", Pattern::Vec(vec![id(a)])),
    ];

    for (s, x) in pairs {
        assert_eq!(Parser::from_str(s).pattern(), Ok(x))
    }
}

macro_rules! with_vars {
    (|$($ids:ident $(,)?)+| { $($rest:tt)* }) => {{
        #[allow(non_snake_case, unused)]
        let [ $($ids,)+ ] =
            wy_intern::intern_many([ $(stringify!($ids)),+ ]);
        let result = {
            $($rest)*
        };
        result
    }};
}

#[test]
fn test_lambda_expr() {
    let src = r#"\x -> f x"#;
    let expr = Parser::from_str(src).expression().unwrap();
    let expected = with_vars!(|x f| {
        Expression::Lambda(
            Pattern::Var(Ident::Lower(x)),
            Box::new(Expression::App(
                Box::new(Expression::Ident(Ident::Lower(f))),
                Box::new(Expression::Ident(Ident::Lower(x)))
            ))
        )
    });
    assert_eq!(expr, expected);
    println!("{:?}", expr);
    println!("{:?}", Parser::from_str(r#"\ a | b -> c"#).expression());
}

#[test]
fn test_types() {
    let src = "Foo x y z -> Bar z y x";
    let result = Parser::from_str(src).ty_node().unwrap();
    println!("{}", &result);
    assert_eq!(
        result,
        with_vars! { |Foo x y z Bar| {
            Type::Fun(
                Box::new(Type::Con(
                    Ident::Upper(Foo), vec![
                        Type::Var(Tv::from_symbol(x)),
                        Type::Var(Tv::from_symbol(y)),
                        Type::Var(Tv::from_symbol(z))],
                    )),
                Box::new(Type::Con(
                    Ident::Upper(Bar), vec![
                        Type::Var(Tv::from_symbol(z)),
                        Type::Var(Tv::from_symbol(y)),
                        Type::Var(Tv::from_symbol(x))
                    ]
                ))
        )} }
    )
}

#[test]
fn test_inst_decl() {
    let src = r#"
impl |Eq a| Eq [a] {
    (==)
    | [] [] = True
    | (x:xs) (y:ys) = (x == y) && (xs == ys)
    | _ _ = False
}
"#;
    let program = Parser::from_str(src).inst_decl();
    println!("{:#?}", program);
}

#[test]
fn parse_imports() {
    let src = r#"
import A.thing.from.Somewhere @ A { foo, bar }
| B.things.elsewhere @ B { baz }
"#;
    let program = Parser::from_str(src).imports();
    let expected = with_vars!(
        |A thing from Somewhere foo bar B things elsewhere baz| {
        vec![ImportSpec {
            name: Chain::new(Ident::Upper(A), vec![
                Ident::Lower(thing),
                Ident::Lower(from),
                Ident::Upper(Somewhere)
            ].into_iter().collect()),
            qualified: false,
            rename: Some(Ident::Upper(A)),
            hidden: false,
            imports: vec![
                Import::Function(Ident::Lower(foo)),
                Import::Function(Ident::Lower(bar))
            ]},
            ImportSpec {
                name: Chain::new(
                    Ident::Upper(B),
                    vec![
                        Ident::Lower(things),
                        Ident::Lower(elsewhere)
                    ].into_iter().collect()
                ),
                qualified: false,
                rename: Some(Ident::Upper(B)),
                hidden: false,
                imports: vec![
                    Import::Function(Ident::Lower(baz))
                ].into_iter().collect()
            }]
    });
    assert_eq!(Ok(expected), program)
}

#[test]
fn parse_prim_module() {
    let src = include_str!("../../../language/prim.wy");
    let result = Parser::from_str(src).parse();

    println!("{:#?}", result);
    let mut parser = Parser::from_str(src);
    for _ in 0..10 {
        println!("{:?}", parser.get_loc());
        println!("{:?}", parser.peek());
        println!("{:?}", parser.get_loc());
        println!("{:?}", parser.bump());
    }
}

#[test]
fn test_cons_pat() {
    let link = with_vars!(|a, b, c| {
        Pattern::Lnk(
            Box::new(var(a)),
            Box::new(Pattern::Lnk(Box::new(var(b)), Box::new(var(c)))),
        )
    });
    assert_eq!(Ok(link), Parser::from_str("(a:b:c)").pattern())
}
