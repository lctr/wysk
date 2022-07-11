#![cfg(test)]
use wy_intern::{symbol, Symbol, Symbolic};
use wy_lexer::Literal;
use wy_syntax::{expr::Expression, pattern::Pattern, stmt::Alternative};

use super::*;
use expr::ExprParser;

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

fn infixed(left: RawExpression, infix: wy_intern::Symbol, right: RawExpression) -> RawExpression {
    Expression::Infix {
        infix: Ident::Infix(infix),
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn tuplex<const N: usize>(subexps: [RawExpression; N]) -> RawExpression {
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
    println!("showing let:\n{:#?}", &result)
}

const fn var<T>(s: Symbol) -> Pattern<Ident, T> {
    Pattern::Var(Ident::Lower(s))
}

#[test]
fn test_pattern() {
    let int = |n| Pattern::Lit(Literal::Int(n));
    let [a, b, c, d] = wy_intern::intern_many(["a", "b", "c", "d"]);
    let id = |s| Pattern::Var(Ident::Lower(s));
    let lnk = |px, py| Pattern::Lnk(Box::new(px), Box::new(py));
    let pairs = [
        ("(a, b)", Pattern::Tup(vec![id(a), id(b)])),
        ("(a:b:(c:d))", lnk(id(a), lnk(id(b), lnk(id(c), id(d))))),
        (
            "a @ [1, 2, 3]",
            Pattern::At(
                Ident::Lower(a),
                Box::new(Pattern::Vec(vec![int(1), int(2), int(3)])),
            ),
        ),
        (
            "(a:b:[c, d])",
            lnk(id(a), lnk(id(b), Pattern::Vec(vec![id(c), id(d)]))),
        ),
        ("(a:[])", lnk(id(a), Pattern::Vec(vec![]))),
    ];

    for (s, x) in pairs {
        assert_eq!(Parser::from_str(s).pattern(), Ok(x))
    }
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
    println!("{:?}", &expr);
}

#[test]
fn test_type_app() {
    let src = "Foo x y z -> Bar (z, y) x";
    let result = Parser::from_str(src).ty_node().unwrap();
    println!("{}", &result);
    let var = Ident::Lower;
    assert_eq!(
        result,
        with_vars! { |Foo x y z Bar| {
            Type::Fun(
                Box::new(Type::Con(
                    Con::Data(Ident::Upper(Foo)), vec![
                        Type::Var(var(x)),
                        Type::Var(var(y)),
                        Type::Var(var(z))],
                    )),
                Box::new(Type::Con(
                    Con::Data(Ident::Upper(Bar)), vec![
                        Type::Tup(vec![
                            Type::Var(var(z)),
                            Type::Var(var(y)),
                        ]),
                        Type::Var(var(x))
                    ]
                ))
        )} }
    )
}

#[test]
fn test_arrow_ty_assoc() {
    let src = "a -> b -> c -> d";
    let result = Parser::from_str(src).ty_node().unwrap();
    println!("{}", &result);
    let expected = with_vars! { |a b c d| {
        Type::Fun(
            Box::new(
                Type::Var(Ident::Lower(a))
            ),
            Box::new(
                Type::Fun(
                    Box::new(Type::Var(Ident::Lower(b))),
                    Box::new(Type::Fun(
                        Box::new(
                            Type::Var(Ident::Lower(c))
                        ), Box::new(
                            Type::Var(Ident::Lower(d))
                        )
                    ))
                )
            )
        )
    }};
    assert_eq!(result, expected)
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
    println!("showing inst decl: {:#?}", program);
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

#[test]
fn test_ty_sigs() {
    let src = r#"forall a b. m a -> (a -> m b) -> m b"#;
    let sig = Parser::from_str(src).total_signature().unwrap();
    let expected = with_vars!(|a b m| { Signature {
        each: vec![Ident::Lower(a), Ident::Lower(b)],
        ctxt: vec![],
        tipo: Type::Fun(
            Box::new(
                Type::Con(Con::Free(Ident::Lower(m)), vec![Type::Var(Ident::Lower(a))])
            ),
            Box::new(
                Type::Fun(
                    Box::new(
                        Type::Fun(
                            Box::new(Type::Var(Ident::Lower(a))),
                            Box::new(Type::Con(Con::Free(Ident::Lower(m)),
                                vec![Type::Var(Ident::Lower(b))])))
                    ),
                    Box::new(
                        Type::Con(Con::Free(Ident::Lower(m)), vec![Type::Var(Ident::Lower(b))])
                    )
                )
            ),
        )
    }});
    println!("showing ty sigs: {:#?}\n{}", &sig, &sig.tipo);
    assert_eq!(expected, sig)
}

#[test]
fn test_newtype_decl() {
    let src = r#"newtype Parser a = Parser { parse :: String -> (a, String) }"#;
    let parsed = Parser::from_str(src).newtype_decl().unwrap();
    let expected = with_vars! { |Parser a parse String| {
        NewtypeDecl {
            name: Ident::Upper(Parser),
            poly: vec![Ident::Lower(a)],
            ctor: Ident::Upper(Parser),
            narg: NewtypeArg::Record(Ident::Lower(parse), Signature {
                each: vec![],
                ctxt: vec![],
                tipo: Type::mk_fun(
                    Type::Con(Con::Data(Ident::Upper(String)), vec![]),
                    Type::Tup(vec![
                        Type::Var(Ident::Lower(a)),
                        Type::Con(Con::Data(Ident::Upper(String)), vec![])
                    ])
                )
            }),
            with: vec![]
        }
    }};
    assert_eq!(parsed, expected)
}

#[test]
fn test_caf() {
    let tests = [
        "fn womp :: |Num a| a = 3",
        "fn womp :: |Num a| a | = 3",
        "fn womp :: |Num a| a => 3",
    ]
    .into_iter()
    .map(|s| Parser::from_str(s).function_decl().unwrap())
    .collect::<Vec<_>>();
    assert_eq!(tests[0], tests[1]);
    assert_eq!(tests[1], tests[2]);
}

#[test]
fn test_record_expr() {
    let src = "
fn some_record_function 
    | a @ A { b, c } = a { 
        b = b + 2,
        c = c a 3 
    }
    | a @ A { b = (1 | 2), c } = a { 
        b, 
        c = c a 3 
    }
";
    println!("{:?}", Parser::from_str(src).function_decl())
}

#[test]
fn test_do_expr() {
    let src = "do { (a, b) <- get'pair; x <- [1..m]; print (a, b) }";
    println!("{:?}", Parser::from_str(src).do_expr())
}

#[test]
fn test_section_expr() {
    use wy_syntax::expr::Section::*;
    use Expression as E;
    use Literal::*;
    let src = "map (+5) [1, 2, 3]";
    let [map, plus] = symbol::intern_many(["map", "+"]);
    let map = Ident::Lower(map);
    let plus = Ident::Infix(plus);
    let expected: RawExpression = E::App(
        Box::new(E::App(
            Box::new(E::Ident(map)),
            Box::new(E::Section(Prefix {
                prefix: plus,
                right: Box::new(E::Lit(Int(5))),
            })),
        )),
        Box::new(E::Array(vec![
            E::Lit(Int(1)),
            E::Lit(Int(2)),
            E::Lit(Int(3)),
        ])),
    );
    assert_eq!(Parser::from_str(src).expression(), Ok(expected))
}

#[test]
fn test_list_comprehension() {
    let src = "[ f x | x <- [0..n] ]";
    let mut parser = Parser::from_str(src);
    let expr = parser.expression();
    println!("{:?}", &expr);
    println!("{:?}", &parser);
}

#[test]
fn test_data_ctor() {
    let mut it = Parser::from_str("a [a]");
    println!("{:?}", it.ty_atom());
    println!("{:?}", it.ty_atom());
    let mut it = Parser::from_str("a [a -> a]");
    println!("{:?}", it.ty_atom());
    println!("{:?}", it.ty_atom());
    let src = "data NonEmpty a = NonEmpty a [a]";
    let mut parser = Parser::from_str(src);
    let expr = parser.data_decl();
    match expr {
        Ok(decl) => println!("{:?}", decl),
        Err(e) => println!("{}", e),
    }
}

#[test]
fn test_data_record() {
    let mut it = Parser::from_str(
        "
    ~~~ A file with random code in Wysk, primarily to get a feel for things
    module Sample where
    
    
    fn differentiate :: |Num a| (a -> a) -> a -> a -> a
    | f dx x = (f (x + dx) - f x) / dx
    
    fn integrate :: |Num a| (a -> a) -> [a] -> a -> a 
    | _ [] _ = 0 ~~ trivially equivalent to an empty domain?
    | f [_] _ = 0 ~~ the integral over a single point is 0
    | f xs dx = sum <| f `over` xs <| dx
    where sum [] = 0 | (y:ys) = y + sum ys
        , over f xs dx = [ (f x) * dx | x <- xs ];
    
    
    data Literal 
        = Byte Byte 
        | Int Int 
        | Char Char 
        | Flt Float 
        | Dbl Double 
        | Str String 
        with (Show, Eq, Ord)
    
    data Ident 
        = Upper Symbol 
        | Lower Symbol 
        | Infix Symbol 
        with Eq
    
    data Lexeme 
        = Lit Literal
        | Var Ident
        | Kw Keyword 
        | At     | Wildcard
        | Equal  | Pipe 
        | Semi   | Comma
        | Escape | Dot
        | Colon2 | Dot2
        | ParenL | ParenR
        | BrackL | BrackR
        | CurlyL | CurlyR
        | ArrowR | ArrowL
        with (Eq, Show)
    
    data Token a = Tok { 
        lexeme :: Lexeme, 
        span :: Span 
    } with (Eq, Show) 
     
    class Store s {
        lookup :: |Eq a| s a b -> a -> Option b;
        insert :: |Eq a| s a b -> (a, b) -> Option b;
    }
    
    newtype Line = Row Int with (Eq, Ord, Show)
    newtype Column = Col Int with (Eq, Ord, Show)
    newtype Symbol = Sym Int with (Eq, Ord, Show)
    newtype Pos = Pos Byte with (Eq, Ord, Show)
    newtype Span = Span Pos Pos with (Eq, Ord, Show)
    newtype Position = Pos (Line, Column) with (Eq, Ord, Show)
    
    data Location = Loc { line :: Row, column :: Column, pos :: Pos } 
        with (Eq, Show)
    
    
    
    ",
    );
    let d = it.parse();
    println!("{:?}", d);
    assert!(d.is_ok())
}

#[test]
fn inspect_expr() {
    println!(
        "{:?}",
        parse_expression("do { let x = 5; x <- [a..b]; x <- [1..b]; return x }")
    );
}
