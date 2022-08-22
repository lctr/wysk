use crate::error::*;
use crate::stream::*;

use wy_lexer::lexpat;
use wy_lexer::token::*;

use wy_syntax::decl::MethodBody;
use wy_syntax::decl::Selector;
use wy_syntax::decl::TypeArgs;
use wy_syntax::decl::WithClause;
use wy_syntax::decl::{
    AliasDecl, ClassDecl, DataDecl, Declaration, FixityDecl, FnDecl, InstDecl, MethodDef,
    NewtypeDecl, TypeArg, Variant,
};
use wy_syntax::fixity::Fixity;
use wy_syntax::stmt::Arm;
use wy_syntax::SpannedIdent;

type DeclParser<'t> = Parser<'t>;
// DECLARATIONS
impl<'t> DeclParser<'t> {
    pub fn declaration(&mut self) -> Parsed<Declaration> {
        use Declaration as D;
        match self.peek() {
            lexpat!(maybe[infixl][infixr][infix]) => self.fixity_decl().map(D::Fixity),
            lexpat!(~[data]) => self.data_decl().map(D::Data),
            lexpat!(~[fn]) => self.function_decl().map(D::Function),
            lexpat!(~[type]) => self.alias_decl().map(D::Alias),
            lexpat!(~[class]) => self.class_decl().map(D::Class),
            lexpat!(~[impl]) => self.inst_decl().map(D::Instance),
            lexpat!(~[newtype]) => self.newtype_decl().map(D::Newtype),
            Some(t) => Err({
                let t = *t;
                self.expected(LexKind::Keyword, t)
            }),
            _ => self.unexpected_eof().err(),
        }
    }

    fn fixity_decl(&mut self) -> Parsed<FixityDecl> {
        let start = self.get_pos();
        let assoc = self.fixity_assoc()?;
        let prec = self.fixity_prec()?;
        let fixity = Fixity { prec, assoc };
        let infixes = self.with_fixity(fixity)?;
        let from_pragma = false;
        let span = Span(start, self.get_pos());
        Ok(FixityDecl {
            span,
            infixes,
            fixity,
            from_pragma,
        })
    }

    fn data_decl(&mut self) -> Parsed<DataDecl> {
        use Keyword::Data;
        use Lexeme::{Equal, Semi};
        let start = self.get_pos();
        self.eat(Data)?;
        // (<pipe> <upper> <lower> (<comma> <upper> <lower>)* <pipe>)?
        let pred = self.ty_predicates()?;
        // <tycon> <tyvar>*
        let tdef = self.ty_simple()?;
        let (vnts, with) = if self.peek_on(Semi) {
            (vec![], None)
        } else {
            self.eat(Equal)?;
            (self.data_variants()?, self.with_clause()?)
        };
        let end = self.get_pos();
        let span = Span(start, end);
        let prag = vec![];
        Ok(DataDecl {
            span,
            prag,
            tdef,
            pred,
            vnts,
            with,
        })
    }

    fn with_clause(&mut self) -> Parsed<Option<WithClause<SpannedIdent>>> {
        use Keyword::With;
        use Lexeme::{Comma, ParenL, ParenR};
        let start = self.get_pos();
        if self.bump_on(With) {
            let mut with = vec![];
            if self.peek_on(ParenL) {
                with = self.delimited([ParenL, Comma, ParenR], Self::expect_upper)?
            } else {
                with.push(self.expect_upper()?);
            }
            let span = Span(start, self.get_pos());
            Ok(Some(WithClause {
                span,
                names: with,
                from_pragma: false,
            }))
        } else {
            Ok(None)
        }
    }

    fn function_decl(&mut self) -> Parsed<FnDecl> {
        use Keyword::Fn;
        use Lexeme::{ParenL, ParenR, Pipe};
        let start = self.get_pos();

        self.eat(Fn)?;

        let name = if self.bump_on(ParenL) {
            let name = self.expect_infix()?;
            self.eat(ParenR)?;
            name
        } else {
            self.expect_lower()?
        };

        let sign = self.ty_signature()?;
        self.ignore(Pipe);
        let mut defs = vec![self.match_arm()?];

        while self.bump_on(Pipe) {
            defs.push(self.match_arm()?);
        }
        let end = self.get_pos();
        let span = Span(start, end);
        let prag = vec![];
        Ok(FnDecl {
            span,
            prag,
            name,
            defs,
            sign,
        })
    }

    fn alias_decl(&mut self) -> Parsed<AliasDecl> {
        use Keyword::Type;
        use Lexeme::Equal;
        let start = self.get_pos();
        self.eat(Type)?;
        let ldef = self.ty_simple()?;
        self.eat(Equal)?;
        let sign = self.ty_node()?;
        let end = self.get_pos();
        let span = Span(start, end);
        let prag = vec![];
        Ok(AliasDecl {
            span,
            prag,
            ldef,
            tipo: sign,
        })
    }

    fn class_decl(&mut self) -> Parsed<ClassDecl> {
        let start = self.get_pos();
        self.eat(Keyword::Class)?;
        let pred = self.ty_predicates()?;
        let cdef = self.ty_simple()?;
        self.eat(Lexeme::CurlyL)?;
        let mut defs = vec![];
        while !self.peek_on(Lexeme::CurlyR) {
            let mut prag = self.attr_before()?;
            let start = self.get_pos();
            self.ignore(Keyword::Def);
            let name = self.binder_name()?;
            self.eat(Lexeme::Colon2)?;
            let annt = self.ty_annotation()?;
            let body = match self.peek().copied().ok_or_else(|| self.unexpected_eof())? {
                Token {
                    lexeme: Lexeme::Semi | Lexeme::Comma | Lexeme::CurlyR | Lexeme::Kw(Keyword::Def),
                    ..
                } => MethodBody::Unimplemented,
                Token {
                    lexeme: Lexeme::Equal,
                    ..
                } => {
                    self.bump();
                    let body = self.expression()?;
                    let wher = self.where_clause()?;
                    MethodBody::Default(vec![Arm {
                        args: vec![],
                        cond: None,
                        body,
                        wher,
                    }])
                }
                Token {
                    lexeme: Lexeme::Pipe,
                    ..
                } => MethodBody::Default(self.match_arms()?),
                t => {
                    return self
                        .custom_error(t, " invalid token for class method")
                        .err()
                }
            };
            let span = Span(start, self.get_pos());
            prag.extend(self.attr_after()?);

            defs.push(MethodDef {
                span,
                prag,
                name,
                annt,
                body,
            });
            self.ignore([Lexeme::Semi, Lexeme::Comma]);
        }
        self.eat(Lexeme::CurlyR)?;
        let end = self.get_pos();
        let span = Span(start, end);
        let prag = vec![];
        Ok(ClassDecl {
            span,
            prag,
            cdef,
            pred,
            defs,
        })
    }

    fn inst_decl(&mut self) -> Parsed<InstDecl> {
        let start = self.get_pos();
        self.eat(Keyword::Impl)?;
        let pred = self.ty_predicates()?;
        let name = self.expect_upper()?;
        let tipo = self.ty_atom()?;
        self.ignore([Keyword::With, Keyword::Where]);
        self.eat(Lexeme::CurlyL)?;
        let mut defs = vec![];
        while !self.peek_on(Lexeme::CurlyR) {
            defs.push(self.binding()?);
            self.ignore(Lexeme::Semi);
        }
        self.eat(Lexeme::CurlyR)?;
        let end = self.get_pos();
        let span = Span(start, end);
        let prag = vec![];
        Ok(InstDecl {
            span,
            prag,
            name,
            pred,
            defs,
            tipo,
        })
    }

    fn newtype_decl(&mut self) -> Parsed<NewtypeDecl<SpannedIdent, SpannedIdent>> {
        use Keyword::Newtype;
        use Lexeme::{CurlyL, CurlyR, Equal};
        let start = self.get_pos();
        self.eat(Newtype)?;
        let tdef = self.ty_simple()?;
        self.eat(Equal)?;
        let ctor = self.expect_upper()?;
        let narg = if self.bump_on(CurlyL) {
            let sel = self.selector()?;
            self.eat(CurlyR)?;
            TypeArg::Selector(sel)
        } else {
            let ty = self.ty_node().map(TypeArg::Type)?;
            if self.peek_on(Lexeme::begins_ty) {
                return self.current_token().and_then(|tok| {
                    self.custom_error(tok, " newtypes are allowed only a single type argument")
                        .err()
                });
            } else {
                ty
            }
        };
        let with = self.with_clause()?;
        let end = self.get_pos();
        let span = Span(start, end);
        let prag = vec![];
        Ok(NewtypeDecl {
            span,
            prag,
            tdef,
            ctor,
            narg,
            with,
        })
    }

    fn data_variants(&mut self) -> Parsed<Vec<Variant>> {
        self.many_while(
            |p| p.bump_or_peek_on(Lexeme::Pipe, Lexeme::is_upper),
            Self::data_variant,
        )
    }

    fn data_variant(&mut self) -> Parsed<Variant> {
        self.ignore(Lexeme::Pipe);
        let start = self.get_pos();
        let name = self.expect_upper()?;
        // let start = name.span().start();
        let args = if self.peek_on(Lexeme::CurlyL) {
            self.delimited(
                [Lexeme::CurlyL, Lexeme::Comma, Lexeme::CurlyR],
                Self::selector,
            )
            .map(TypeArgs::Record)?
        } else {
            self.many_while_on(Lexeme::begins_ty, Self::ty_atom)
                .map(TypeArgs::Curried)?
        };
        let span = Span(start, self.get_pos());
        let prag = vec![];
        Ok(Variant {
            name,
            span,
            prag,
            args,
        })
    }

    fn selector(&mut self) -> Parsed<Selector> {
        let name = self.binder_name()?;
        self.eat(Lexeme::Colon2)?;
        let tipo = self.ty_node()?;
        Ok(Selector { name, tipo })
    }
}

#[cfg(test)]
mod test {
    use wy_common::functor::{Func, MapFst, MapSnd};
    use wy_failure::diff::diff_assert_eq;
    use wy_intern::Symbol;
    use wy_lexer::Literal;
    use wy_name::Ident;
    use wy_syntax::{
        expr::Expression,
        pattern::Pattern,
        record::{Field, Record},
        stmt::{Arm, Binding},
        tipo::{Con, Parameter, Predicate, Signature, SimpleType, Type},
    };

    use super::*;

    #[test]
    fn inspect_data_decl_variant_spans() {
        let src =
            "data Foo a b = Foo a b | Bar a (Foo a b) | Baz { foo_a :: a, foo_b :: b } with Eq";
        let data_decl = Parser::from_str(src).data_decl().unwrap();
        println!("src[data_decl.span] = `{}`", &src[data_decl.span.range()]);
        data_decl
            .variants_iter()
            .enumerate()
            .for_each(|(n, vnt)| println!("src[(variant {n}).span] = `{}`", &src[vnt.span.range()]))
    }

    #[test]
    fn test_data_decl() {
        let src =
            "data Foo a b = Foo a b | Bar a (Foo a b) | Baz { foo_a :: a, foo_b :: b } with Eq";
        let spans = {
            let base = BytePos::strlen("data Foo a b = ");
            let sep = BytePos::strlen("| ");
            let dx0 = BytePos::strlen("Foo a b ");
            let dx1 = BytePos::strlen("Bar a (Foo a b) ");
            let dx2 = BytePos::strlen("Baz { foo_a :: a, foo_b :: b }");
            let span_1 = Span(base, base + dx0);
            let span_2 = Span(span_1.end() + sep, span_1.end() + sep + dx1);
            let span_3 = Span(span_2.end() + sep, span_2.end() + sep + dx2);
            [span_1, span_2, span_3]
        };
        let decl = Parser::from_str(src)
            .data_decl()
            .map(|ty| {
                ty.map_fst(&mut Func::New(Spanned::take_item))
                    .map_snd(&mut Func::New(Spanned::take_item))
            })
            .unwrap();
        let [a, b, foo_a, foo_b] =
            Symbol::intern_many_with(["a", "b", "foo_a", "foo_b"], Ident::Lower);
        let [foo, bar, baz, eq] =
            Symbol::intern_many_with(["Foo", "Bar", "Baz", "Eq"], Ident::Upper);
        let expected = {
            DataDecl {
                span: Span::of_str(src),
                prag: vec![],
                tdef: SimpleType(foo, vec![a, b]),
                pred: vec![],
                vnts: vec![
                    Variant {
                        name: foo,
                        span: spans[0],
                        prag: vec![],
                        args: TypeArgs::Curried(vec![Type::Var(a), Type::Var(b)]),
                    },
                    Variant {
                        name: bar,
                        span: spans[1],
                        prag: vec![],
                        args: TypeArgs::Curried(vec![
                            Type::Var(a),
                            Type::Con(Con::Named(foo), vec![Type::Var(a), Type::Var(b)]),
                        ]),
                    },
                    Variant {
                        name: baz,
                        span: spans[2],
                        prag: vec![],
                        args: TypeArgs::Record(vec![
                            Selector {
                                name: foo_a,
                                tipo: Type::Var(a),
                            },
                            Selector {
                                name: foo_b,
                                tipo: Type::Var(b),
                            },
                        ]),
                    },
                ],
                with: {
                    let start_pos = BytePos::strlen("data Foo a b = Foo a b | Bar a (Foo a b) | Baz { foo_a :: a, foo_b :: b } ");
                    let pos_diff = BytePos::strlen("with Eq");
                    Some(WithClause {
                        span: Span(start_pos, start_pos + pos_diff),
                        names: vec![eq],
                        from_pragma: false,
                    })
                },
            }
        };
        diff_assert_eq!(decl, expected)
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
        let [a, x, xs, y, ys] = Symbol::intern_many_with(["a", "x", "xs", "y", "ys"], Ident::Lower);
        let [cl_eq, con_true, con_false] =
            Symbol::intern_many_with(["Eq", "True", "False"], Ident::Upper);
        let [eq2, amper2] = Symbol::intern_many_with(["==", "&&"], Ident::Infix);
        let actual = Parser::from_str(src)
            .inst_decl()
            .map(|ty| {
                ty.map_fst(&mut Func::New(Spanned::take_item))
                    .map_snd(&mut Func::New(Spanned::take_item))
            })
            .unwrap();
        let expected = {
            InstDecl {
                span: Span::of_str(src.trim_end()),
                prag: vec![],
                name: cl_eq,
                tipo: Type::Vec(Box::new(Type::Var(a))),
                pred: vec![Predicate {
                    class: cl_eq,
                    head: Parameter(a, vec![]),
                }],
                defs: vec![Binding {
                    name: eq2,
                    tsig: Signature::Implicit,
                    arms: vec![
                        Arm {
                            args: vec![Pattern::NULL, Pattern::NULL],
                            cond: None,
                            body: Expression::Ident(con_true),
                            wher: vec![],
                        },
                        Arm {
                            args: vec![
                                Pattern::Lnk(Box::new(Pattern::Var(x)), Box::new(Pattern::Var(xs))),
                                Pattern::Lnk(Box::new(Pattern::Var(y)), Box::new(Pattern::Var(ys))),
                            ],
                            cond: None,
                            body: Expression::Infix {
                                infix: amper2,
                                left: Box::new(Expression::Group(Box::new(Expression::Infix {
                                    infix: eq2,
                                    left: Box::new(Expression::Ident(x)),
                                    right: Box::new(Expression::Ident(y)),
                                }))),
                                right: Box::new(Expression::Group(Box::new(Expression::Infix {
                                    infix: eq2,
                                    left: Box::new(Expression::Ident(xs)),
                                    right: Box::new(Expression::Ident(ys)),
                                }))),
                            },
                            wher: vec![],
                        },
                        Arm {
                            args: vec![Pattern::Wild, Pattern::Wild],
                            cond: None,
                            body: Expression::Ident(con_false),
                            wher: vec![],
                        },
                    ],
                }],
            }
        };
        diff_assert_eq!(actual, expected)
    }

    #[test]
    fn test_newtype_decl() {
        let src = r#"newtype Parser a = Parser { parse :: String -> (a, String) }"#;
        let parsed = Parser::from_str(src)
            .newtype_decl()
            .map(|ty| {
                ty.map_fst(&mut Func::New(Spanned::take_item))
                    .map_snd(&mut Func::New(Spanned::take_item))
            })
            .unwrap();
        let [parser_ty, a, parse, string_ty] =
            Symbol::intern_many(["Parser", "a", "parse", "String"]);
        let expected = NewtypeDecl {
            span: Span::of_str(src),
            prag: vec![],
            tdef: SimpleType(Ident::Upper(parser_ty), vec![Ident::Lower(a)]),
            ctor: Ident::Upper(parser_ty),
            narg: TypeArg::Selector(Selector {
                name: Ident::Lower(parse),
                tipo: Type::mk_fun(
                    Type::Con(Con::Named(Ident::Upper(string_ty)), vec![]),
                    Type::Tup(vec![
                        Type::Var(Ident::Lower(a)),
                        Type::Con(Con::Named(Ident::Upper(string_ty)), vec![]),
                    ]),
                ),
            }),
            with: None,
        };
        assert_eq!(parsed, expected)
    }

    #[test]
    fn test_caf() {
        let tests = ["fn womp :: |Num a| a =   3", "fn womp :: |Num a| a | = 3"]
            .into_iter()
            .map(|s| Parser::from_str(s).function_decl().unwrap())
            .collect::<Vec<_>>();
        diff_assert_eq!(tests[0], tests[1]);
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
    fn test_record_fn() {
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
        let [a, b, c, some_record_function] =
            Symbol::intern_many_with(["a", "b", "c", "some_record_function"], Ident::Lower);
        let [con_a] = Symbol::intern_many_with(["A"], Ident::Upper);
        let [plus] = Symbol::intern_many_with(["+"], Ident::Infix);
        let mkint = Literal::simple_int;
        let actual = Parser::from_str(src)
            .function_decl()
            .map(|ty| {
                ty.map_fst(&mut Func::New(Spanned::take_item))
                    .map_snd(&mut Func::New(Spanned::take_item))
            })
            .unwrap();
        let expected = FnDecl {
            span: Span::of_str(src),
            prag: vec![],
            name: some_record_function,
            sign: Signature::Implicit,
            defs: vec![
                Arm {
                    args: vec![Pattern::At(
                        a,
                        Box::new(Pattern::Rec(Record::Data(
                            con_a,
                            vec![Field::Key(b), Field::Key(c)],
                        ))),
                    )],
                    cond: None,
                    body: Expression::Dict(Record::Data(
                        a,
                        vec![
                            Field::Entry(
                                b,
                                Expression::Infix {
                                    infix: plus,
                                    left: Box::new(Expression::Ident(b)),
                                    right: Box::new(Expression::Lit(mkint(2))),
                                },
                            ),
                            Field::Entry(
                                c,
                                Expression::App(
                                    Box::new(Expression::App(
                                        Box::new(Expression::Ident(c)),
                                        Box::new(Expression::Ident(a)),
                                    )),
                                    Box::new(Expression::Lit(mkint(3))),
                                ),
                            ),
                        ],
                    )),
                    wher: vec![],
                },
                Arm {
                    args: vec![Pattern::At(
                        a,
                        Box::new(Pattern::Rec(Record::Data(
                            con_a,
                            vec![
                                Field::Entry(
                                    b,
                                    Pattern::Or(vec![
                                        Pattern::Lit(mkint(1)),
                                        Pattern::Lit(mkint(2)),
                                    ]),
                                ),
                                Field::Key(c),
                            ],
                        ))),
                    )],
                    cond: None,
                    body: Expression::Dict(Record::Data(
                        a,
                        vec![
                            Field::Key(b),
                            Field::Entry(
                                c,
                                Expression::App(
                                    Box::new(Expression::App(
                                        Box::new(Expression::Ident(c)),
                                        Box::new(Expression::Ident(a)),
                                    )),
                                    Box::new(Expression::Lit(mkint(3))),
                                ),
                            ),
                        ],
                    )),
                    wher: vec![],
                },
            ],
        };
        assert_eq!(actual, expected)
    }

    #[test]
    fn this_shouldnt_fail() {
        let src = r#"
class Functor f {
    map :: (a -> b) -> f a -> f b;
    (/>) :: b -> f a -> f b
        = map \> const
    }
"#;
        println!("{:?}", Parser::from_str(src).declaration())
    }
}
