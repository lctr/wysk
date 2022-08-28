use crate::error::*;
use crate::stream::*;

use wy_lexer::lexpat;
use wy_lexer::token::*;

use wy_syntax::decl::MethodBody;
use wy_syntax::decl::MethodImpl;
use wy_syntax::decl::Selector;
use wy_syntax::decl::TypeArgs;
use wy_syntax::decl::Vis;
use wy_syntax::decl::WithClause;
use wy_syntax::decl::{
    AliasDecl, ClassDecl, DataDecl, Declaration, FixityDecl, FnDecl, InstDecl, MethodDef,
    NewtypeDecl, TypeArg, Variant,
};
use wy_syntax::fixity::Fixity;
use wy_syntax::stmt::Arm;
use wy_syntax::stmt::Binding;
use wy_syntax::SpannedIdent;

type DeclParser<'t> = Parser<'t>;
// DECLARATIONS
impl<'t> DeclParser<'t> {
    pub fn declaration(&mut self) -> Parsed<Declaration> {
        use Declaration as D;
        let pos = self.get_pos();
        let vis = self.visibility()?;

        match self.peek() {
            lexpat!(~[import]) => self.reject_decl_vis((vis, pos), Self::import_spec),
            lexpat!(maybe[infixl][infixr][infix]) => {
                self.reject_decl_vis((vis, pos), Self::fixity_decl)
            }
            lexpat!(~[data]) => self.data_decl(vis).map(D::Data),
            lexpat!(~[fn]) => self.function_decl(vis).map(D::Function),
            lexpat!(~[type]) => self.alias_decl(vis).map(D::Alias),
            lexpat!(~[class]) => self.class_decl(vis).map(D::Class),
            lexpat!(~[impl]) => self.reject_decl_vis((vis, pos), Self::inst_decl),
            lexpat!(~[newtype]) => self.newtype_decl(vis).map(D::Newtype),
            Some(t) => Err({
                let t = *t;
                self.expected(LexKind::Keyword, t)
            }),
            _ => self.unexpected_eof().err(),
        }
    }

    pub(crate) fn visibility(&mut self) -> Parsed<Vis> {
        if self.bump_on(Keyword::Pub) {
            Ok(Vis::Public)
        } else {
            Ok(Vis::Private)
        }
    }

    fn reject_decl_vis<A, B, X>(
        &mut self,
        (vis, pos): (Vis, wy_span::BytePos),
        mut f: impl FnMut(&mut Self) -> Parsed<X>,
    ) -> Parsed<Declaration<A, B>>
    where
        Declaration<A, B>: From<X>,
    {
        if vis.is_public() {
            let kw_token = self.current_token()?;
            self.unsupported_vis_modifier(pos, kw_token).err()
        } else {
            f(self).map(Declaration::from)
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

    fn data_decl(&mut self, visi: Vis) -> Parsed<DataDecl> {
        use Keyword::Data;
        use Lexeme::{Equal, Semi};
        let mut prag = self.attr_before()?;
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
        prag.extend(self.attr_after()?);
        Ok(DataDecl {
            visi,
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
        fn derives(p: &mut Parser) -> Parsed<(SpannedIdent, bool)> {
            p.expect_upper().map(|id| (id, false))
        }
        let start = self.get_pos();
        if self.bump_on(With) {
            let mut names = vec![];
            if self.peek_on(ParenL) {
                names = self.delimited([ParenL, Comma, ParenR], derives)?
            } else {
                names.push(derives(self)?);
            }
            let span = Span(start, self.get_pos());
            Ok(Some(WithClause { span, names }))
        } else {
            Ok(None)
        }
    }

    fn function_decl(&mut self, visi: Vis) -> Parsed<FnDecl> {
        use Keyword::Fn;
        use Lexeme::Pipe;
        let mut prag = self.attr_before()?;
        let start = self.get_pos();
        self.eat(Fn)?;
        let name = self.binder_name()?;
        let sign = self.ty_signature()?;
        self.ignore(Pipe);
        let mut defs = vec![self.match_arm()?];
        while self.bump_on(Pipe) {
            defs.push(self.match_arm()?);
        }
        let span = Span(start, self.get_pos());
        prag.extend(self.attr_after()?);
        Ok(FnDecl {
            visi,
            span,
            prag,
            name,
            defs,
            sign,
        })
    }

    fn alias_decl(&mut self, visi: Vis) -> Parsed<AliasDecl> {
        use Keyword::Type;
        use Lexeme::Equal;
        let mut prag = self.attr_before()?;
        let start = self.get_pos();
        self.eat(Type)?;
        let ldef = self.ty_simple()?;
        self.eat(Equal)?;
        let tipo = self.ty_node()?;
        let span = Span(start, self.get_pos());
        prag.extend(self.attr_after()?);
        Ok(AliasDecl {
            visi,
            span,
            prag,
            ldef,
            tipo,
        })
    }

    fn class_decl(&mut self, visi: Vis) -> Parsed<ClassDecl> {
        let mut prag = self.attr_before()?;
        let start = self.get_pos();
        self.eat(Keyword::Class)?;
        let pred = self.ty_predicates()?;
        let cdef = self.ty_simple()?;
        self.eat(Lexeme::CurlyL)?;
        prag.extend(self.attr_after()?);
        let mut defs = vec![];
        while !self.peek_on(Lexeme::CurlyR) {
            defs.push(self.method_def()?);
            self.ignore(Lexeme::Semi);
        }
        self.eat(Lexeme::CurlyR)?;
        let span = Span(start, self.get_pos());
        Ok(ClassDecl {
            visi,
            span,
            prag,
            cdef,
            pred,
            defs,
        })
    }

    fn method_def(&mut self) -> Parsed<MethodDef> {
        let mut prag = self.attr_before()?;
        let start = self.get_pos();
        self.ignore(Keyword::Fn);
        prag.extend(self.attr_before()?);
        let name = self.binder_name()?;
        self.eat(Lexeme::Colon2)?;
        let annt = self.ty_annotation()?;
        let body = self.method_body()?;
        let span = Span(start, self.get_pos());
        prag.extend(self.attr_after()?);
        Ok(MethodDef {
            span,
            prag,
            name,
            annt,
            body,
        })
    }

    fn method_body(&mut self) -> Parsed<MethodBody> {
        match self.current_token()? {
            Token {
                lexeme:
                    Lexeme::Semi
                    | Lexeme::Comma
                    | Lexeme::CurlyR
                    | Lexeme::Pound
                    | Lexeme::Hashbang
                    | Lexeme::Kw(Keyword::Fn),
                ..
            } => Ok(MethodBody::Unimplemented),
            Token {
                lexeme: Lexeme::Equal,
                ..
            } => {
                self.bump();
                let (body, wher) = self.binding_rhs()?;
                Ok(MethodBody::Default(vec![Arm {
                    args: vec![],
                    cond: None,
                    body,
                    wher,
                }]))
            }
            Token {
                lexeme: Lexeme::Pipe,
                ..
            } => Ok(MethodBody::Default(self.match_arms()?)),
            t => return self.invalid_fn_ident(t).err(),
        }
    }

    fn inst_decl(&mut self) -> Parsed<InstDecl> {
        let mut prag = self.attr_before()?;
        let start = self.get_pos();
        self.eat(Keyword::Impl)?;
        let pred = self.ty_predicates()?;
        let name = self.expect_upper()?;
        let tipo = self.ty_atom()?;
        self.eat(Lexeme::CurlyL)?;
        prag.extend(self.attr_after()?);
        let mut defs = vec![];
        while !self.peek_on(Lexeme::CurlyR) {
            defs.push(self.method_impl()?);
            self.ignore(Lexeme::Semi);
        }
        self.eat(Lexeme::CurlyR)?;
        let span = Span(start, self.get_pos());
        Ok(InstDecl {
            span,
            prag,
            name,
            pred,
            defs,
            tipo,
        })
    }

    fn method_impl(&mut self) -> Parsed<MethodImpl> {
        let mut prag = self.attr_before()?;
        let start = self.get_pos();
        self.ignore(Keyword::Fn);
        prag.extend(self.attr_before()?);
        let Binding { name, arms, tsig } = self.binding()?;
        let span = Span(start, self.get_pos());
        prag.extend(self.attr_after()?);
        Ok(MethodImpl {
            span,
            prag,
            name,
            tsig,
            arms,
        })
    }

    fn newtype_decl(&mut self, visi: Vis) -> Parsed<NewtypeDecl<SpannedIdent, SpannedIdent>> {
        use Keyword::Newtype;
        use Lexeme::{CurlyL, CurlyR, Equal};
        let mut prag = self.attr_before()?;
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
        prag.extend(self.attr_after()?);
        Ok(NewtypeDecl {
            visi,
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
        let mut prag = self.attr_before()?;
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
        prag.extend(self.attr_after()?);
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
        decl::MethodImpl,
        expr::Expression,
        pattern::Pattern,
        record::{Field, Record},
        stmt::Arm,
        tipo::{Con, Parameter, Predicate, Signature, SimpleType, Type},
    };

    use super::*;

    #[test]
    fn inspect_data_decl_variant_spans() {
        let src =
            "data Foo a b = Foo a b | Bar a (Foo a b) | Baz { foo_a :: a, foo_b :: b } with Eq";
        let data_decl = Parser::from_str(src).data_decl(Default::default()).unwrap();
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
            .data_decl(Default::default())
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
                visi: Default::default(),
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
                        names: vec![(eq, false)],
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
                span: Span(BytePos(1), BytePos::strlen(src.trim_end())),
                prag: vec![],
                name: cl_eq,
                tipo: Type::Vec(Box::new(Type::Var(a))),
                pred: vec![Predicate {
                    class: cl_eq,
                    head: Parameter(a, vec![]),
                }],
                defs: vec![MethodImpl {
                    span: Span(
                        BytePos::strlen(
                            r#"
impl |Eq a| Eq [a] {
    "#,
                        ),
                        BytePos::strlen(
                            r#"impl |Eq a| Eq [a] {
    (==)
    | [] [] = True
    | (x:xs) (y:ys) = (x == y) && (xs == ys)
    | _ _ = False
}"#,
                        ),
                    ),
                    name: eq2,
                    prag: vec![],
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
            .newtype_decl(Default::default())
            .map(|ty| {
                ty.map_fst(&mut Func::New(Spanned::take_item))
                    .map_snd(&mut Func::New(Spanned::take_item))
            })
            .unwrap();
        let [parser_ty, a, parse, string_ty] =
            Symbol::intern_many(["Parser", "a", "parse", "String"]);
        let expected = NewtypeDecl {
            visi: Default::default(),
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
            .map(|s| {
                Parser::from_str(s)
                    .function_decl(Default::default())
                    .unwrap()
            })
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
        let expr = parser.data_decl(Default::default());
        match expr {
            Ok(decl) => println!("{:?}", decl),
            Err(e) => println!("{}", e),
        }
    }

    #[test]
    fn test_record_fn() {
        let src = r#"
fn some_record_function
    | a @ A { b, c } = a {
        b = b + 2,
        c = c a 3
    }
    | a @ A { b = (1 | 2), c } = a {
        b,
        c = c a 3
    }
"#;
        let [a, b, c, some_record_function] =
            Symbol::intern_many_with(["a", "b", "c", "some_record_function"], Ident::Lower);
        let [con_a] = Symbol::intern_many_with(["A"], Ident::Upper);
        let [plus] = Symbol::intern_many_with(["+"], Ident::Infix);
        let mkint = Literal::simple_int;
        let actual = Parser::from_str(src)
            .function_decl(Default::default())
            .map(|ty| {
                ty.map_fst(&mut Func::New(Spanned::take_item))
                    .map_snd(&mut Func::New(Spanned::take_item))
            })
            .unwrap();
        let expected = FnDecl {
            visi: Default::default(),
            span: Span(BytePos(1), BytePos::strlen(src)),
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
        diff_assert_eq!(actual, expected)
    }

    #[test]
    fn test_inline_attr_in_class_method() {
        let src = "
class |Semigroup a| Monoid a {
    ~~> The identity element of the associative monoidal append operation `<>`
    ~~| inherited from the `Semigroup` superclass.
    ~~|
    ~~| The equality `x <> mempty == mempty <> x == x` should hold.
    mempty :: a;

    ~~ inline attribute/pragma in hopes of fusing with mconcat's argument
    #[inline]
    ~~> Fold a list using the monoid.
    mconcat :: [a] -> a
        = foldr mappend mempty;
    }
";
        let mut parser = Parser::from_str(src);
        println!("{:?}", parser.class_decl(Default::default()));
        println!("{:?}", &parser)
    }
}
