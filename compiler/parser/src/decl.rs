use crate::error::*;
use crate::stream::*;

use wy_lexer::lexpat;
use wy_lexer::meta::Placement;
use wy_lexer::token::*;
use wy_name::ident::Ident;
use wy_syntax::attr::Attribute;
use wy_syntax::decl::{
    AliasDecl, Arity, ClassDecl, DataDecl, Declaration, FixityDecl, FnDecl, InstDecl, Method,
    MethodDef, NewtypeArg, NewtypeDecl, Tag, Variant,
};
use wy_syntax::fixity::Fixity;
use wy_syntax::stmt::RawBinding;

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
            lexpat!(~[#]) => self.attribute().map(D::Attribute),
            _ => Err(self.expected(LexKind::Keyword)),
        }
    }

    fn attribute(&mut self) -> Parsed<Attribute<Ident, Ident>> {
        self.eat(Lexeme::Pound)?;
        let _bang = self.bump_on(Lexeme::Bang);
        let is_after = self.lexer.get_mode().is_meta_after();
        self.eat(Lexeme::BrackL)?;
        let _attr = match self.bump() {
            Token {
                lexeme: Lexeme::Meta(pragma),
                span: _,
            } => {
                let pl = if is_after {
                    Placement::After
                } else {
                    Placement::Before
                };
                self.pragmas.push((pragma, pl));
                Ok(())
            }
            t @ Token {
                lexeme: Lexeme::Unknown(_lex),
                span: _,
            } => Err(ParseError::InvalidLexeme(
                self.get_srcloc(),
                t,
                self.get_source(),
            )),
            Token {
                lexeme: Lexeme::Eof,
                span: _,
            } => Err(ParseError::UnexpectedEof(
                self.get_srcloc(),
                self.get_source(),
            )),
            t => Err(self.expected(LexKind::from(t.lexeme))),
        }?;
        self.eat(Lexeme::BrackR)?;
        self.lexer.reset_mode();
        todo!()
    }

    fn fixity_decl(&mut self) -> Parsed<FixityDecl> {
        let assoc = self.fixity_assoc()?;
        let prec = self.fixity_prec()?;
        let fixity = Fixity { prec, assoc };
        let infixes = self.with_fixity(fixity)?;
        Ok(FixityDecl { infixes, fixity })
    }

    fn data_decl(&mut self) -> Parsed<DataDecl<Ident, Ident>> {
        use Keyword::{Data, With};
        use Lexeme::{Comma, Equal, Kw, ParenL, ParenR, Pipe, Semi};

        self.eat(Kw(Data))?;

        let ctxt = if self.peek_on(Pipe) {
            self.delimited([Pipe, Comma, Pipe], Self::ty_constraint)?
        } else {
            vec![]
        };
        let name = self.expect_upper()?;
        let poly = self.many_while_on(Not([Equal, Semi]), |p| p.expect_lower())?;
        let mut decl = DataDecl {
            name,
            ctxt,
            poly,
            vnts: vec![],
            with: vec![],
        };

        if self.peek_on(Semi) {
            return Ok(decl);
        }

        self.eat(Equal)?;

        decl.vnts = self.many_while(
            |p| p.bump_on(Pipe) || p.peek_on(Lexeme::is_upper),
            Self::data_variant,
        )?;

        if self.bump_on(Kw(With)) {
            decl.with = if self.peek_on(ParenL) {
                self.delimited([ParenL, Comma, ParenR], Self::expect_upper)?
            } else {
                vec![self.expect_upper()?]
            }
        };

        Ok(decl.enumer_tags())
    }

    fn function_decl(&mut self) -> Parsed<FnDecl> {
        use Keyword::Fn;
        use Lexeme::{Colon2, ParenL, ParenR, Pipe};

        self.eat(Fn)?;

        let name = if self.bump_on(ParenL) {
            let name = self.expect_infix()?;
            self.eat(ParenR)?;
            name
        } else {
            self.expect_lower()?
        };

        let sign = if self.bump_on(Colon2) {
            self.total_signature().map(Some)?
        } else {
            None
        };

        self.ignore(Pipe);

        let mut defs = vec![self.match_arm()?];

        while self.bump_on(Pipe) {
            defs.push(self.match_arm()?);
        }

        Ok(FnDecl { name, defs, sign })
    }

    fn alias_decl(&mut self) -> Parsed<AliasDecl> {
        use Keyword::Type;
        use Lexeme::Equal;
        self.eat(Type)?;
        let name = self.expect_upper()?;
        let poly = self.many_while_on(Not(Equal), |p| p.expect_lower())?;
        self.eat(Equal)?;
        let sign = self.total_signature()?;
        Ok(AliasDecl { name, poly, sign })
    }

    fn class_decl(&mut self) -> Parsed<ClassDecl> {
        self.eat(Keyword::Class)?;
        let ctxt = self.ty_contexts()?;
        let name = self.expect_upper()?;
        let poly = self.many_while_on(Lexeme::is_lower, |p| p.expect_lower())?;
        self.eat(Lexeme::CurlyL)?;
        let mut defs = vec![];
        while !self.peek_on(Lexeme::CurlyR) {
            self.ignore(Keyword::Def);
            if let RawBinding {
                name,
                arms,
                tipo: Some(sign),
            } = self.binding()?
            {
                defs.push(MethodDef {
                    name,
                    sign,
                    body: arms,
                })
            } else {
                return Err(self.custom_error("class method definition without type signature"));
            };
            self.ignore(Lexeme::Semi);
        }
        self.eat(Lexeme::CurlyR)?;
        Ok(ClassDecl {
            name,
            poly,
            ctxt,
            defs,
        })
    }

    #[allow(unused)]
    fn method_signature(&mut self) -> Parsed<Method> {
        self.eat(Lexeme::Kw(Keyword::Def))?;
        let name = self.binder_name()?;
        self.eat(Lexeme::Colon2)?;
        let tipo = self.total_signature()?;
        Ok(Method::Sig(name, tipo))
    }

    fn inst_decl(&mut self) -> Parsed<InstDecl> {
        self.eat(Keyword::Impl)?;
        let ctxt = self.ty_contexts()?;
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
        Ok(InstDecl {
            name,
            ctxt,
            defs,
            tipo,
        })
    }

    fn newtype_decl(&mut self) -> Parsed<NewtypeDecl> {
        use Keyword::{Newtype, With};
        use Lexeme::{Colon2, Comma, CurlyL, CurlyR, Equal, ParenL, ParenR};

        fn until_semi_kw(parser: &mut Parser) -> bool {
            !lexpat!(parser on [;] | [kw])
        }

        self.eat(Newtype)?;
        let name = self.expect_upper()?;
        let poly = self.many_while_on(Lexeme::is_lower, Self::expect_lower)?;
        self.eat(Equal)?;
        let ctor = self.expect_upper()?;
        let narg = if self.bump_on(CurlyL) {
            let label = self.expect_lower()?;
            self.eat(Colon2)?;
            let tysig = self.total_signature()?;
            self.eat(CurlyR)?;
            NewtypeArg::Record(label, tysig)
        } else {
            self.many_while(until_semi_kw, Self::ty_node)
                .map(NewtypeArg::Stacked)?
        };
        let with = if self.bump_on(With) {
            if self.peek_on(ParenL) {
                self.delimited([ParenL, Comma, ParenR], Self::expect_upper)?
            } else {
                vec![self.expect_upper()?]
            }
        } else {
            vec![]
        };
        Ok(NewtypeDecl {
            name,
            poly,
            ctor,
            narg,
            with,
        })
    }

    fn data_variant(&mut self) -> Parsed<Variant> {
        self.ignore(Lexeme::Pipe);
        // constructor name
        let name = self.expect_upper()?;
        let mut args = vec![];
        while !(self.is_done() || lexpat!(self on [;] | [|] | [kw])) {
            args.push(if lexpat!(self on [curlyL]) {
                self.curly_ty()
            } else {
                self.ty_atom()
            }?);
        }
        let arity = Arity::new(args.len());
        Ok(Variant {
            name,
            args,
            arity,
            tag: Tag(0),
        })
    }
}

#[cfg(test)]
mod test {
    use wy_syntax::tipo::{Con, Signature, Type};

    use super::*;

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
    fn test_newtype_decl() {
        let src = r#"newtype Parser a = Parser { parse :: String -> (a, String) }"#;
        let parsed = Parser::from_str(src).newtype_decl().unwrap();
        let [parser_ty, a, parse, string_ty] =
            wy_intern::intern_many(["Parser", "a", "parse", "String"]);
        let expected = NewtypeDecl {
            name: Ident::Upper(parser_ty),
            poly: vec![Ident::Lower(a)],
            ctor: Ident::Upper(parser_ty),
            narg: NewtypeArg::Record(
                Ident::Lower(parse),
                Signature {
                    each: vec![],
                    ctxt: vec![],
                    tipo: Type::mk_fun(
                        Type::Con(Con::Data(Ident::Upper(string_ty)), vec![]),
                        Type::Tup(vec![
                            Type::Var(Ident::Lower(a)),
                            Type::Con(Con::Data(Ident::Upper(string_ty)), vec![]),
                        ]),
                    ),
                },
            ),
            with: vec![],
        };
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
}
