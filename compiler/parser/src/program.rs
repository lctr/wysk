use wy_lexer::{Keyword, Lexeme};
use wy_name::{Chain, Ident};

use wy_span::Spanned;

use wy_syntax::{Import, ImportSpec, Module, Program, SpannedIdent};

use crate::error::*;
use crate::stream::*;

pub type RawModule<P = SrcPath> = Module<Ident, Ident, P>;
pub type RawProgram<P = SrcPath> = Program<Ident, Ident, P>;

// TOP-LEVEL
type ModuleParser<'t> = Parser<'t>;
impl<'t> ModuleParser<'t> {
    pub fn id_chain(&mut self) -> Parsed<Chain<SpannedIdent>> {
        self.expect_upper().and_then(|root| {
            self.many_while(|p| p.bump_on(Lexeme::Dot), Self::expect_ident)
                .map(|tail| Chain::new(root, tail.into()))
        })
    }

    pub fn module(&mut self) -> Parsed<RawModule> {
        self.eat(Keyword::Module)?;
        let modname = self.id_chain()?.map(Spanned::take_item);
        self.eat(Keyword::Where)?;
        let doc_comments = self.module_doc_comments();
        let imports = self.imports()?;
        let mut module = Module {
            modname,
            imports,
            srcpath: self.path.clone(),
            pragmas: doc_comments,
            ..Default::default()
        };

        self.populate_module(&mut module)?;
        Ok(module)
    }

    fn populate_module(&mut self, module: &mut RawModule) -> Parsed<()> {
        while !self.is_done() {
            let mut pragmas = self.attr_before()?;
            let mut decl = self.declaration()?;
            pragmas.extend(self.attr_after()?);
            decl.extend_pragmas(pragmas);
            module.push_decl(decl);
            self.ignore(Lexeme::Semi)
        }
        Ok(())
    }

    fn imports(&mut self) -> Parsed<Vec<ImportSpec>> {
        use Keyword::Import;
        use Lexeme::{Kw, Pipe};
        self.many_while(|p| p.bump_on([Kw(Import), Pipe]), Self::import_spec)
    }

    fn import_spec(&mut self) -> Parsed<ImportSpec> {
        use Keyword::{Hiding, Qualified};
        use Lexeme::{At, Comma, CurlyL, CurlyR};

        Ok(ImportSpec {
            qualified: self.bump_on(Qualified),
            name: self.id_chain()?,
            rename: if self.bump_on(At) {
                Some(self.expect_upper()?)
            } else {
                None
            },
            hidden: self.bump_on(Hiding),
            imports: if self.peek_on(CurlyL) {
                self.delimited([CurlyL, Comma, CurlyR], Self::import_item)?
            } else {
                Vec::new()
            },
        })
    }

    fn import_item(&mut self) -> Parsed<Import> {
        use Import as I;
        use Lexeme as L;

        match self.peek() {
            Some(t) if t.is_ident() => self.expect_lower().map(I::Function),
            Some(t) if t.is_infix() => self.expect_infix().map(I::Operator),
            Some(t) if t.is_paren_l() => {
                self.eat(L::ParenL)?;
                let infix = self.expect_infix()?;
                self.eat(L::ParenR)?;
                Ok(I::Operator(infix))
            }
            Some(t) if t.is_upper() => {
                let first = self.expect_upper()?;
                if self.bump_on(L::ParenL) {
                    if self.bump_on(L::Dot2) {
                        self.eat(L::ParenR)?;
                        return Ok(I::Total(first));
                    }

                    let ctors = self
                        .many_while_on(L::is_ident, |p| p.trailing(L::Comma, Self::expect_ident))?;

                    self.eat(L::ParenR)?;
                    Ok(I::Partial(first, ctors))
                } else {
                    Ok(I::Abstract(first))
                }
            }
            _ => self
                .current_token()
                .and_then(|tok| self.custom_error(tok, " is not a valid import").err()),
        }
    }

    pub fn parse_program(mut self) -> ParseResult<RawProgram> {
        use Keyword as K;
        use Module as M;
        let module = if self.peek_on(K::Module) {
            self.module()
        } else {
            Ok(M::default())
        }
        .map_err(|e| self.errors.push(e))
        .and_then(|mut module| {
            self.many_while_on(K::Import, Self::import_spec)
                .map_err(|e| self.errors.push(e))
                .and_then(|imports| {
                    module.imports = imports;
                    self.populate_module(&mut module)
                        .map(|_| module)
                        .map_err(|e| self.errors.push(e))
                })
        })
        .map_err(|_| self.text());
        let Parser {
            fixities,
            lexer,
            path,
            errors,
            ..
        } = self;
        match module {
            Ok(module) => Ok(Program {
                module,
                fixities: fixities.as_fixities(),
                comments: lexer.comments,
            }),
            Err(source) => Err(ParseFailure {
                srcpath: path,
                source,
                errors,
            }),
        }
    }
}

#[cfg(test)]
mod test {

    use wy_intern::Symbol;
    use wy_name::ident::Ident;

    use super::*;

    #[test]
    fn parse_imports() {
        let src = r#"
import A.thing.from.Somewhere @ A { foo, bar }
| B.things.elsewhere @ B { baz }
"#;
        let program = Parser::from_str(src).imports();
        let [a_con, thing, from, somewhere_con, foo, bar, b_con, things, elsewhere, baz] =
            Symbol::intern_many([
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
        assert_eq!(expected, program.unwrap())
    }

    #[test]
    fn parse_prelude_module() {
        let src = include_str!("../../../language/prelude/src/lib.wy");
        let result = Parser::new(src, "../../../language/prelude/src/lib.wy").parse_program();
        // let dcons = result.as_ref().map(|prog| prog.module.data_ctors());
        match result {
            Ok(program) => {
                println!("showing prim.wy: {:#?}", program.module)
            }
            Err(err) => {
                println!("{}", err)
            }
        };
    }
}
