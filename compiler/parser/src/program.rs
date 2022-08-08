use wy_lexer::{Keyword, Lexeme};
use wy_name::{Chain, Ident};

use wy_syntax::decl::Declaration;
use wy_syntax::{Import, ImportSpec, Module, Program};

use crate::error::*;
use crate::stream::*;

pub type RawModule<P = SrcPath> = Module<Ident, P, Ident>;
pub type RawProgram<P = SrcPath> = Program<Ident, P, Ident>;

// TOP-LEVEL
type ModuleParser<'t> = Parser<'t>;
impl<'t> ModuleParser<'t> {
    pub fn id_chain(&mut self) -> Parsed<Chain> {
        self.expect_upper().and_then(|root| {
            self.many_while(|p| p.bump_on(Lexeme::Dot), Self::expect_ident)
                .map(|tail| Chain::new(root, tail.into()))
        })
    }

    pub fn module(&mut self) -> Parsed<RawModule> {
        self.eat(Keyword::Module)?;
        let modname = self.id_chain()?;
        self.eat(Keyword::Where)?;
        let imports = self.imports()?;
        let mut module = Module {
            modname,
            imports,
            uid: self.path.clone(),
            ..Default::default()
        };

        self.populate_module(&mut module)?;
        Ok(module)
    }

    fn populate_module(&mut self, module: &mut RawModule) -> Parsed<()> {
        while !self.is_done() {
            match self.declaration()? {
                Declaration::Data(data) => module.datatys.push(data),
                Declaration::Alias(alias) => module.aliases.push(alias),
                Declaration::Fixity(fixity) => module.infixes.push(fixity),
                Declaration::Class(class) => module.classes.push(class),
                Declaration::Instance(inst) => module.implems.push(inst),
                Declaration::Function(fun) => module.fundefs.push(fun),
                Declaration::Newtype(newty) => module.newtyps.push(newty),
                Declaration::Attribute(attr) => module.pragmas.push(attr),
            }
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
            _ => Err(self.custom_error("is not a valid import")),
        }
    }

    pub fn parse_program(mut self) -> Parsed<RawProgram> {
        use Keyword as K;
        use Module as M;
        Ok(Program {
            module: if self.peek_on(K::Module) {
                self.module()?
            } else {
                let mut module = M::default();
                module.imports = self.many_while_on(K::Import, Self::import_spec)?;
                self.populate_module(&mut module)?;
                module
            },
            fixities: self.fixities,
            comments: self.lexer.comments,
        })
    }
}

#[cfg(test)]
mod test {
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
    fn parse_prelude_module() {
        let src = include_str!("../../../language/prelude/src/lib.wy");
        let result = Parser::from_str(src).parse_program();
        // let dcons = result.as_ref().map(|prog| prog.module.data_ctors());
        match result {
            Ok(program) => {
                println!("showing prim.wy: {:?}", program.module)
            }
            Err(err) => {
                println!("{}", err)
            }
        };
    }
}
