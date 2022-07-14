use token::*;

use wy_lexer::*;
use wy_name::ident::{Chain, Ident};
use wy_syntax::{
    decl::Declaration,
    expr::RawExpression,
    tipo::{Signature, Tv, Type},
    Ast, Import, ImportSpec, Module, Program, RawModule, RawProgram, SyntaxTree,
};

mod decl;
pub mod error;
mod expr;
pub mod fixity;
mod pat;
mod program;
pub mod stream;
mod ty;

use error::*;

use stream::{Parser, Streaming};

// IDENTIFIERS AND LITERAL
impl<'t> Parser<'t> {
    fn expect_upper(&mut self) -> Parsed<Ident> {
        self.peek()
            .and_then(|t| t.upper_symbol().map(Ident::Upper))
            .map(|id| self.bumped(id))
            .ok_or_else(|| self.expected(LexKind::Upper))
    }

    fn expect_lower(&mut self) -> Parsed<Ident> {
        self.peek()
            .and_then(|t| t.lower_symbol().map(Ident::Lower))
            .map(|id| self.bumped(id))
            .ok_or_else(|| self.expected(LexKind::Lower))
    }

    fn expect_infix(&mut self) -> Parsed<Ident> {
        self.peek()
            .and_then(|t| t.infix_symbol().map(Ident::Infix))
            .map(|id| self.bumped(id))
            .ok_or_else(|| self.expected(LexKind::Infix))
    }

    fn expect_ident(&mut self) -> Parsed<Ident> {
        self.peek()
            .and_then(Token::lift(Lexeme::mk_id(Ident::NAMES)))
            .map(|id| self.bumped(id))
            .ok_or_else(|| self.expected(LexKind::Identifier))
    }

    fn expect_literal(&mut self) -> Parsed<Literal> {
        self.peek()
            .and_then(|t| t.literal())
            .map(|lit| self.bumped(lit))
            .ok_or_else(|| self.expected(LexKind::Literal))
    }
}

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
            uid: self.filepath.clone(),
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
            lexpat!(~[parenL]) => {
                self.eat(L::ParenL)?;
                let infix = self.expect_infix()?;
                self.eat(L::ParenR)?;
                Ok(I::Operator(infix))
            }
            lexpat!(~[Var]) => {
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

    pub fn parse(mut self) -> Parsed<RawProgram> {
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

pub fn parse_input(src: &str) -> Parsed<RawProgram> {
    Parser::from_str(src).parse()
}

/// Parsing the type portion of a type signature in an isolated context
#[allow(unused)]
pub fn parse_type_node(src: &str) -> Parsed<Type> {
    Parser::from_str(src).ty_node()
}

/// Parsing a type signature in an isolated context
#[allow(unused)]
pub fn parse_type_signature(src: &str) -> Parsed<Signature> {
    Parser::from_str(src).total_signature()
}

/// Parsing en expression in an isolated context
#[allow(unused)]
pub fn parse_expression(src: &str) -> Parsed<RawExpression> {
    Parser::from_str(src).expression()
}

pub fn try_parse_file<P: AsRef<std::path::Path>>(
    filepath: P,
) -> Result<RawProgram, Failure<ParseError>> {
    let path = filepath.as_ref();
    let content = std::fs::read_to_string(path)?;
    Parser::new(content.as_str(), Some(path.to_owned()))
        .parse()
        .map_err(Failure::Err)
}

#[cfg(test)]
#[allow(unused)]
mod test;
