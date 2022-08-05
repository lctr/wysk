use token::*;
use wy_lexer::*;
use wy_name::ident::Ident;
use wy_syntax::{
    expr::RawExpression,
    tipo::{Signature, Type},
    RawProgram,
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

pub fn parse_program(src: &str) -> Parsed<RawProgram> {
    Parser::from_str(src).parse_program()
}

/// Parsing the type portion of a type signature in an isolated context
pub fn parse_type_node(src: &str) -> Parsed<Type> {
    Parser::from_str(src).ty_node()
}

/// Parsing a type signature in an isolated context
pub fn parse_type_signature(src: &str) -> Parsed<Signature<Ident, Ident>> {
    Parser::from_str(src).ty_signature()
}

/// Parsing en expression in an isolated context
pub fn parse_expression(src: &str) -> Parsed<RawExpression> {
    Parser::from_str(src).expression()
}

pub fn try_parse_file<P: AsRef<std::path::Path>>(
    filepath: P,
) -> Result<RawProgram, Failure<ParseError>> {
    let path = filepath.as_ref();
    let content = std::fs::read_to_string(path)?;
    Parser::new(content.as_str(), Some(path.to_owned()))
        .parse_program()
        .map_err(Failure::Err)
}
