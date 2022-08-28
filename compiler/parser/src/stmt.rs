use wy_common::either::Either;
use wy_lexer::lexpat;
use wy_lexer::Keyword;
use wy_lexer::Lexeme;
use wy_lexer::Token;
use wy_syntax::expr::Expression;
use wy_syntax::pattern::RawPattern;
use wy_syntax::stmt::RawStatement;

use crate::error::*;
use crate::stream::*;

pub type StmtParser<'t> = Parser<'t>;
impl<'t> StmtParser<'t> {
    fn maybe_generator(
        &mut self,
        lex: Lexeme,
    ) -> Parsed<Either<(RawPattern, Expression), Expression>> {
        match lex {
            lx if lx.is_lower() => {
                let lower = self.expect_lower()?;
                if self.bump_on(Lexeme::ArrowL) {
                    Ok(Either::Left((RawPattern::Var(lower), self.expression()?)))
                } else {
                    Ok(Either::Right(
                        self.many_while_on(Lexeme::begins_expr, Self::expression)?
                            .into_iter()
                            .fold(Expression::Ident(lower), Expression::mk_app),
                    ))
                }
            }
            lx if lx == Lexeme::Underline => {
                self.bump();
                self.eat(Lexeme::ArrowL)?;
                let expr = self.expression()?;
                Ok(Either::Left((RawPattern::Wild, expr)))
            }
            lx if lx.begins_pat() => {
                let lexer = self.lexer.clone();
                let queue = self.queue.clone();
                let pat = self.pattern()?;
                if self.bump_on(Lexeme::ArrowL) {
                    Ok(Either::Left((pat, self.expression()?)))
                } else {
                    self.lexer = lexer;
                    self.queue = queue;
                    Ok(Either::Right(self.expression()?))
                }
            }
            lx if lx.begins_expr() => self.expression().map(Either::Right),
            _ => self.current_token().and_then(|tok| {
                self.custom_error(tok, " does not begin a pattern or an expression")
                    .err()
            }),
        }
    }

    pub(crate) fn statement(&mut self) -> Parsed<RawStatement> {
        fn bump_comma(parser: &mut Parser) -> bool {
            parser.bump_on(Lexeme::Comma)
        }
        match self.peek() {
            lexpat!(~[do]) => self.do_expr().map(RawStatement::Predicate),
            lexpat!(~[let]) => {
                self.eat(Keyword::Let)?;
                let mut bindings = vec![self.local_def()?];
                self.many_while(bump_comma, Self::local_def)
                    .map(|binds| bindings.extend(binds))?;
                if self.bump_on(Keyword::In) {
                    Ok(RawStatement::Predicate(Expression::Let(
                        bindings,
                        Box::new(self.expression()?),
                    )))
                } else {
                    Ok(RawStatement::JustLet(bindings))
                }
            }
            Some(t) => {
                let lex = t.lexeme;
                self.maybe_generator(lex).map(|ei| match ei {
                    Either::Left((pat, expr)) => RawStatement::Generator(pat, expr),
                    Either::Right(expr) => RawStatement::Predicate(expr),
                })
            }
            _ => self.current_token().and_then(|tok| {
                self.custom_error(tok, " is not supported in `do` expressions")
                    .err()
            }),
        }
    }
}
