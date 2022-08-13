use crate::error::*;
use crate::stream::*;

use wy_lexer::token::{Keyword, Lexeme};
// use wy_name::ident::Ident;
use wy_span::Spanned;
// use wy_span::WithSpan;
use wy_syntax::fixity::{Assoc, Fixity, Prec};
use wy_syntax::SpannedIdent;

// FIXITY DECLARATIIONS
type FixityParser<'t> = Parser<'t>;
impl<'t> FixityParser<'t> {
    pub(crate) fn fixity_assoc(&mut self) -> Parsed<Assoc> {
        use Assoc as A;
        use Keyword::{Infix, InfixL, InfixR};
        use Lexeme as L;
        let assoc = match self.peek().map(|t| t.lexeme) {
            Some(L::Kw(Infix)) => Ok(A::None),
            Some(L::Kw(InfixL)) => Ok(A::Left),
            Some(L::Kw(InfixR)) => Ok(A::Right),
            _ => Err(self.custom_error("expected fixity keyword `infix`, `infixl`, or `infixr`")),
        }?;
        self.bump();
        Ok(assoc)
    }

    pub(crate) fn fixity_prec(&mut self) -> Parsed<Prec> {
        if let Some(p) = self.peek().and_then(|tok| match tok.lexeme {
            Lexeme::Lit(lit) => lit.try_simple_digit_byte(),
            _ => None,
        }) {
            if p < 10 {
                let prec = Prec(p as u8);
                self.bump();
                return Ok(prec);
            }
        }

        Err(ParseError::InvalidPrec(
            self.srcloc(),
            self.bump(),
            self.text(),
        ))
    }

    pub(crate) fn with_fixity(&mut self, fixity: Fixity) -> Parsed<Vec<SpannedIdent>> {
        self.many_while_on(Lexeme::is_infix, |p| {
            let srcloc = p.srcloc();
            p.expect_infix().and_then(|spanned @ Spanned(infix, span)| {
                if p.fixities.contains_key(&infix) {
                    Err(ParseError::FixityExists(srcloc, infix, span, p.text()))
                } else {
                    p.fixities.insert(infix, fixity);
                    Ok(spanned)
                }
            })
        })
    }
}
