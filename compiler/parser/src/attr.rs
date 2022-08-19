#![allow(unused)]
use wy_lexer::{
    comment::LineKind,
    meta::{Attr, Meta, Placement},
    stream::Mode,
    token::Not,
    Keyword, Lexeme, Token,
};
use wy_name::Ident;
use wy_span::{BytePos, Span, Spanned, WithSpan};
use wy_syntax::{
    attr::{Attribute, DocLine, Pragma},
    fixity::{Assoc, Fixity, Prec},
    SpannedIdent,
};

use crate::error::*;

use super::stream::*;

impl<'t> Parser<'t> {
    pub fn module_doc_comments(&mut self) -> Vec<Pragma<SpannedIdent, SpannedIdent>> {
        let (reg_comments, doc_comments) = std::mem::take(&mut self.lexer.comments)
            .into_iter()
            .fold((vec![], vec![]), |(mut reg, mut doc), com| {
                match com {
                    c @ (wy_syntax::Comment::Line(_)
                    | wy_syntax::Comment::Block(_)
                    | wy_syntax::Comment::Doc {
                        linekind: LineKind::Ignore,
                        ..
                    }) => reg.push(c),
                    wy_syntax::Comment::Doc { id, span, linekind } => doc.push(Pragma {
                        span,
                        plmt: Placement::Before,
                        attr: Attribute::Doc(DocLine {
                            id,
                            span,
                            line_kind: linekind,
                        }),
                    }),
                };
                (reg, doc)
            });
        self.lexer.comments = reg_comments;
        doc_comments
    }

    pub fn attributes(&mut self) -> Parsed<Vec<Pragma<SpannedIdent, SpannedIdent>>> {
        let (is_before, is_after) = {
            let mode = self.lexer.get_mode();
            (mode.is_meta_before(), mode.is_meta_after())
        };
        match self.peek() {
            Some(Token {
                lexeme: Lexeme::Pound,
                ..
            }) if is_before => self.attr_before(),
            Some(Token {
                lexeme: Lexeme::Hashbang,
                ..
            }) if is_after => self.attr_after(),
            _ => Ok(vec![]),
        }
    }

    /// Continuously parses attribute pragmas that precede the
    /// declaration they describe
    pub fn attr_before(&mut self) -> Parsed<Vec<Pragma<SpannedIdent, SpannedIdent>>> {
        let mut prags = vec![];
        while self.peek_on(Lexeme::Pound) {
            let start = self.get_pos();
            self.eat(Lexeme::Pound)?;
            self.eat(Lexeme::BrackL)?;
            let prag = self.pragma(start, Placement::Before)?;
            prags.push(prag);
        }
        Ok(prags)
    }

    /// Parses attribute pragmas that follow the declaration they describe
    pub fn attr_after(&mut self) -> Parsed<Vec<Pragma<SpannedIdent, SpannedIdent>>> {
        let mut prags = vec![];
        while self.peek_on(Lexeme::Hashbang) && self.lexer.get_mode().is_meta_after() {
            let start = self.get_pos();
            self.eat(Lexeme::Hashbang)?;
            self.eat(Lexeme::BrackL)?;
            let prag = self.pragma(start, Placement::After)?;
            prags.push(prag);
        }
        Ok(prags)
    }

    pub fn pragma(
        &mut self,
        start: BytePos,
        plmt: Placement,
    ) -> Parsed<Pragma<SpannedIdent, SpannedIdent>> {
        let attr = match self.peek() {
            Some(Token {
                lexeme: Lexeme::Meta(meta),
                ..
            }) => {
                let meta = *meta;
                self.meta_head(meta)
            }
            Some(Token {
                lexeme: Lexeme::Eof,
                ..
            })
            | None => self.unexpected_eof().err(),
            Some(t) if t.is_brack_r() => self.empty_pragma().err(),
            _ => self
                .custom_error("is not a valid pragma or attribute name")
                .err(),
        }?;
        self.eat(Lexeme::BrackR)?;
        self.lexer.reset_mode();
        let span = Span(start, self.get_pos());
        Ok(Pragma { span, plmt, attr })
    }

    pub fn meta_head(&mut self, meta: Meta) -> Parsed<Attribute<SpannedIdent, SpannedIdent>> {
        match meta {
            Meta::BuiltIn(attr) => match attr {
                Attr::Inline => Ok(Attribute::Inline),
                Attr::NoInline => Ok(Attribute::NoInline),
                Attr::Fixity => {
                    self.bump();
                    self.fixity_attr()
                }
                Attr::Derive => {
                    self.bump();
                    self.derive_attr()
                }
                Attr::Allow => todo!("lint attributes not yet implemented"),
                Attr::Test => Ok(Attribute::Test),
                Attr::Todo => Ok(Attribute::Todo),
                Attr::Specialize => todo!(),
                Attr::Feature => todo!("feature attributes not yet implemented"),
                Attr::Cfg => todo!("config attributes not yet implemented"),
                Attr::Macro => todo!("macro attributes not yet implemented"),
            },
            Meta::Custom(s) => {
                let s = Ident::Label(s);
                let start = self.get_pos();
                self.bump();
                let span = Span(start, self.get_pos());
                let rest = self.many_while_on(Not(Lexeme::BrackR), |p| Ok(p.bump()))?;
                Ok(Attribute::Custom(Spanned(s, span), rest))
            }
        }
    }

    /// Updates the parser's internal fixity table upon seeing a
    /// fixity attribute; Note that fixity attributes are only allowed
    /// for top-level function declarations!
    pub fn fixity_attr(&mut self) -> Parsed<Attribute<SpannedIdent, SpannedIdent>> {
        fn valid_assoc(parser: &mut Parser, first: bool) -> Parsed<Assoc> {
            match parser.peek() {
                Some(Token {
                    lexeme: Lexeme::Kw(Keyword::Infix),
                    ..
                }) => Ok(Assoc::None),
                Some(Token {
                    lexeme: Lexeme::Kw(Keyword::InfixL),
                    ..
                }) => Ok(Assoc::Left),
                Some(Token {
                    lexeme: Lexeme::Kw(Keyword::InfixR),
                    ..
                }) => Ok(Assoc::Right),
                Some(Token {
                    lexeme: Lexeme::Upper(s) | Lexeme::Lower(s),
                    ..
                }) => match s.as_str() {
                    "l" | "L" | "left" | "Left" | "LEFT" => Ok(Assoc::Left),
                    "r" | "R" | "right" | "Right" | "RIGHT" => Ok(Assoc::Right),
                    "n" | "N" | "none" | "None" | "NONE" => Ok(Assoc::None),
                    _ => {
                        return parser
                            .custom_error("invalid associativity value for fixity attribute")
                            .err()
                    }
                },
                Some(t) if t.is_brack_r() => {
                    if first {
                        parser.custom_error("prematurely closing fixity attribute while expecting associativity").err()
                    } else {
                        Ok(Assoc::None)
                    }
                }
                None
                | Some(Token {
                    lexeme: Lexeme::Eof,
                    ..
                }) => parser.unexpected_eof().err(),
                Some(t) => parser
                    .custom_error("invalid associativity value for fixity attribute")
                    .err(),
            }
        }

        match self.peek() {
            None |
            Some(Token { lexeme: Lexeme::Eof, .. }) => {
                self.unexpected_eof().err()
            }
            Some(t) if t.is_brack_r() => {
                self.custom_error("prematurely closing fixity attribute").err()
            }
            Some(Token { lexeme: Lexeme::Lit(lit), ..}) if lit.is_bare_int() => {
                let prec = self.fixity_prec()?;
                let assoc = valid_assoc(self, false)?;
                self.bump();
                let fixity = Fixity { assoc, prec };
                Ok(Attribute::Fixity(fixity))
            }
            Some(Token { lexeme: Lexeme::Upper(_) | Lexeme::Lower(_), ..}) => {
                let assoc = valid_assoc(self, true)?;
                self.bump();
                let prec = match self.peek() {
                    Some(Token { lexeme: Lexeme::Lit(lit), .. }) if lit.is_bare_int() => {
                        self.fixity_prec()
                    }
                    Some(t) if t.is_brack_r() => {
                        Ok(Prec::MAX)
                    }
                    None | Some(Token { lexeme: Lexeme::Eof, .. }) => {
                        self.unexpected_eof().err()
                    }
                    _ => {
                        self.custom_error("is not a valid precedence value; expected a digit between 0 and 9 or a closing right bracket").err()
                    }
                }?;
                let fixity = Fixity { assoc, prec };
                Ok(Attribute::Fixity(fixity))
            }
            // report invalid fixity pragma value
            _ => self.custom_error("is not a valid fixity attribute parameter, expected -- in any order -- a single digit and/or one of: `l`, `L`, `left`, `Left`, `LEFT`, `infixl`, `r`, `R`, `right`, `Right`, `RIGHT`, `infixr`, `n`, `N`, `none`, `None`, `NONE` or `infix`").err()
        }
    }

    pub fn derive_attr(&mut self) -> Parsed<Attribute<SpannedIdent, SpannedIdent>> {
        self.delimited(
            [Lexeme::ParenL, Lexeme::Comma, Lexeme::ParenR],
            Self::expect_upper,
        )
        .map(Attribute::Derive)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_fixity_attr() {
        let src = "\
        #[fixity 3 L]";
        let mut parser = Parser::from_str(src);
        println!("lexer mode: {:?}", parser.lexer.get_mode());
        parser.peek();
        println!("lexer mode: {:?}", parser.lexer.get_mode());
        let res = parser.attributes().unwrap();
        println!("{:?}", res);
        println!("{:?}", &parser.lexer)
    }
}
