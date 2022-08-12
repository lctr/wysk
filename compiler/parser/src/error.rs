pub use wy_failure::{self, Dialogue, Failure};

pub use wy_failure::{SrcLoc, SrcPath};

use wy_lexer::{
    stream::Source,
    token::{LexKind, Lexeme, Token},
};
use wy_name::ident::Ident;
use wy_span::Span;

pub trait Report {
    fn get_srcloc(&mut self) -> SrcLoc;
    fn get_source(&self) -> String;
    fn next_token(&mut self) -> Token;

    #[inline(always)]
    fn snapshot(&mut self) -> (SrcLoc, Token, String) {
        (self.get_srcloc(), self.next_token(), self.get_source())
    }
    fn expected(&mut self, lexes: LexKind) -> ParseError {
        let (srcloc, tok, src) = self.snapshot();
        ParseError::Expected(srcloc, lexes, tok, src)
    }
    fn unexpected_eof(&mut self) -> ParseError {
        ParseError::UnexpectedEof(self.get_srcloc(), self.get_source())
    }
    fn unknown_lexeme(&mut self) -> ParseError {
        let (srcloc, tok, src) = self.snapshot();
        ParseError::InvalidLexeme(srcloc, tok, src)
    }
    fn invalid_pattern(&mut self) -> ParseError {
        let (srcloc, tok, src) = self.snapshot();
        ParseError::InvalidPattern(srcloc, tok, src)
    }
    fn invalid_expr(&mut self) -> ParseError {
        let (srcloc, tok, src) = self.snapshot();
        ParseError::InvalidExpression(srcloc, tok, src)
    }
    fn invalid_type(&mut self) -> ParseError {
        let (srcloc, tok, src) = self.snapshot();
        ParseError::InvalidType(srcloc, tok, src)
    }
    fn invalid_fn_ident(&mut self) -> ParseError {
        self.custom_error("is not a valid function name: expected a lowercase-initial identifier or an infix wrapped in parentheses")
    }
    fn custom_error(&mut self, message: &'static str) -> ParseError {
        let (srcloc, tok, src) = self.snapshot();
        ParseError::Custom(srcloc, tok, message, src)
    }

    fn unbalanced(&mut self, delim: Lexeme) -> ParseError {
        let (srcloc, found, source) = self.snapshot();
        ParseError::Unbalanced {
            srcloc,
            found,
            delim,
            source,
        }
    }
    fn unbalanced_paren(&mut self) -> ParseError {
        self.unbalanced(Lexeme::ParenR)
    }
    fn unbalanced_brack(&mut self) -> ParseError {
        self.unbalanced(Lexeme::BrackR)
    }
    fn unbalanced_curly(&mut self) -> ParseError {
        self.unbalanced(Lexeme::CurlyR)
    }
}

pub type Parsed<X> = Result<X, ParseError>;
/// Error messages provided by the `Parser`. A general message *should* have the
/// following components:
/// 1. What went wrong
/// 2. Where it happened
/// 3. What grammatical rule we unfulfilled*
///
/// For example, an "Expected" error message should follow the following layout:
/// ```txt
/// Unexpected token found while GRAMMAR_RULE. Expected EXPECTED but found
/// TOKEN at COORD:
///   => [PATH/ROW:COL]
///         |
///   [ROW] | <LINE_WITH_BAD_TOKEN> <BAD_TOKEN> ...
///         |                       ^^^^^^^^^^^
/// ```
#[derive(Clone, PartialEq)]
pub enum ParseError {
    UnexpectedEof(SrcLoc, String),
    Expected(SrcLoc, LexKind, Token, String),
    InvalidLexeme(SrcLoc, Token, String),
    InvalidPrec(SrcLoc, Token, String),
    InvalidNegatedPattern(SrcLoc, Token, String),
    InvalidPattern(SrcLoc, Token, String),
    InvalidExpression(SrcLoc, Token, String),
    InvalidType(SrcLoc, Token, String),
    FixityExists(SrcLoc, Ident, Span, String),
    BadContext(SrcLoc, Ident, Span, String),
    Custom(SrcLoc, Token, &'static str, String),
    Unbalanced {
        srcloc: SrcLoc,
        found: Token,
        delim: Lexeme,
        source: String,
    },
}

impl std::error::Error for ParseError {}

wy_failure::fails!(impl for ParseError);

impl ParseError {
    #[inline]
    pub fn err<X>(self) -> Result<X, Self> {
        Err(self)
    }
    pub fn srcloc(&self) -> &SrcLoc {
        match self {
            ParseError::UnexpectedEof(srcloc, ..)
            | ParseError::Expected(srcloc, ..)
            | ParseError::InvalidLexeme(srcloc, ..)
            | ParseError::InvalidPrec(srcloc, ..)
            | ParseError::InvalidNegatedPattern(srcloc, ..)
            | ParseError::InvalidPattern(srcloc, ..)
            | ParseError::InvalidExpression(srcloc, ..)
            | ParseError::InvalidType(srcloc, ..)
            | ParseError::FixityExists(srcloc, ..)
            | ParseError::BadContext(srcloc, ..)
            | ParseError::Custom(srcloc, ..)
            | ParseError::Unbalanced { srcloc, .. } => srcloc,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            ParseError::UnexpectedEof(_, s) => {
                let len = Span::of_str(s).end();
                Span(len, len)
            }
            ParseError::Expected(_, _, Token { span, .. }, _)
            | ParseError::InvalidLexeme(_, Token { span, .. }, _)
            | ParseError::InvalidPrec(_, Token { span, .. }, _)
            | ParseError::InvalidNegatedPattern(_, Token { span, .. }, _)
            | ParseError::InvalidPattern(_, Token { span, .. }, _)
            | ParseError::InvalidExpression(_, Token { span, .. }, _)
            | ParseError::InvalidType(_, Token { span, .. }, _)
            | ParseError::Custom(_, Token { span, .. }, _, _)
            | ParseError::Unbalanced {
                found: Token { span, .. },
                ..
            }
            | ParseError::FixityExists(_, _, span, _)
            | ParseError::BadContext(_, _, span, _) => *span,
        }
    }
}

impl<X> From<ParseError> for Result<X, ParseError> {
    fn from(e: ParseError) -> Self {
        e.err()
    }
}

impl std::fmt::Debug for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (message, srcloc, srctext) = match self {
            ParseError::UnexpectedEof(srcloc, src) => {
                ("unexpected EOF".into(), srcloc, src)},
            ParseError::Expected(srcloc, kind, found, src) => {
                (
                    format!("expected `{}`, but found `{}`", kind, &found.lexeme), 
                    srcloc, 
                    src
                )
            }
            ParseError::InvalidLexeme(srcloc, b, src) => {
                (
                    format!("invalid lexeme `{}` found", &Source::new(src.as_str())[b.span]), 
                    srcloc, 
                    src
                )
            },
            ParseError::InvalidPrec(srcloc, found, src) => {
                (
                    format!("expected a precedence value between 0 and 9, but found `{}`", &found.lexeme), 
                    srcloc, 
                    src
                )
            },
            ParseError::InvalidNegatedPattern(srcloc, tok, src)  => {
                (
                    format!("only numeric literals are allowed as negated ungrouped patterns, but `{tok}` is not a numeric literal: all other patterns must be wrapped in parentheses"), 
                    srcloc, 
                    src
                )
            }
            ParseError::InvalidPattern(srcloc, tok, src) => (
                format!("expected a pattern, but found `{}` which does not begin a valid pattern", tok), 
                srcloc, 
                src
            ),
            ParseError::InvalidExpression(srcloc, tok, src) => (
                format!("expected an expression, but found `{}` which does not begin a valid expression", tok), 
                srcloc, 
                src
            ),
            ParseError::InvalidType(srcloc, tok, src) => (
                format!("expected a type, but found `{}` which does not begin a valid type", tok), 
                srcloc, 
                src
            ),
            ParseError::FixityExists(srcloc, infix, _, src) => {
                (format!("multiple fixities defined for `{}`", &infix), srcloc, src)
            }
            ParseError::Custom(srcloc, found, msg, src) => {
                (format!("unexpected token `{}` {}", found.lexeme, msg), srcloc, src)
            }
            ParseError::BadContext(srcloc, id, span, src) => (
                format!("invalid token `{}` found while parsing type context on {}", id, span), 
                srcloc, 
                src
            ),
            ParseError::Unbalanced {
                srcloc,
                found,
                delim,
                source: src,
            } => (
                format!("found `{}` but expected closing delimiter `{}`", found.lexeme, delim),
                srcloc, 
                src
            ),
        };
        Dialogue::new("Parse error:", message, srctext, srcloc, self.span()).display(f)
    }
}

pub trait Expects {
    fn expects(reporter: &mut impl Report, lexes: LexKind) -> ParseError {
        reporter.expected(lexes)
    }
}

impl Expects for ParseError {}
