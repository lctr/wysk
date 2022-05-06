pub use wy_failure::{self, Failure, SrcLoc};

use wy_lexer::{
    stream::Source,
    token::{LexKind, Lexeme, Token},
};
use wy_span::Span;
use wy_syntax::ident::Ident;

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
    pub fn srcloc(&self) -> &SrcLoc {
        match self {
            ParseError::UnexpectedEof(srcloc, ..)
            | ParseError::Expected(srcloc, ..)
            | ParseError::InvalidLexeme(srcloc, ..)
            | ParseError::InvalidPrec(srcloc, ..)
            | ParseError::FixityExists(srcloc, ..)
            | ParseError::BadContext(srcloc, ..)
            | ParseError::Custom(srcloc, ..)
            | ParseError::Unbalanced { srcloc, .. } => srcloc,
        }
    }
}

impl std::fmt::Debug for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Parse error: ")?;
        let src = match self {
            ParseError::UnexpectedEof(_srcloc, src) => write!(f, "unexpected EOF").map(|_| src),
            ParseError::Expected(_, kind, found, src) => {
                write!(f, "expected `{}`, but found `{}`", kind, &found.lexeme).map(|_| src)
            }
            ParseError::InvalidLexeme(_, b, src) => write!(
                f,
                "invalid lexeme `{}` found",
                &Source::new(src.as_str())[b.span]
            )
            .map(|_| src),
            ParseError::InvalidPrec(_, found, src) => write!(
                f,
                "expected a precedence value between 0 and 9, but found `{}`",
                &found.lexeme
            )
            .map(|_| src),
            ParseError::FixityExists(_, infix, _, src) => {
                write!(f, "multiple fixities defined for `{}`", &infix).map(|_| src)
            }
            ParseError::Custom(_, found, msg, src) => {
                write!(f, "unexpected token `{}` {}", found.lexeme, msg).map(|_| src)
            }
            ParseError::BadContext(_, id, span, src) => write!(
                f,
                "invalid token `{}` found while parsing type context on {}",
                id, span
            )
            .map(|_| src),
            ParseError::Unbalanced {
                found,
                delim,
                source: src,
                ..
            } => write!(
                f,
                "found `{}` but expected closing delimiter `{}`",
                found.lexeme, delim
            )
            .map(|_| src),
        }?;
        let srcloc = self.srcloc();
        // Parse error: #{MESSAGE}
        //   => #{PATH/TO/FILE}:#{ROW}:#{COL}
        //           |
        //  [#{ROW}] | #{LINE_CODE_BEFORE} #{LEXEME} #{FITTING_LINE_CODE_AFTER}
        //                                 ^^^^^^^^^
        let row = srcloc.coord.row;
        let col = srcloc.coord.col;
        let gutter = srcloc.gutter();
        // TODO: sometimes the error will be on the beginning of the next line
        // (or end of previous line??) with no line text shown at all.
        // womp. fix.
        let line = &&src.lines()[row - 1usize];
        let trimmed = line.trim();
        // string with whitespace trimmed is *never* longer than the original
        let diff = line.len() - trimmed.len();
        let underline = (0..4 + col.abs_diff(diff as u32))
            .map(|_| '-')
            .chain(['^'])
            .collect::<String>();
        write!(f, "\n{}=> {}\n", &gutter, &srcloc)?;
        write!(f, "{}|\n", &gutter)?;
        // write!(f, "{}|\n", &gutter)?;
        write!(f, " [{}]  |    `{}`\n", row, trimmed)?;
        write!(f, "{}|{}\n", &gutter, underline)?;
        write!(f, "{}|\n", &gutter)?;
        Ok(())
    }
}
