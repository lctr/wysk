use std::path::{Path, PathBuf};

pub use wy_failure::{self, Failure};

use wy_lexer::{
    stream::Source,
    token::{LexKind, Lexeme, Token},
};
use wy_name::ident::Ident;
use wy_span::{Coord, Row, Span};

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
            | ParseError::InvalidPattern(srcloc, ..)
            | ParseError::InvalidExpression(srcloc, ..)
            | ParseError::InvalidType(srcloc, ..)
            | ParseError::FixityExists(srcloc, ..)
            | ParseError::BadContext(srcloc, ..)
            | ParseError::Custom(srcloc, ..)
            | ParseError::Unbalanced { srcloc, .. } => srcloc,
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
        write!(f, "Parse error: ")?;
        let src = match self {
            ParseError::UnexpectedEof(_srcloc, src) => write!(f, "unexpected EOF").and(Ok(src)),
            ParseError::Expected(_, kind, found, src) => {
                write!(f, "expected `{}`, but found `{}`", kind, &found.lexeme).and(Ok(src))
            }
            ParseError::InvalidLexeme(_, b, src) => write!(
                f,
                "invalid lexeme `{}` found",
                &Source::new(src.as_str())[b.span]
            )
            .and(Ok(src)),
            ParseError::InvalidPrec(_, found, src) => write!(
                f,
                "expected a precedence value between 0 and 9, but found `{}`",
                &found.lexeme
            )
            .map(|_| src),
            ParseError::InvalidPattern(_, tok, src) if tok.is_minus_sign() => {
                write!(f, "only numeric literals are allowed as negated ungrouped patterns: all other patterns must be wrapped in parentheses").and(Ok(src))
            }
            ParseError::InvalidPattern(_, tok, src) => write!(
                f,
                "expected a pattern, but found `{}` which does not begin a valid pattern",
                tok
            )
            .and(Ok(src)),
            ParseError::InvalidExpression(_, tok, src) => write!(
                f,
                "expected an expression, but found `{}` which does not begin a valid expression",
                tok
            )
            .and(Ok(src)),
            ParseError::InvalidType(_, tok, src) => write!(
                f,
                "expected a type, but found `{}` which does not begin a valid type",
                tok
            )
            .and(Ok(src)),
            ParseError::FixityExists(_, infix, _, src) => {
                write!(f, "multiple fixities defined for `{}`", &infix).map(|_| src)
            }
            ParseError::Custom(_, found, msg, src) => {
                write!(f, "unexpected token `{}` {}", found.lexeme, msg).and(Ok(src))
            }
            ParseError::BadContext(_, id, span, src) => write!(
                f,
                "invalid token `{}` found while parsing type context on {}",
                id, span
            )
            .and(Ok(src)),
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
            .and(Ok(src)),
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

pub trait Expects {
    fn expects(reporter: &mut impl Report, lexes: LexKind) -> ParseError {
        reporter.expected(lexes)
    }
}

impl Expects for ParseError {}

//---------- FOR FILE-CONTENT-RELATED STUFF, such as parsing, lexing, etc
/// Describing the source path and position, primarily used in error reporting.
/// This should be included in every error message to be able to reproduce
/// tracking information regarding the source code involved during error
/// reporting.
///
/// The error should effectively be able to produce a string of the form
/// ```txt
///         [PATH/TO/FILE]:[ROW][COL]
/// ```
/// in error messages.

#[derive(Clone, Debug, PartialEq)]
pub enum SrcPath<P: AsRef<Path> = PathBuf> {
    Direct,
    File(P),
}

impl<P: AsRef<Path>> Default for SrcPath<P> {
    fn default() -> Self {
        Self::Direct
    }
}

impl<P: AsRef<Path>> std::fmt::Display for SrcPath<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SrcPath::Direct => write!(f, "<STDIN>"),
            SrcPath::File(p) => write!(f, "{}", p.as_ref().display()),
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct SrcLoc {
    pub coord: Coord,
    pub pathstr: SrcPath<PathBuf>,
}

impl std::fmt::Display for SrcLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // include only starting coordinates?
        write!(f, "{}:{}", &self.pathstr, &self.coord)
    }
}

impl std::fmt::Debug for SrcLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl SrcLoc {
    pub fn gutter(&self) -> RowGutter {
        RowGutter(self.coord.row)
    }
}

/// Error printing utility
#[derive(Copy, Clone, PartialEq, PartialOrd)]
pub struct RowGutter(Row);
impl std::fmt::Display for RowGutter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for _ in 0..(4 + self.0.strlen()) {
            char::fmt(&' ', f)?;
        }
        Ok(())
    }
}

pub struct WithSrcLoc<X>(X, SrcLoc, String);
impl<X> WithSrcLoc<X> {
    pub fn new(x: X, srcloc: SrcLoc, text: String) -> Self {
        Self(x, srcloc, text)
    }
    pub fn srcloc(&self) -> &SrcLoc {
        &self.1
    }
    pub fn item(&self) -> &X {
        &self.0
    }
    pub fn text(&self) -> &String {
        &self.2
    }
    pub fn parts(self) -> (X, SrcLoc, String) {
        let WithSrcLoc(x, srcloc, text) = self;
        (x, srcloc, text)
    }
}
