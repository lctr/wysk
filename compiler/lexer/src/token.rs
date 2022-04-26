use std::num::ParseFloatError;
use std::str::Chars;
use std::{iter::Peekable, num::ParseIntError};

// use serde::{Deserialize, Serialize};
use wy_common::strenum;
use wy_intern::symbol::{self, Symbol};
pub use wy_span::{
    BytePos, Col, Coord, Located, Location, Row, Span, Spanned, WithLoc,
};

/// A character iterator that tracks byte position as well as row (=line) and
/// column locations.
#[derive(Clone, Debug)]
pub struct Source<'t> {
    pub(crate) src: &'t str,
    pub(crate) pos: BytePos,
    pub(crate) loc: Coord,
    chars: Peekable<Chars<'t>>,
}

impl<'t> Source<'t> {
    pub fn new(src: &'t str) -> Self {
        Self {
            src,
            chars: src.chars().peekable(),
            pos: BytePos::ZERO,
            loc: Coord::new(),
        }
    }

    pub fn get_pos(&self) -> BytePos {
        self.pos
    }

    pub fn get_loc(&self) -> Coord {
        self.loc
    }

    pub fn peek(&mut self) -> Option<&char> {
        self.chars.peek()
    }

    /// Takes the character returned -- if any -- from calling the `peek`
    /// method on the underlying character stream and updates the current byte
    /// position in the `pos` field according to the number of bytes in said
    /// character. Additionally updates the layout location, incremeenting the
    /// `row` by 1 if encountering a line-feed `\n`, and otherwise incrementing
    /// the `column` by 1. If there are no characters left, no side effects are
    /// performed and `None` is returned.
    pub fn next(&mut self) -> Option<char> {
        if let Some(c) = self.chars.peek() {
            self.pos += if c == &'\n' {
                self.loc.incr_row()
            } else {
                self.loc.incr_column(*c)
            };
            self.chars.next()
        } else {
            None
        }
    }

    /// Given a predicate, advances the iterator. Returns a boolean indicating
    /// whether the predicate passed (and hence advanced the iterator).
    pub fn next_if<F>(&mut self, f: F) -> bool
    where
        F: Fn(&char) -> bool,
    {
        if self.test_char(f) {
            self.next();
            true
        } else {
            false
        }
    }

    pub fn is_done(&mut self) -> bool {
        self.chars.peek().is_none()
    }

    /// Given an initial `Pos` *start*, returns the span generated from the
    /// *start* to the current `Pos`.
    pub fn span_from(&self, start: BytePos) -> Span {
        Span(start, self.get_pos())
    }

    pub fn spanned<F, X>(&mut self, mut f: F) -> Spanned<X>
    where
        F: FnMut(&mut Self) -> X,
    {
        let start = self.get_pos();
        let x = f(self);
        let end = self.get_pos();
        Spanned(x, Span(start, end))
    }

    /// Given an initial `Loc` *start*, returns the `Location` generated
    /// from the *start* to the current `Loc`.
    pub fn location_from(&self, start: Coord) -> Location {
        Location {
            start,
            end: self.get_loc(),
        }
    }

    pub fn located<F, X>(&mut self, mut f: F) -> Located<X>
    where
        F: FnMut(&mut Self) -> X,
    {
        let start = self.get_loc();
        let x = f(self);
        let end = self.get_loc();
        Located(x, Location { start, end })
    }

    /// Advances the underlying iterator until a non-whitespace character is
    /// encountered. Returns a span of byte positions corresponding to the
    /// number of bytes consumed.
    #[inline]
    pub fn eat_whitespace(&mut self) -> (Span, Location) {
        let start_pos = self.get_pos();
        let start_loc = self.get_loc();
        while matches!(self.peek(), Some(c) if c.is_whitespace()) {
            self.next();
        }
        (
            Span(start_pos, self.get_pos()),
            Location {
                start: start_loc,
                end: self.get_loc(),
            },
        )
    }

    /// Consumes characters until encountering a whitespace. For use when
    /// skipping the rest of a potential lexeme during a lexing error.
    #[inline]
    pub fn eat_until_whitespace(&mut self) -> (Span, Location) {
        self.eat_while(|c| !c.is_whitespace())
    }

    /// Advance the underlying iterator as long as the given character
    /// predicate holds true.
    pub fn eat_while<F>(&mut self, mut f: F) -> (Span, Location)
    where
        F: FnMut(char) -> bool,
    {
        let start_pos = self.get_pos();
        let start_loc = self.get_loc();
        while matches!(self.peek(), Some(c) if f(*c)) {
            self.next();
        }
        (self.span_from(start_pos), self.location_from(start_loc))
    }

    /// Identifies whether a given character matches that of the character
    /// reference returned by peeking. This will *always* return false if no
    /// more characters are left to be consumed.
    pub fn on_char(&mut self, c: char) -> bool {
        matches!(self.peek(), Some(ch) if ch == &c)
    }

    /// Identifies whether the character returned by `peek` satisfies a given
    /// predicate.
    pub fn test_char<F>(&mut self, f: F) -> bool
    where
        F: Fn(&char) -> bool,
    {
        matches!(self.peek().map(f), Some(true))
    }
}

impl<'t> std::ops::Index<Span> for Source<'t> {
    type Output = str;

    fn index(&self, Span(a, b): Span) -> &Self::Output {
        let len = self.src.len();
        let start = a.as_usize();
        let end = b.as_usize();
        debug_assert!(start <= len && end <= len);
        if start == end {
            ""
        } else if start > end {
            // allow for inverted spans?
            &self.src[end..start]
        } else {
            &self.src[start..end]
        }
    }
}

strenum! { Keyword is_keyword ::
    Let "let"
    In "in"
    If "if"
    Then "then"
    Else "else"
    Case "case"
    Of "of"
    Do "do"

    Where "where"
    With "with"

    Fn "fn"
    Data "data"
    Type "type"
    Class "class"
    Impl "impl"

    InfixL "infixl"
    InfixR "infixr"

    Module "module"
    Import "import"
    Qualified "qualified"
    Hiding "hiding"
}

impl PartialEq<Lexeme> for Keyword {
    fn eq(&self, other: &Lexeme) -> bool {
        matches!(other, Lexeme::Kw(kw) if kw == self)
    }
}

impl PartialEq<Token> for Keyword {
    fn eq(&self, other: &Token) -> bool {
        matches!(&other.lexeme, Lexeme::Kw(kw) if kw == self)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Base {
    /// Base 2 (binary) integers. By default parsed as `u32`.
    Bin,
    /// Base 8 (octal) integers. By default parsed as `u32`.
    Oct,
    /// Base 16 (hexadecimal) integers. By default parsed as `u32`.
    Hex,
    /// Default base (10) for floats and integers.
    Dec,
}

impl Base {
    pub fn radix(&self) -> u32 {
        match self {
            Base::Bin => 2,
            Base::Oct => 8,
            Base::Hex => 16,
            Base::Dec => 10,
        }
    }
}

/// Literals directly parsed during the lexing process. Note that we don't
/// represent negative integers with `Literal`s, as all integers are initially
/// parsed as nonnegatives -- a negative number is represented by the AST as a
/// "negation" node containing a numeric literal.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Literal {
    Byte(u8),
    Int(u32),
    Nat(u64),
    // maybe replace with an interned string symbol and parse later?
    Float(f32),
    Double(f64),
    Char(char),
    Str(Symbol),
}

impl Eq for Literal {}

impl Literal {
    #[inline]
    pub fn parse_byte(src: &str, base: Base) -> Result<u8, ParseIntError> {
        u8::from_str_radix(src, base.radix())
    }

    #[inline]
    pub fn parse_int(src: &str, base: Base) -> Result<u32, ParseIntError> {
        u32::from_str_radix(src, base.radix())
    }

    #[inline]
    pub fn parse_nat(src: &str, base: Base) -> Result<u64, ParseIntError> {
        u64::from_str_radix(src, base.radix())
    }

    #[inline]
    pub fn parse_float(src: &str) -> Result<f32, ParseFloatError> {
        src.parse::<f32>()
    }

    #[inline]
    pub fn parse_double(src: &str) -> Result<f64, ParseFloatError> {
        src.parse::<f64>()
    }

    #[inline]
    pub fn from_u8(b: u8) -> Self {
        Self::Byte(b)
    }

    #[inline]
    pub fn from_u32(n: u32) -> Self {
        Self::Int(n)
    }

    #[inline]
    pub fn from_u64(n: u64) -> Self {
        Self::Nat(n)
    }

    #[inline]
    pub fn from_f32(q: f32) -> Self {
        Self::Float(q)
    }

    #[inline]
    pub fn from_f64(d: f64) -> Self {
        Self::Double(d)
    }

    #[inline]
    pub fn from_char(c: char) -> Self {
        Self::Char(c)
    }

    #[inline]
    pub fn from_str(s: impl AsRef<str>) -> Self {
        Self::Str(symbol::intern_once(s.as_ref()))
    }
}

impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Byte(n) => write!(f, "{}", n),
            Literal::Int(n) => write!(f, "{}", n),
            Literal::Nat(n) => write!(f, "{}", n),
            Literal::Float(n) => write!(f, "{}", n),
            Literal::Double(n) => write!(f, "{}", n),
            Literal::Char(c) => write!(f, "'{}'", c),
            Literal::Str(s) => write!(f, "\"{}\"", s),
        }
    }
}

impl PartialEq<Lexeme> for Literal {
    fn eq(&self, other: &Lexeme) -> bool {
        matches!(other, Lexeme::Lit(lit) if lit == self)
    }
}

impl PartialEq<Token> for Literal {
    fn eq(&self, other: &Token) -> bool {
        matches!(other, Token { lexeme: Lexeme::Lit(lit), .. } if lit == self)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Lexeme {
    Underline, // `_`
    Tilde,     // '~'
    Lambda,    // `\`
    At,        // `@`
    Pound,     // `#`
    Equal,     // `=`
    Comma,     // `,`
    Semi,      // `;`
    Dot,       // `.`
    Dot2,      // `..`
    Colon,     // `:`
    Colon2,    // `::`
    ArrowL,    // `<-`
    ArrowR,    // `->`
    FatArrow,  // `=>`
    Pipe,      // `|`
    ParenL,    // `(`
    ParenR,    // `)`
    BrackL,    // `[`
    BrackR,    // `]`
    CurlyL,    // `{`
    CurlyR,    // `}`
    Kw(Keyword),
    Upper(Symbol),
    Lower(Symbol),
    Infix(Symbol),
    Lit(Literal),
    Unknown, // TODO: integrate lexeme errors
    Eof,
}

impl Lexeme {
    /// Tests whether a lexeme is an identifier beginning with an
    /// uppercase character.
    #[inline]
    pub fn is_upper(&self) -> bool {
        matches!(self, Lexeme::Upper(_))
    }

    /// Tests whether a lexeme is an identifier beginning with a lowercase
    /// character OR an underscore. Note that a single underscore is NOT lexed
    /// as a `Lower` lexeme variant.
    #[inline]
    pub fn is_lower(&self) -> bool {
        matches!(self, Lexeme::Lower(_))
    }

    /// Tests whether a lexeme is an identifier; this includes names beginning
    /// with an uppercase letter, names beginning with either a lowercase
    /// letter (or an underscore along with alphanumeric characters), OR an
    /// infix (corresponding to a sequence of characters entirely made up of
    /// ASCII symbols).
    #[inline]
    pub fn is_ident(&self) -> bool {
        matches!(self, Lexeme::Upper(_) | Lexeme::Lower(_) | Lexeme::Infix(_))
    }

    #[inline]
    pub fn is_kw(&self) -> bool {
        matches!(self, Lexeme::Kw(_))
    }

    #[inline]
    pub fn is_eof(&self) -> bool {
        self == &Lexeme::Eof
    }

    #[inline]
    pub fn is_unknown(&self) -> bool {
        self == &Lexeme::Unknown
    }

    #[inline]
    pub fn meta_kw(&self) -> bool {
        matches!(self, Lexeme::Kw(Keyword::Module | Keyword::Import))
    }

    #[inline]
    pub fn expr_kw(&self) -> bool {
        matches!(
            self,
            Lexeme::Kw(
                Keyword::Let | Keyword::Case | Keyword::If | Keyword::Do
            )
        )
    }

    #[inline]
    pub fn decl_kw(&self) -> bool {
        matches!(
            self,
            Lexeme::Kw(
                Keyword::InfixL
                    | Keyword::InfixR
                    | Keyword::Type
                    | Keyword::Class
                    | Keyword::Data
                    | Keyword::Fn
                    | Keyword::Impl
            )
        )
    }

    #[inline]
    pub fn begins_expr(&self) -> bool {
        matches!(
            self,
            Lexeme::Lambda
                | Lexeme::ParenL
                | Lexeme::BrackL
                | Lexeme::Upper(_)
                | Lexeme::Lower(_)
                | Lexeme::Infix(_)
        )
    }

    #[inline]
    pub fn beginst_pat(&self) -> bool {
        matches!(
            self,
            Lexeme::Upper(_)
                | Lexeme::Lower(_)
                | Lexeme::Lit(_)
                | Lexeme::ParenL
                | Lexeme::BrackL
                | Lexeme::Underline
        )
    }
}

impl From<Literal> for Lexeme {
    fn from(lit: Literal) -> Self {
        Lexeme::Lit(lit)
    }
}

impl PartialEq<Literal> for Lexeme {
    fn eq(&self, other: &Literal) -> bool {
        matches!(self, Lexeme::Lit(lit) if lit == other)
    }
}

impl From<Keyword> for Lexeme {
    fn from(kw: Keyword) -> Self {
        Lexeme::Kw(kw)
    }
}

impl PartialEq<Keyword> for Lexeme {
    fn eq(&self, other: &Keyword) -> bool {
        matches!(self, Lexeme::Kw(kw) if kw == other)
    }
}

impl PartialEq<Token> for Lexeme {
    fn eq(&self, other: &Token) -> bool {
        self == &other.lexeme
    }
}

impl std::fmt::Display for Lexeme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Lexeme::Underline => write!(f, "[Underline] `_`"),
            Lexeme::Tilde => write!(f, "[Tilde] `~`"),
            Lexeme::Lambda => write!(f, "[Lambda] `\\`"),
            Lexeme::At => write!(f, "[At] `@`"),
            Lexeme::Pound => write!(f, "[Pound] `#`"),
            Lexeme::Equal => write!(f, "[Equal] `=`"),
            Lexeme::Comma => write!(f, "[Comma] `,`"),
            Lexeme::Semi => write!(f, "[Semi] `;`"),
            Lexeme::Dot => write!(f, "[Dot] `.`"),
            Lexeme::Dot2 => write!(f, "[Dot2] `..`"),
            Lexeme::Colon => write!(f, "[Colon] `:`"),
            Lexeme::Colon2 => write!(f, "[Colon2] `::`"),
            Lexeme::ArrowL => write!(f, "[ArrowL] `<-`"),
            Lexeme::ArrowR => write!(f, "[ArrowR] `->`"),
            Lexeme::FatArrow => write!(f, "[FatArrow] `=>`"),
            Lexeme::Pipe => write!(f, "[Pipe] `|`"),
            Lexeme::ParenL => write!(f, "[ParenL] `(`"),
            Lexeme::ParenR => write!(f, "[ParenR] `)`"),
            Lexeme::BrackL => write!(f, "[BrackL] `[`"),
            Lexeme::BrackR => write!(f, "[BrackR] `]`"),
            Lexeme::CurlyL => write!(f, "[CurlyL] `{}`", '{'),
            Lexeme::CurlyR => write!(f, "[CurlyR] `{}`", '}'),
            Lexeme::Kw(kw) => write!(f, "[Kw] `{}`", kw),
            Lexeme::Upper(s) => write!(f, "[Upper] `{}`", s),
            Lexeme::Lower(s) => write!(f, "[Lower] `{}`", s),
            Lexeme::Infix(s) => write!(f, "[Infix] `{}`", s),
            Lexeme::Lit(lit) => write!(f, "[Lit] `{}`", lit),
            Lexeme::Unknown => write!(f, "[UNKNOWN]"),
            Lexeme::Eof => write!(f, "[EOF]"),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub lexeme: Lexeme,
    pub span: Span,
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {})", &self.lexeme, &self.span)
    }
}

impl PartialEq<Keyword> for Token {
    fn eq(&self, other: &Keyword) -> bool {
        matches!(&self.lexeme, Lexeme::Kw(kw) if kw == other)
    }
}

impl PartialEq<Literal> for Token {
    fn eq(&self, other: &Literal) -> bool {
        matches!(&self.lexeme, Lexeme::Lit(lit) if lit == other)
    }
}

impl PartialEq<Lexeme> for Token {
    fn eq(&self, other: &Lexeme) -> bool {
        &self.lexeme == other
    }
}

//----ERRORS (maybe move to `Failure` library?---------------------
/// * unknown char -- no rules applicable
/// * invalid integer prefix
/// * invalid number: multiple dots found, like "1.2.3"
/// * invalid number: terminated with dot, like "3."
/// * invalid number: terminated with exponent, like "3e"
/// * invalid number: terminated in exponent sign, like "3e+"
/// * invalid number:
/// * non-terminated character lexeme
/// * invalid character escape
/// * unexpected end of input
/// * non-terminated comment (?)
/// * non-terminated string lexeme (?)
pub struct LexError;
