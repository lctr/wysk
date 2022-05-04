use std::num::ParseFloatError;
use std::str::Chars;
use std::{iter::Peekable, num::ParseIntError};

// use serde::{Deserialize, Serialize};
use wy_common::strenum;
use wy_intern::symbol::{self, Symbol};
pub use wy_span::{BytePos, Col, Coord, Located, Location, Row, Span, Spanned, WithLoc, WithSpan};

/// A character iterator that tracks byte position as well as row (=line) and
/// column locations.
#[derive(Clone, Debug)]
pub struct Source<'t> {
    pub(crate) src: &'t str,
    pub(crate) pos: BytePos,
    pub(crate) loc: Coord,
    chars: Peekable<Chars<'t>>,
}

impl<'t> WithLoc for Source<'t> {
    fn get_loc(&self) -> Coord {
        self.loc
    }
}

impl<'t> WithSpan for Source<'t> {
    fn get_pos(&self) -> BytePos {
        self.pos
    }
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

    pub fn string(&self) -> String {
        self.src.to_string()
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

impl<'t> From<Source<'t>> for String {
    fn from(src: Source<'t>) -> Self {
        src.src.to_string()
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
    Infix "infix"

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
    Unknown(LexError),
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
    pub fn is_infix(&self) -> bool {
        matches!(self, Lexeme::Infix(_))
    }

    /// Extracting the `Symbol` stored by a given `Lexeme`, if it contains one.
    /// This is to avoid having to pattern match over a lexeme for its `Symbol`
    /// when it is already known that a `Lexeme` contains a `Symbol`.
    #[inline]
    pub fn symbol(&self) -> Option<Symbol> {
        match self {
            Self::Lower(s) | Self::Upper(s) | Self::Infix(s) | Self::Lit(Literal::Str(s)) => {
                Some(*s)
            }
            _ => None,
        }
    }

    #[inline]
    pub fn is_kw(&self) -> bool {
        matches!(self, Lexeme::Kw(_))
    }

    #[inline]
    pub fn is_lit(&self) -> bool {
        matches!(self, Lexeme::Lit(..))
    }

    #[inline]
    pub fn is_eof(&self) -> bool {
        matches!(self, Lexeme::Eof)
    }

    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Lexeme::Unknown(..))
    }

    #[inline]
    pub fn meta_kw(&self) -> bool {
        matches!(self, Lexeme::Kw(Keyword::Module | Keyword::Import))
    }

    #[inline]
    pub fn expr_kw(&self) -> bool {
        matches!(
            self,
            Lexeme::Kw(Keyword::Let | Keyword::Case | Keyword::If | Keyword::Do)
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
        self.expr_kw()
            || matches!(
                self,
                Lexeme::Lambda
                    | Lexeme::ParenL
                    | Lexeme::BrackL
                    | Lexeme::Upper(_)
                    | Lexeme::Lower(_)
                    | Lexeme::Lit(_)
            )
    }

    #[inline]
    pub fn begins_pat(&self) -> bool {
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

    #[inline]
    pub fn begins_ty(&self) -> bool {
        matches!(
            self,
            Lexeme::Upper(_) | Lexeme::Lower(_) | Lexeme::ParenL | Lexeme::BrackL // | Lexeme::CurlyL
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
            Lexeme::Underline => write!(f, "_"),
            Lexeme::Tilde => write!(f, "~"),
            Lexeme::Lambda => write!(f, "\\"),
            Lexeme::At => write!(f, "@"),
            Lexeme::Pound => write!(f, "#"),
            Lexeme::Equal => write!(f, "="),
            Lexeme::Comma => write!(f, ","),
            Lexeme::Semi => write!(f, ";"),
            Lexeme::Dot => write!(f, "."),
            Lexeme::Dot2 => write!(f, ".."),
            Lexeme::Colon => write!(f, ":"),
            Lexeme::Colon2 => write!(f, "::"),
            Lexeme::ArrowL => write!(f, "<-"),
            Lexeme::ArrowR => write!(f, "->"),
            Lexeme::FatArrow => write!(f, "=>"),
            Lexeme::Pipe => write!(f, "|"),
            Lexeme::ParenL => write!(f, "("),
            Lexeme::ParenR => write!(f, ")"),
            Lexeme::BrackL => write!(f, "["),
            Lexeme::BrackR => write!(f, "]"),
            Lexeme::CurlyL => write!(f, "{}", '{'),
            Lexeme::CurlyR => write!(f, "{}", '}'),
            Lexeme::Kw(kw) => write!(f, "{}", kw),
            Lexeme::Upper(s) => write!(f, "{}", s),
            Lexeme::Lower(s) => write!(f, "{}", s),
            Lexeme::Infix(s) => write!(f, "{}", s),
            Lexeme::Lit(lit) => write!(f, "{}", lit),
            Lexeme::Unknown(err) => write!(f, "<[INVALID]: {}>", err),
            Lexeme::Eof => write!(f, "<[EOF]>"),
        }
    }
}

/// Enumeration used by error reporting within the parser to specify expected
/// lexeme kinds without relying on the data held by specific instances of
/// lexemes. This isn't to be used on its own within error reporting, but as a
/// component of the more general error-reporting types used in order to
/// generate accurate and descriptive messages.
///
/// Additionally, `LexKind`s make a stronger distinction between `Lexeme`s than
/// the general `Lexeme` type. This can be seen with the `Delim` variants, which
/// correspond to lexemes expected in specific (positional) contexts such as
/// `Lexeme::ParenL` (a `LeftDelim`) vs `Lexeme::ParenR` (a `RightDelim`).
///
/// For example, if we expect a constructor (i.e., an identifier beginning with
/// an uppercase letter) and we don't get one, we don't want to have to fill a
/// `Lexeme` instance with a dummy value.
///
/// In the event a specific `Lexeme` is expected, the `Specified` variant is
/// used.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LexKind {
    Identifier,
    Upper,
    Lower,
    Infix,
    Punct,
    LeftDelim,
    RightDelim,
    Keyword,
    Literal,
    Number,
    Character,
    Specified(Lexeme),
}

impl From<Keyword> for LexKind {
    fn from(_: Keyword) -> Self {
        LexKind::Keyword
    }
}

impl From<Literal> for LexKind {
    fn from(lit: Literal) -> Self {
        match lit {
            Literal::Byte(_)
            | Literal::Int(_)
            | Literal::Nat(_)
            | Literal::Float(_)
            | Literal::Double(_) => Self::Number,
            Literal::Char(_) => Self::Character,
            Literal::Str(_) => Self::Literal,
        }
    }
}

impl From<Lexeme> for LexKind {
    fn from(lexeme: Lexeme) -> Self {
        match lexeme {
            Lexeme::Underline
            | Lexeme::Tilde
            | Lexeme::Lambda
            | Lexeme::At
            | Lexeme::Pound
            | Lexeme::Equal
            | Lexeme::Comma
            | Lexeme::Semi
            | Lexeme::Dot
            | Lexeme::Dot2
            | Lexeme::Colon
            | Lexeme::Colon2
            | Lexeme::ArrowL
            | Lexeme::ArrowR
            | Lexeme::FatArrow
            | Lexeme::Pipe => Self::Punct,
            Lexeme::ParenL | Lexeme::BrackL | Lexeme::CurlyL => Self::LeftDelim,
            Lexeme::ParenR | Lexeme::BrackR | Lexeme::CurlyR => Self::RightDelim,
            Lexeme::Kw(_) => Self::Keyword,
            Lexeme::Upper(_) => Self::Upper,
            Lexeme::Lower(_) => Self::Lower,
            Lexeme::Infix(_) => Self::Infix,
            Lexeme::Lit(_) => Self::Literal,
            Lexeme::Unknown(..) | Lexeme::Eof => Self::Specified(lexeme),
        }
    }
}

impl std::fmt::Display for LexKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LexKind::Identifier => {
                write!(
                    f,
                    "identifier beginning with either and uppercase or lowercase letter"
                )
            }
            LexKind::Upper => {
                write!(f, "identifier beginning with an uppercase letter")
            }
            LexKind::Lower => {
                write!(f, "identifier beginning with a lowercase letter")
            }
            LexKind::Infix => {
                write!(f, "infix or identifier surrounded by backticks")
            }
            LexKind::Punct => write!(f, "punctuation"),
            LexKind::LeftDelim => write!(f, "left delimiter"),
            LexKind::RightDelim => write!(f, "right delimiter"),
            LexKind::Keyword => write!(f, "keyword"),
            LexKind::Literal => write!(f, "literal"),
            LexKind::Number => write!(f, "number"),
            LexKind::Character => write!(f, "character"),
            LexKind::Specified(lexeme) => write!(f, "{}", lexeme),
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

impl std::ops::Deref for Token {
    type Target = Lexeme;

    fn deref(&self) -> &Self::Target {
        &self.lexeme
    }
}

impl AsRef<Lexeme> for Token {
    fn as_ref(&self) -> &Lexeme {
        &self.lexeme
    }
}

/// Public interface used to generalize (or alternatively, specify with greater
/// detail) comparisons for type parameters `Tok` (which defaults to `Token`)
/// and `Lex` (which defaults to `Lexeme`) types. This trait is generic in `Tok`
/// and `Lex` to allow for extending existing functionality without specifically
/// requiring the lexemes compared to be a concrete type.
///
/// For example, the `Tok`
/// parameter may be set to `(X, T)` for some `T` that also implements this
/// trait, allowing extra data `X` to be included with lexemes without requiring
/// that extra data specifically be derived from a lexeme.
///
/// Since a `Lexeme` may contain
/// derivative types, such as `Keyword` and `Literal` (all of which are
/// comparable with `Token` and `Lexeme` types), this trait trivially extends
/// this functionality to *non-derivative* types. A nontrivial example is that
/// of types `F` that implement `FnMut(Lex) -> bool`, which allows for
/// comparisons using predicates instead of just relying on `PartialEq`.
///
/// The idea behind this trait is to allow for greater ergonomics in applying
/// predicates and in fact was inspired by the Rust `Pattern<'a>` trait (not to
/// be confused with other types in the compiler named `Pattern`), which allows
/// for comparison-based functionality on string slices using characters, other
/// string slices, or character-valued predicates.
///
/// An example of a type that benefits from implementing this trait, but that
/// isn't a derivative type of `Token` or `Lexeme`
pub trait Lexlike<Tok = Token, Lex = Lexeme> {
    fn cmp_lex(&self, lex: &Lex) -> bool;
    fn cmp_tok(&self, tok: &Tok) -> bool;

    fn compare<T>(&self, item: T) -> bool
    where
        T: PartialEq<Tok>,
        Tok: PartialEq<T>,
        Lex: From<T>,
    {
        self.cmp_lex(&Lex::from(item))
    }
}

impl<F> Lexlike for F
where
    F: Fn(&Lexeme) -> bool,
{
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        (self)(lex)
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        (self)(&tok.lexeme)
    }
}

impl Lexlike for Keyword {
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        self == lex
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self == &tok.lexeme
    }
}

impl Lexlike for Literal {
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        self == lex
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self == &tok.lexeme
    }
}

impl Lexlike for Lexeme {
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        self == lex
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self == &tok.lexeme
    }
}

impl Lexlike for Token {
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        &self.lexeme == lex
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self == tok
    }
}

/// Allow lexeme comparison with the results of calling a `peek` method
/// analogous to that of `Peekable::<T>::peek`.
impl<T> Lexlike for Option<&T>
where
    T: Lexlike,
{
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        if let Some(t) = self {
            t.cmp_lex(lex)
        } else {
            lex.is_eof()
        }
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        if let Some(t) = self {
            t.cmp_tok(tok)
        } else {
            tok.lexeme.is_eof()
        }
    }
}

//----ERRORS (maybe move to `Failure` library?---------------------
/// Flags used to denote invalid lexemes stemming from lexer failures.
///
/// The messages printed by this enum should answer the question "what
/// happened?" such that the offending lexeme could naturally be quoted
/// afterwards
///
/// The following cases are covered:
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
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum LexError {
    /// Emitted when encountering a character that doesn't belong to any lexeme
    /// kinds
    Unsupported,
    /// Emitted when an unsupported character is escaped in either string or
    /// character literals
    InvalidEscape,
    /// Emitted when a character literal was not terminated, i.e., when a single
    /// quote is missing its closing pair `'`
    UnterminatedChar,
    /// Emitted when encountering an EOF before a string literal is terminated,
    /// i.e., when a double quote is missing its closing pair `"`
    UnterminatedString,
    /// Emitted when encountering a non-identifier character before a closing
    /// backtick.
    ///
    /// Examples:
    /// * invalid due to space:
    ///
    ///         `modulo`
    /// * invalid due to non-lowercase-initial* identifier `#`:
    ///
    ///         `foo#`
    /// * invalid, `<>` is already an infix:
    ///
    ///         `<>`
    ///
    ///
    UnterminatedInfix,
    /// Emitted when encountering a nondigit character (that isn't `b`, `B`,
    /// `o`, `O`, `x`, or `X`) after (the initial) `0` in a number beginning
    /// with `0`.
    InvalidIntPrefix,
    /// Emitted when encountering empty backticks, i.e., "``".
    EmptyInfix,
    /// Emitted when a non-lowercase initial identifier character is found
    /// between backticks.
    InvalidInfix,
    /// Emitted when a numeric literal ends in a decimal.
    ///
    /// ### Examples:
    /// * `3e`
    /// * `5.4e+`
    MissingExponent,
    /// Emitted when a non-integer is found after the `e`, `+`, or `-` in a
    /// numeric literal
    ///
    /// ### Examples:
    /// * `210.`
    MissingFractional,
    /// Emitted when encountering a dot and then a number. Note that the string
    /// `3.4.5` is lexed as `3.4` -> `.5`, where this error corresponds to `.5`
    MissingIntegral,
    /// Emitted when parsing a numeric literal to a Rust number fails
    MalformedNumber,
    /// Emitted when encountering the EOF after `~{` without a closing `}~`.
    UnterminatedComment,
}
impl std::error::Error for LexError {}

impl std::fmt::Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LexError::Unsupported => write!(f, "found unsupported grapheme"),
            LexError::InvalidEscape => write!(f, "invalid character escape"),
            LexError::UnterminatedChar => write!(f, "unterminated character literal"),
            LexError::UnterminatedString => write!(f, "unterminated string literal"),
            LexError::UnterminatedInfix => write!(f, "unterminated backticks"),
            LexError::InvalidIntPrefix => write!(f, "invalid integer prefix"),
            LexError::EmptyInfix => write!(f, "no content between backticks"),
            LexError::InvalidInfix => write!(
                f,
                "non-lowercase initial identifier character found between backticks"
            ),
            LexError::MissingExponent => {
                write!(f, "scientific notation missing exponent in numeric literal")
            }
            LexError::MissingFractional => write!(
                f,
                "digits not found after decimal point in floating point number"
            ),
            LexError::MissingIntegral => write!(f, "decimal point found beginning numeric literal"),
            LexError::MalformedNumber => write!(f, "malformed integer"),
            LexError::UnterminatedComment => write!(f, "block comment not terminated"),
        }
    }
}

#[macro_export]
macro_rules! lexpat {
    ($self:ident on [<-]) => {
        matches!($self.peek(), Some(Token { lexeme: Lexeme::ArrowL, .. }))
    };
    ([_]) => {
        Lexeme::Underline
    };
    ([:]) => {
        Lexeme::Colon
    };
    ([::]) => {
        Lexeme::Colon2
    };
    ([..]) => {
        Lexeme::Dot2
    };
    ([.]) => {
        Lexeme::Dot
    };
    ([,]) => {
        Lexeme::Comma
    };
    ([;]) => {
        Lexeme::Semi
    };
    ([|]) => {
        Lexeme::Pipe
    };
    ([->]) => {
        Lexeme::ArrowR
    };
    ([<-]) => {
        Lexeme::ArrowL
    };
    ([=]) => {
        Lexeme::Equal
    };
    ([=>]) => {
        Lexeme::FatArrow
    };
    ([~]) => {
        Lexeme::Tilde
    };
    ([@]) => {
        Lexeme::At
    };
    ([#]) => {
        Lexeme::Pound
    };
    ([lam]) => {
        Lexeme::Lambda
    };
    ([parenL]) => {
        Lexeme::ParenL
    };
    ([parenR]) => {
        Lexeme::ParenR
    };
    ([brackL]) => {
        Lexeme::BrackL
    };
    ([brackR]) => {
        Lexeme::BrackR
    };
    ([curlyL]) => {
        Lexeme::CurlyL
    };
    ([curlyR]) => {
        Lexeme::CurlyR
    };
    (some [$ts:tt]) => {
        Some(Token { lexeme: lexpat!{[$ts]}, .. })
    };
    (~[$t:tt] $([$ts:tt])*) => {
        Some(Token { lexeme: (lexpat!([$t]) $(| lexpat!([$ts]))*), .. })
    };
    (maybe [$t0:tt] $([$ts:tt])*) => {
        Some(Token { lexeme: (lexpat!{[$t0]} $(| lexpat!{[$ts]})*), .. })
    };
    ($self:ident on [$t:tt$($t2:tt)?]) => {{
        matches!($self.peek(), lexpat!(some [$t$($t2)?]))
    }};
    ($self:ident on [$t:tt] $(| [$ts:tt])+) => {{
        matches!($self.peek(), lexpat!(~[$t]) $(| lexpat!(~[$ts]))+)
    }};
    (? $lexeme:ident [$t:tt]) => {
        matches!($lexeme, lexpat!([$t]))
    };
    (? $lexeme:ident [$t:tt] $(| [$r:tt])* ) => {
        lexpat!(? $lexeme [$t]) $(|| lexpat!(? $lexeme [$r]))*
    };
    ([??]) => {
        Lexeme::Unknown
    };
    ([eof]) => {
        Lexeme::Eof
    };
    ([lit]) => {
        Lexeme::Lit(_)
    };
    ([op]) => {
        Lexeme::Infix(_)
    };
    ([kw]) => {
        Lexeme::Kw(_)
    };
    ([var]) => (
        Lexeme::Lower(_)
    );
    ([Var]) => (
        Lexeme::Upper(_)
    );
    ([let]) => {
        Lexeme::Kw(Keyword::Let)
    };
    ([in]) => {
        Lexeme::Kw(Keyword::In)
    };
    ([where]) => {
        Lexeme::Kw(Keyword::Where)
    };
    ([if]) => {
        Lexeme::Kw(Keyword::If)
    };
    ([then]) => {
        Lexeme::Kw(Keyword::Then)
    };
    ([else]) => {
        Lexeme::Kw(Keyword::Else)
    };
    // ([match]) => {Lexeme::Kw(Keyword::Match)};
    ([case]) => {
        Lexeme::Kw(Keyword::Case)
    };
    ([of]) => {
        Lexeme::Kw(Keyword::Of)
    };
    ([do]) => {
        Lexeme::Kw(Keyword::Do)
    };
    ([fn]) => {
        Lexeme::Kw(Keyword::Fn)
    };
    ([data]) => {
        Lexeme::Kw(Keyword::Data)
    };
    ([type]) => {
        Lexeme::Kw(Keyword::Type)
    };
    ([with]) => {
        Lexeme::Kw(Keyword::With)
    };
    ([class]) => {
        Lexeme::Kw(Keyword::Class)
    };
    ([impl]) => {
        Lexeme::Kw(Keyword::Impl)
    };
    ([infixl]) => {
        Lexeme::Kw(Keyword::InfixL)
    };
    ([infixr]) => {
        Lexeme::Kw(Keyword::InfixR)
    };
    ([infix]) => {
        Lexeme::Kw(Keyword::Infix)
    };
    ([module]) => {
        Lexeme::Kw(Keyword::Module)
    };
    ([qualified]) => {
        Lexeme::Kw(Keyword::Qualified)
    };
    ([hiding]) => {
        Lexeme::Kw(Keyword::Hiding)
    };
}
