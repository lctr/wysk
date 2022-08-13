use serde::Deserialize;
use serde::Serialize;
// use serde::{Deserialize, Serialize};
use wy_common::ref_lifting_strenum;
use wy_intern::symbol::{self, Symbol};
use wy_span::Dummy;
pub use wy_span::{BytePos, Col, Coord, Located, Location, Row, Span, Spanned, WithLoc, WithSpan};

use crate::literal::*;
use crate::meta::*;

ref_lifting_strenum! { Keyword is_keyword => Lexeme Kw ::
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
    Newtype "newtype"
    Def "def"

    Forall "forall"

    InfixL "infixl"
    InfixR "infixr"
    Infix "infix"

    Module "module"
    Import "import"
    Qualified "qualified"
    Hiding "hiding"

    Extern "extern"
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

impl PartialEq<Lexeme> for Attr {
    fn eq(&self, other: &Lexeme) -> bool {
        matches!(other.symbol(), Some(s) if s == Symbol::from_str(self.as_str()))
    }
}

impl PartialEq<Attr> for Lexeme {
    fn eq(&self, other: &Attr) -> bool {
        matches!(self.symbol(), Some(s) if s == Symbol::from_str(other.as_str()))
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

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Lexeme {
    Underline, // `_`
    Unlabel,   // `'_`
    Tilde,     // '~'
    Lambda,    // `\`
    At,        // `@`
    Pound,     // `#`
    Bang,      // `!`
    Hashbang,  // `#!`
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
    Label(Symbol),
    Lit(Literal),
    Meta(Meta),
    Unknown(LexError),
    Eof,
}

wy_common::variant_preds! {
    Lexeme
    | is_kw => Kw (_)
    | is_lit => Lit (_)
    | is_numeric => Lit(Literal::Integral { .. } | Literal::Fractional { .. })
    /// Tests whether a lexeme is an identifier beginning with a lowercase
    /// character OR an underscore. Note that a single underscore is NOT lexed
    /// as a `Lower` lexeme variant.
    | is_lower => Lower (_)
    /// Tests whether a lexeme is an identifier beginning with an
    /// uppercase character.
    | is_upper => Upper (_)
    /// NOTE: This includes `:`, even though it is lexed as a `Lexeme::Colon`
    | is_infix => Infix (_) [ | Self::Colon]
    | is_label => Label (_)
    | is_eof => Eof
    /// Tests whether a lexeme is an identifier; this includes names beginning
    /// with an uppercase letter, names beginning with either a lowercase
    /// letter (or an underscore along with alphanumeric characters), OR an
    /// infix (corresponding to a sequence of characters entirely made up of
    /// ASCII symbols).
    | is_ident => Upper (_) [ | Self::Lower(_) | Self::Infix(_)]
    | is_meta => Meta (_)
    | is_eq_sign => Equal
    | is_fat_arrow => FatArrow
    | is_colon => Colon
    | is_colon2 => Colon2
    | is_pipe => Pipe
    | is_semi => Semi
    | is_comma => Comma
    | is_pound => Pound
    | is_arrow_r => ArrowR
    | is_arrow_l => ArrowL
    | is_paren_l => ParenL
    | is_paren_r => ParenR
    | is_brack_l => BrackL
    | is_brack_r => BrackR
    | is_curly_l => CurlyL
    | is_curly_r => CurlyR
    | is_unknown => Unknown (..)
    | is_left_delim => ParenL [ | Self::BrackL | Self::CurlyL ]
    | is_right_delim => ParenR [ | Self::BrackR | Self::CurlyR ]
    | is_builtin_attr => Meta (Meta::BuiltIn(_))
    | is_custom_attr => Meta (Meta::Custom(_))

}

impl Lexeme {
    /// Extracting the `Symbol` stored by a given `Lexeme`, if it contains one.
    /// This is to avoid having to pattern match over a lexeme for its `Symbol`
    /// when it is already known that a `Lexeme` contains a `Symbol`.
    #[inline]
    pub fn symbol(&self) -> Option<Symbol> {
        match self {
            Self::Lower(s)
            | Self::Upper(s)
            | Self::Infix(s)
            | Self::Label(s)
            | Self::Lit(Literal::Str(s)) => Some(*s),
            Self::Colon => Some(wy_intern::sym::COLON),
            _ => None,
        }
    }

    #[inline]
    pub fn ident_symbol(&self) -> Option<Symbol> {
        match self {
            Self::Lower(s) | Self::Upper(s) | Self::Infix(s) | Self::Label(s) => Some(*s),
            Self::Colon => Some(wy_intern::sym::COLON),
            _ => None,
        }
    }

    pub fn upper_symbol(&self) -> Option<Symbol> {
        if let Self::Upper(s) = self {
            Some(*s)
        } else {
            None
        }
    }
    pub fn lower_symbol(&self) -> Option<Symbol> {
        if let Self::Lower(s) = self {
            Some(*s)
        } else {
            None
        }
    }
    pub fn infix_symbol(&self) -> Option<Symbol> {
        match self {
            Self::Colon => Some(wy_intern::sym::COLON),
            Self::Infix(s) => Some(*s),
            _ => None,
        }
    }
    pub fn label_symbol(&self) -> Option<Symbol> {
        if let Self::Upper(s) = self {
            Some(*s)
        } else {
            None
        }
    }

    /// If the lexeme is an `Upper`, `Lower`, `Infix`, or `Label` variant, then
    /// applies the inner symbol to the identifier constructor function
    /// corresponding to *one* of the given an array of identifier constructor
    /// functions.
    ///
    /// Since the `token` module doesn't depend on the `wy_name` crate, and to
    /// allow for flexibility, this method does *not* constrain the return type
    /// of the above-mentioned constructor functions.
    #[inline]
    pub fn map_id<Id>(&self, [upper, lower, infix, label]: [fn(Symbol) -> Id; 4]) -> Option<Id> {
        match self {
            Self::Upper(s) => Some(upper(*s)),
            Self::Lower(s) => Some(lower(*s)),
            Self::Infix(s) => Some(infix(*s)),
            Self::Label(s) => Some(label(*s)),
            _ => None,
        }
    }

    /// Flipped and curried version of `map_identifier`, i.e., given an array of
    /// functions constructing the same generic `Id` type, returns another
    /// function taking a lexeme as input and returning as output the optional
    /// identifier from applying that lexeme's `map_identifier` method.
    #[inline]
    pub fn mk_id<Id>(constructors: [fn(Symbol) -> Id; 4]) -> impl Fn(&Lexeme) -> Option<Id> {
        move |this| Self::map_id(this, constructors)
    }

    #[inline]
    pub fn literal(&self) -> Option<Literal> {
        if let Self::Lit(lit) = self {
            Some(*lit)
        } else {
            None
        }
    }

    #[inline]
    pub fn info_kw(&self) -> bool {
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
                Keyword::Infix
                    | Keyword::InfixL
                    | Keyword::InfixR
                    | Keyword::Type
                    | Keyword::Class
                    | Keyword::Data
                    | Keyword::Fn
                    | Keyword::Impl
                    | Keyword::Newtype
                    | Keyword::Def
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

    #[inline]
    pub fn is_minus_sign(&self) -> bool {
        matches!(self, Lexeme::Infix(s) if *s == wy_intern::sym::MINUS)
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
            Lexeme::Unlabel => write!(f, "'_"),
            Lexeme::Tilde => write!(f, "~"),
            Lexeme::Lambda => write!(f, "\\"),
            Lexeme::At => write!(f, "@"),
            Lexeme::Pound => write!(f, "#"),
            Lexeme::Bang => write!(f, "!"),
            Lexeme::Hashbang => write!(f, "#!"),
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
            Lexeme::CurlyL => write!(f, "{{"),
            Lexeme::CurlyR => write!(f, "}}"),
            Lexeme::Kw(kw) => write!(f, "{}", kw),
            Lexeme::Upper(s) => write!(f, "{}", s),
            Lexeme::Lower(s) => write!(f, "{}", s),
            Lexeme::Infix(s) => write!(f, "{}", s),
            Lexeme::Label(s) => write!(f, "'{}", s),
            Lexeme::Lit(lit) => write!(f, "{}", lit),
            Lexeme::Meta(pr) => write!(f, "<PRAGMA: {:?}>", pr),
            Lexeme::Unknown(err) => write!(f, "<[INVALID]: {}>", err),
            Lexeme::Eof => write!(f, "<[EOF]>"),
        }
    }
}

impl AsRef<Lexeme> for Lexeme {
    fn as_ref(&self) -> &Lexeme {
        self
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
    /// Includes `LexKind::Upper`, `LexKind::Lower`, and `LexKind::Infix`
    Identifier,
    /// Identifiers beginning with an uppercase alphabetic character
    Upper,
    /// Identifiers beginning with a lowercase alphabetic character OR an
    /// underscore followed by AT LEAST one alphanumeric character
    Lower,
    /// Identifiers consisting of ascii symbols `~!@#$%%^&*-+:?/\\.<>=` with the
    /// exception of `->`, `<-`, `=`, `|`, `::`, `.`, `..`, and `@`
    Infix,
    /// Identifiers beginning with an apostrophe
    Label,
    /// The reserved symbols `->`, `<-`, `=`, `|`, `::`, `.`, `..`, and `@`
    Punct,
    /// An open or left delimiter, such as `(`, `[`, or `{`
    LeftDelim,
    /// An closing or right delimiter, such as `)`, `]`, or `}`
    RightDelim,
    /// A reserved identifier lexed as a `Keyword`.
    Keyword,
    /// A numeric, string, or character literal. This encompasses
    /// `LexKind::Number` and `LexKind::Character`
    Literal,
    /// A numeric literal
    Number,
    /// A character literal
    Character,
    /// A specific lexeme (as opposed to a general class of lexemes)
    Specified(Lexeme),
    /// Any of the listed specific lexemes
    AnyOf(&'static [LexKind]),
    Attribute,
}

impl LexKind {
    pub fn from_keyword(_: Keyword) -> Self {
        LexKind::Keyword
    }

    pub fn from_literal(lit: Literal) -> Self {
        match lit {
            Literal::Integral { .. } | Literal::Fractional { .. } => Self::Number,
            Literal::Char(_) | Literal::NullChar => Self::Character,
            Literal::Str(_) | Literal::EmptyStr => Self::Literal,
        }
    }

    pub fn from_lexeme(lexeme: Lexeme) -> Self {
        match lexeme {
            Lexeme::Underline
            | Lexeme::Tilde
            | Lexeme::Lambda
            | Lexeme::At
            | Lexeme::Pound
            | Lexeme::Bang
            | Lexeme::Equal
            | Lexeme::Comma
            | Lexeme::Semi
            | Lexeme::Dot
            | Lexeme::Dot2
            | Lexeme::Colon2
            | Lexeme::ArrowL
            | Lexeme::ArrowR
            | Lexeme::FatArrow
            | Lexeme::Pipe => Self::Punct,
            Lexeme::Hashbang => Self::Specified(Lexeme::Hashbang),
            Lexeme::ParenL | Lexeme::BrackL | Lexeme::CurlyL => Self::LeftDelim,
            Lexeme::ParenR | Lexeme::BrackR | Lexeme::CurlyR => Self::RightDelim,
            Lexeme::Kw(_) => Self::Keyword,
            Lexeme::Upper(_) => Self::Upper,
            Lexeme::Lower(_) => Self::Lower,
            Lexeme::Infix(_) | Lexeme::Colon => Self::Infix,
            Lexeme::Unlabel | Lexeme::Label(_) => Self::Label,
            Lexeme::Lit(_) => Self::Literal,
            Lexeme::Unknown(..) | Lexeme::Eof => Self::Specified(lexeme),
            Lexeme::Meta(..) => Self::Attribute,
        }
    }
}

impl<T> From<T> for LexKind
where
    T: PartialEq<Token>,
    Token: PartialEq<T>,
    Lexeme: From<T>,
{
    fn from(t: T) -> Self {
        Self::from_lexeme(t.into())
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
            LexKind::Label => {
                write!(f, "identifier prefixed with an apostrophe")
            }
            LexKind::Punct => write!(f, "punctuation"),
            LexKind::LeftDelim => write!(f, "left delimiter"),
            LexKind::RightDelim => write!(f, "right delimiter"),
            LexKind::Keyword => write!(f, "keyword"),
            LexKind::Literal => write!(f, "literal"),
            LexKind::Number => write!(f, "number"),
            LexKind::Character => write!(f, "character"),
            LexKind::Specified(lexeme) => write!(f, "{}", lexeme),
            LexKind::AnyOf(lexemes) => {
                assert!(
                    lexemes.len() > 1,
                    "LexKind::AnyOf requires at least 2 elements"
                );
                write!(f, "any of [{}", lexemes[0])?;
                for lex in &lexemes[1..] {
                    write!(f, ", {}", lex)?;
                }
                write!(f, "]")
            }
            LexKind::Attribute => write!(f, "attribute"),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Token<L = Lexeme> {
    pub lexeme: L,
    pub span: Span,
}

impl<L> Token<L> {
    pub fn spanned(self) -> Spanned<L> {
        Spanned(self.lexeme, self.span)
    }
}

impl<L> From<Token<L>> for Spanned<L> {
    fn from(token: Token<L>) -> Self {
        token.spanned()
    }
}

impl Token<Lexeme> {
    /// Utility method allowing for point-free closure application of `Lexeme`
    /// methods. This is helpful when wanting to transform an
    /// `Option<&Token<Lexeme>>` using a method on a `Lexeme` reference that
    /// *only* the
    /// lexeme receiver by reference as a parameter.
    pub fn lift<X>(f: impl Fn(&Lexeme) -> X) -> impl Fn(&Token) -> X {
        move |this| f(&this.lexeme)
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Token({})[{}]", &self.lexeme, &self.span)
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
        match (&self.lexeme, other) {
            (Lexeme::Colon, Lexeme::Infix(s)) | (Lexeme::Infix(s), Lexeme::Colon) => {
                *s == wy_intern::sym::COLON
            }
            (me, other) => me == other,
        }
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

/// Public interface used to generalize (or alternatively, specify
/// with greater detail) comparisons for type parameters `Tok` (which
/// defaults to `Token`) and `Lex` (which defaults to `Lexeme`) types.
/// This trait is generic in `Tok` and `Lex` to allow for extending
/// existing functionality without specifically requiring the lexemes
/// compared to be a concrete type.
///
/// For example, the `Tok` parameter may be set to `(X, T)` for some
/// `T` that also implements this trait, allowing extra data `X` to be
/// included with lexemes without requiring that extra data
/// specifically be derived from a lexeme.
///
/// Since a `Lexeme` may contain derivative types, such as `Keyword`
/// and `Literal` (all of which are comparable with `Token` and
/// `Lexeme` types), this trait trivially extends this functionality
/// to *non-derivative* types. A nontrivial example is that of types
/// `F` that implement `FnMut(Lex) -> bool`, which allows for
/// comparisons using predicates instead of just relying on
/// `PartialEq`.
///
/// The idea behind this trait is to allow for greater ergonomics in
/// applying predicates and in fact was inspired by the Rust
/// `Pattern<'a>` trait (not to be confused with other types in the
/// compiler named `Pattern`), which allows for comparison-based
/// functionality on string slices using characters, other string
/// slices, or character-valued predicates.
///
/// An example of a type that benefits from implementing this trait,
/// but that isn't a derivative type of `Token` or `Lexeme`
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

    fn is_eof(&self) -> bool
    where
        Lex: From<Lexeme> + PartialEq<Tok>,
        Tok: PartialEq<Lexeme>,
        Lexeme: PartialEq<Tok>,
    {
        self.compare(Lexeme::Eof)
    }
}

/// Wrapper allowing for predicates to be negated and passed around without
/// relying on closures.
pub struct Not<F>(pub F);

impl<F> Lexlike for Not<F>
where
    F: Lexlike,
{
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        !self.0.cmp_lex(lex)
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        !self.0.cmp_tok(tok)
    }
}

impl Lexlike for fn(Lexeme) -> bool {
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        self(*lex)
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self(tok.lexeme)
    }
}

impl Lexlike for fn(Token) -> bool {
    /// Note that a `Token` is constructed to feed into the function pointer for
    /// which this trait is implemented. In the constructed `Token`, a dummy
    /// span `Span::DUMMY` is used for the `span` field, but as this method
    /// compares *lexemes*, the given function may return a false positive!
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        self(Token {
            lexeme: *lex,
            span: Span::DUMMY,
        })
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self(*tok)
    }
}

impl Lexlike for fn(Option<&Token>) -> bool {
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        self(Some(&Token {
            lexeme: *lex,
            span: Span::DUMMY,
        }))
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self(Some(tok))
    }
}

impl Lexlike for fn(Option<&Lexeme>) -> bool {
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        self(Some(lex))
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self(Some(&tok.lexeme))
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

impl Lexlike for Meta {
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        matches!(lex, Lexeme::Meta(p) if p == self)
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        matches!(&tok.lexeme, Lexeme::Meta(p) if p == self)
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

impl<T, const N: usize> Lexlike for [T; N]
where
    T: Lexlike,
{
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        self.iter().any(|t| t.cmp_lex(lex))
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self.iter().any(|t| t.cmp_tok(tok))
    }
}

impl<T> Lexlike for &[T]
where
    T: Lexlike,
{
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        self.iter().any(|t| t.cmp_lex(lex))
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self.iter().any(|t| t.cmp_tok(tok))
    }
}

impl Lexlike for Symbol {
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        matches!(lex, Lexeme::Upper(s) | Lexeme::Lower(s) | Lexeme::Infix(s) if *self == *s)
            || (lex.is_kw()
                && matches!(Keyword::from_str(symbol::lookup(*self).as_str()), Some(kw) if kw.cmp_lex(lex)))
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self.cmp_lex(&tok.lexeme)
    }
}

impl<A, B> Lexlike for (A, B)
where
    A: Lexlike,
    B: Lexlike,
{
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        self.0.cmp_lex(lex) || self.1.cmp_lex(lex)
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self.0.cmp_tok(tok) || self.1.cmp_tok(tok)
    }
}

impl<A, B, C> Lexlike for (A, B, C)
where
    A: Lexlike,
    B: Lexlike,
    C: Lexlike,
{
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        self.0.cmp_lex(lex) || self.1.cmp_lex(lex) || self.2.cmp_lex(lex)
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self.0.cmp_tok(tok) || self.1.cmp_tok(tok) || self.2.cmp_tok(tok)
    }
}

impl<A, B, C, D> Lexlike for (A, B, C, D)
where
    A: Lexlike,
    B: Lexlike,
    C: Lexlike,
    D: Lexlike,
{
    fn cmp_lex(&self, lex: &Lexeme) -> bool {
        self.0.cmp_lex(lex) || self.1.cmp_lex(lex) || self.2.cmp_lex(lex) || self.3.cmp_lex(lex)
    }

    fn cmp_tok(&self, tok: &Token) -> bool {
        self.0.cmp_tok(tok) || self.1.cmp_tok(tok) || self.2.cmp_tok(tok) || self.3.cmp_tok(tok)
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
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
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
    /// * invalid due to space: `modulo`
    /// * invalid due to non-lowercase-initial* identifier `#`: `foo#`
    /// * invalid, `<>` is already an infix: `<>`
    UnterminatedInfix,
    /// Emitted when encountering a nondigit character (that isn't `b`, `B`,
    /// `o`, `O`, `x`, or `X`) after (the initial) `0` in a number beginning
    /// with `0`.
    InvalidIntPrefix,
    InvalidIntSuffix,
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
    /// Emitted when encountering a `0` followed by another (decimal) integer
    /// between `1` and `9`.
    NoLeadingZeroInt,
    /// Emitted when parsing a numeric literal to a Rust number fails
    MalformedNumber,
    /// Emitted when encountering the EOF after `~{` without a closing `}~`.
    UnterminatedComment,
    /// Emitted when encountering a closing bracket `[` after the
    /// opening bracket `[` within an attribute.
    EmptyPragma,
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
            LexError::InvalidIntSuffix => write!(f, "invalid integer suffix"),
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
            LexError::NoLeadingZeroInt => write!(f, "invalid leading 0 found in number"),
            LexError::MalformedNumber => write!(f, "malformed integer"),
            LexError::UnterminatedComment => write!(f, "block comment not terminated"),
            LexError::EmptyPragma => write!(f, "no pragma found within attribute"),
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
        (Lexeme::Infix(_) | Lexeme::Colon)
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
    ([def]) => {
        Lexeme::Kw(Keyword::Def)
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
    ([newtype]) => {
        Lexeme::Kw(Keyword::Newtype)
    };
}
