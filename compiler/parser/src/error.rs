use std::fmt;

pub use wy_failure;
use wy_failure::Dialogue;
pub use wy_failure::Failure;
pub use wy_failure::SrcLoc;
pub use wy_failure::SrcPath;

use wy_intern::Symbol;
use wy_intern::Symbolic;
use wy_lexer::token::LexKind;
use wy_lexer::token::Token;
use wy_lexer::LexError;
use wy_lexer::Lexeme;
use wy_name::ident::Ident;
use wy_name::Chain;
use wy_span::ranges::CoordSpan;
use wy_span::Coord;
use wy_span::Span;
use wy_span::Spanned;
use wy_span::WithCoordSpan;
use wy_span::WithLoc;
use wy_syntax::ast::respan::ReSpan;
use wy_syntax::fixity::Assoc;
use wy_syntax::fixity::Prec;

use SyntaxError::*;

pub trait Report: WithLoc {
    fn next_token(&mut self) -> Token;
    fn next_coord_span(&mut self) -> CoordSpan;
    fn current_coord(&self) -> Coord {
        self.get_coord()
    }
    fn unexpected_eof(&mut self) -> ParseError {
        let token = self.next_token();
        let coord = self.current_coord();
        ParseError::new(true, coord, token.span, UnexpectedEof, [])
    }
    fn report_error<X: Into<Evidence>>(
        &mut self,
        syntax_err: SyntaxError,
        token: Token,
        text_slots: impl IntoIterator<Item = (&'static str, X)>,
    ) -> ParseError {
        let coord = self.current_coord();
        ParseError::new(
            true,
            coord,
            token.span,
            syntax_err,
            text_slots.into_iter().map(|(s, x)| (s, x.into())), // .into_iter(),
        )
    }
    fn expected_token(&mut self, expected: impl Into<Evidence>) -> ParseError {
        let found = self.next_token();
        let coord = self.current_coord();
        ParseError::new(
            true,
            coord,
            found.span,
            ExpectedToken,
            [("", expected.into()), ("", Evidence::Tok(found))],
        )
    }

    fn custom_error(&mut self, token: Token, message: &'static str) -> ParseError {
        ParseError::new(
            false,
            self.current_coord(),
            token.span,
            Custom,
            [
                ("".into(), Evidence::Tok(token)),
                (message, Evidence::Empty),
            ],
        )
    }

    fn store_error(&mut self, error: ParseError);
}

pub trait TakeEvidence: Report {
    fn take_evidence(x: impl Into<Evidence>) -> Evidence {
        x.into()
    }
}

pub trait ReportPragma: TakeEvidence {
    fn empty_pragma(&mut self) -> ParseError {
        let token = self.next_token();
        ParseError::new(true, self.get_coord(), token.span, EmptyPragma, [])
    }
}

pub trait Expects: TakeEvidence {
    fn expected<L>(&mut self, expected: L, found: Token) -> ParseError
    where
        LexKind: From<L>,
    {
        let lexkind = LexKind::from(expected);
        ParseError::new(
            true,
            self.get_coord(),
            found.span,
            UnexpectedToken,
            [("", lexkind.into()), ("", found.into())],
        )
    }
    fn invalid_fn_ident(&mut self, token: Token) -> ParseError {
        let coord = self.get_coord();
        ParseError::new(
            true,
            coord,
            token.span,
            InvalidFnBindingName,
            [("", token.into())],
        )
    }

    fn invalid_type_start(&mut self, token: Token) -> ParseError {
        let tok = Evidence::Tok(token);
        self.report_error(ExpectedTypeStart, token, [("", tok)])
    }

    fn unbalanced_delim(&mut self, delim: Lexeme, found: Token) -> ParseError {
        let coord = self.get_coord();
        ParseError::new(
            true,
            coord,
            found.span,
            UnbalancedDelimiter,
            [("", delim.into()), ("", found.into())],
        )
    }

    fn unbalanced_paren(&mut self, token: Token) -> ParseError {
        self.unbalanced_delim(Lexeme::ParenR, token)
    }

    fn unbalanced_brack(&mut self, token: Token) -> ParseError {
        self.unbalanced_delim(Lexeme::BrackR, token)
    }

    fn unbalanced_curly(&mut self, token: Token) -> ParseError {
        self.unbalanced_delim(Lexeme::CurlyR, token)
    }

    fn invalid_fixity_prec(&mut self, token: Token) -> ParseError {
        self.report_error(InvalidFixityPrec, token, [("", token)])
    }

    fn fixity_exists(&mut self, infix: Ident, span: Span) -> ParseError {
        ParseError::new(
            true,
            self.get_coord(),
            span,
            FixityAlreadyDefined,
            [("", infix.into())],
        )
    }
}

pub trait ReportExpr: TakeEvidence {}

impl<T> TakeEvidence for T where T: Report {}
impl<T> ReportPragma for T where T: TakeEvidence {}
impl<P> Expects for P where P: TakeEvidence {}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SyntaxError {
    // finding a literal, tuple, range, list/list comprehension or
    // negation in the head (or "function position") of an app
    // expression, such as `(1 x)`, etc.
    CannotApplyNonCallable,
    // when a fixity decl or pragma includes `(:)`
    CannotModifyConsFixity,
    // when `(:)` is used as a binding name/identifier
    CannotRedefineConsInfix,
    Custom,
    DerivePragmaNameInWithClause,
    EmptyDoBlock,
    // foo :: || ... OR foo :: | | ..
    EmptyPragma,
    EmptyTypePredicate,
    ExpectedAsPatRhs,
    ExpectedClassName,
    ExpectedDeclKeyword,
    ExpectedExprStart,
    ExpectedFixityAssoc,
    ExpectedFixityPrec,
    // [e1, e2 | ... ]
    ExpectedListTailNotCompr,
    ExpectedMethodName,
    ExpectedPatStart,
    // (<op> e1, ...)
    ExpectedSectionNotTuple,
    ExpectedToken,
    // (e1)
    ExpectedTupleNotSection,
    ExpectedTypeSignature,
    ExpectedTypeStart,
    FixityExpectedInfix,
    FixityAlreadyDefined,
    IncompletePragma,
    // (->) a b
    InvalidArrowTyConArity,
    InvalidFixityPrec,
    // invalid identifier for top-level function definition, e.g. `fn
    // 4 :: ...`, i.e., function identifier not a lowercase ident or
    // infix ident
    InvalidFnBindingName,
    InvalidImport,
    // import module aliases must be Upper idents
    InvalidImportModuleAlias,
    // [] a b
    InvalidListTyConArity,
    // finding a comma after a list's inner type instead of a closing
    // bracket, e.g., foo:: [a, b] -> c
    InvalidListTypeComma,

    // invalid binding identifier for bindings introduced in
    // let-expressions or where-declarations
    InvalidLocalBindingName,
    InvalidModuleName,
    InvalidNegatedPattern,
    InvalidPattern,
    InvalidRecordConstructor,
    // pat <- pat,
    InvalidStatement,
    // (,) a b c
    // namely, `n` commas are seen and `m > n + 1` types are found to
    // follow in type argument position
    InvalidTupleTyConArity,
    InvalidTypePredicate,
    // a section must be one-sided; stacking sections requires
    // explicit grouping such that `(<op1> <e1> <op2>)` is invalid but
    // `(<op1> (<e1> <op2>))` and `((<op1> <e1>) <op2>)` are valid
    MultiSidedSection,
    NoExprEndingDoBlock,
    NoLitPatsInLambdas,
    // finding `..` outside of a record (field) pattern
    NoLoneDoubleDotPattern,
    NoOrPatsInLambdas,
    // no top level expressions when parsing a file/only allow top
    // level expressions in interactive/repl mode, i.e., when
    // `SrcPath` is a `Direct` variant
    NoTopLevelExprForModule,
    // a.b -> c
    // all type variables must be nonqualified/non-chained
    NoTyVarChains,
    // when a let-expression or where-decl binding doesnt have a name,
    // begins with a non-callable/applicable pattern, and is followed
    // by at leas one more pattern, e.g., `let (a, b) c = ...`
    NonCallablePatAppliedInBinding,
    // |Class (a (b c))|
    NonSimpleClassParameter,
    // type Foo a Bar baz = ...
    // data Foo a Bar baz = ...
    NonTyVarInSimpleType,
    NonUpperIdentInWithClause,
    // newtype Foo a = Foo Bar ...
    OnlyOneNewtypeConstructor,
    PragmaFixityAlreadyDefined,
    // [a, .. b]
    RangeFromThenToMissingThen,
    // [a, b .. c, d], or generally any instance of a `..` token found
    // in syntactic lists with more than 2 "elements"
    RangeNotIsolated,
    // [.. e]
    RangeWithoutStart,
    // variants with record syntax cannot admit additional type
    // arguments
    // data ... = ... | Foo { a :: A, b :: B } C | ...
    //                                         ^
    RecordVariantNotCurried,
    // in patterns, [a, ..]
    RecordWildcardInList,
    // fields may not follow wildcard/rest `..` in record patterns/exprs
    RecordWildcardNotLast,
    // a cons pattern beginning with or ending with the cons pattern
    // operator `(:)`, such as in `(:a)`, etc.
    NoPatternConsSections,
    // Simple types must not have type applications within each
    // position; after a tycon, `a b c` and `(a b c)` are fine but `(a
    // (b c))` are not
    SimpleTypeNotFlat,
    UnbalancedDelimiter,
    UnexpectedEof,
    UnexpectedKeywordInExpr,
    UnexpectedKeywordInPat,
    UnexpectedKeywordInType,
    UnexpectedRepeatedSeparator,
    // todo!: specialize
    UnexpectedToken,
    // incorrect: |Class a b c|
    // correct: |Class (a b c)|
    UngroupedClassParameter,
    // case <expr> of { pat :: Foo a -> <alt_body> ...
    // should be: case <expr> of { (pat :: Foo a) -> ...
    // or         case <expr> of { pat :: (Foo a) -> ... }
    UngroupedTypeCast,
    // ... | Foo a -> b | ... <- not fine
    // ... | Foo a | ... <- fine
    UngroupedVariantFuncTypeArg,
    // data Foo = Foo | Bar with A, B
    //                           ^^^^
    UngroupedWithClauseNames,
    // a -> forall ...
    UniversalQuantifierWithinType,
    UnknownLexeme,
    UnterminatedPragma,
    // in variants/selectors:
    //  Foo { name }  <- invalid/misssing separator `::`
    //  Foo { :: Baz } <- `::` is invalid/missing lhs
    //  Foo { name :: } <- invalid/missing rhs
    UnterminatedRecordSelector,
    WithClauseNameInDerivePragma,
}

impl SyntaxError {
    pub fn txt_count(&self) -> usize {
        self.text().0
    }

    pub fn text(&self) -> (usize, &'static [&'static str]) {
        match self {
            CannotApplyNonCallable => (1, &["cannot construct application expression with a non-functional expression type as the head"]),
            CannotModifyConsFixity => (1, &["the cons operator `(:)` is not accepted within fixity declarations"]),
            CannotRedefineConsInfix => (1, &["the cons operator `(:)` is not a valid function name"]),
            Custom => (0, &[]),
            DerivePragmaNameInWithClause => (2, &["the name ", " already exists in the associated with clause"]),
            EmptyDoBlock => (1, &["empty `do` block found"]),
            EmptyPragma => (1, &["unexpected end of pragma attribute body"]),
            EmptyTypePredicate => (1, &["no type predicates were found between the vertical pipes `|` preceding the type"]),
            ExpectedAsPatRhs => (2, &["expected a pattern for the `as` pattern right-hand side, but ", " does not begin a valid pattern"]),
            ExpectedClassName => (2, &["expected a class name, but found ", " which is not an uppercase-initial identifier"]),
            ExpectedDeclKeyword => (2, &["the token ", " does not begin a keyword: expected either `type`, `class`, `impl`, `fn`, `data`, or `newtype`"]),
            ExpectedExprStart => (2, &["the token ", " does not begin an expression; expected an uppercase identifier, lowercase identifier, literal, `(`, `[`, `\\`, or one of the keywords `let`, `if`, `case`, or `do`"]),
            ExpectedFixityAssoc => (1, &["expected a valid fixity associativity value, but found "]),
            ExpectedFixityPrec => (1, &["expected a valid fixity precedence value between 0 and 10, but found "]),
            ExpectedListTailNotCompr => (1, &["unexpected vertical pipe `|` found in list"]),
            ExpectedMethodName => (1, &["expected identifier beginning with lowercase letter or operator surrounded with parentheses for method name, but instead found "]),
            ExpectedPatStart => (2, &["expected an uppercase-initial identifier, lowercase initial identifier, `_`, literal, `(`, or `[`, but found ", " which does not begin a valid pattern"]),
            ExpectedSectionNotTuple => (2, &["unexpected comma `,` in operator section"]),
            ExpectedToken => (2, &["expected the token ", " but instead found "]),
            ExpectedTupleNotSection => (2, &["unexpected operator ", " in tuple"]),
            ExpectedTypeSignature => (1, &["expected type signature after `::`, but found "]),
            ExpectedTypeStart => (2, &["the token ", " does not begin a valid type"]),
            FixityExpectedInfix => (1, &["expected infix for fixity declaration, but instead found"]),
            FixityAlreadyDefined => (2, &["the operator ", " has already had its fixity defined"]),
            IncompletePragma => (2, &["missing arguments for ", " pragma, closing bracket `]` found"]),
            InvalidArrowTyConArity => (1, &["the arrow/function type constructor `(->)` accepts a max of two type arguments"]),
            InvalidFixityPrec => (2, &["the token ", " does not correspond to a valid fixity precedence value, which must be an integer between 0 and 10 (exclusive)"]),
            InvalidFnBindingName => (1, &["expected an operator surrounded in parentheses or an identifier beginning with a lowercase letter, but instead found "]),
            InvalidImport => (2, &["", " is not a valid import"]),
            InvalidImportModuleAlias => (2, &["expected a single identifier beginning with an uppercase letter, but found ", " which is not a valid alias for an imported module"]),
            InvalidListTyConArity =>(1, &["the list type constructor `[]` only accepts up to one type argument"]),
            InvalidListTypeComma => (1, &["unexpected comma within list type"]),
            InvalidLocalBindingName => (2, &["the token ", " does not form a valid identifier for a local (let/where) binding"]),
            InvalidModuleName => (2, &["the token ", " is not a valid module name; module names must begin with a capital ascii character"]),
            InvalidNegatedPattern => (2, &["found unexpected `-` in pattern beginning with ", " without surrounding parentheses; only numeric literals and comma delimited patterns may be negated without being wrapped in parentheses"]),
            InvalidPattern => (2, &["expected either an uppercase identifier, lowercase identifier, literal, `_`, `(` or `[`, but found ", ", which does not begin a valid pattern"]),
            InvalidRecordConstructor => (2, &["expected an identifier beginning with an uppercase or lowercase letter, but found ", " which is not a valid record constructor"]),
            InvalidStatement => (2, &["expected a pattern or expression, but instead found the token ", " which does not begin a valid statement"]),
            InvalidTupleTyConArity => (2, &["the n-tuple tupe constructor `(", ")` only accepts up to n+1 type arguments"]),
            InvalidTypePredicate => (1, &["invalid type predicate"]),
            MultiSidedSection => (1, &["operators found after `(` and before `)"]),
            NoExprEndingDoBlock => (1, &["`do` blocks must end with an expression"]),
            NoLitPatsInLambdas => (2, &["lambda arguments may not consist of literal patterns, but the literal ", " was found"]),
            NoLoneDoubleDotPattern => (1, &["patterns may only contain `..` if they are record patterns and `..` precedes the closing `}` brace"]),
            NoOrPatsInLambdas => (1, &["lambda arguments may not consist of `or` patterns"]),
            NoPatternConsSections => (1, &["the cons operator `(:)` requires arguments on both sides within patterns"]),
            NoTopLevelExprForModule => (1, &["top-level expressions are only accepted in interactive mode; expected one of the declaration keywords `infix`, `infixl`, `infixr`, `type`, `data`, `newtype`, `fn`, `class` or `impl`, but found "]),
            NoTyVarChains => (1, &["type variables cannot be qualified"]),
            NonCallablePatAppliedInBinding => (1, &["bindings lacking binder names and beginning with compound patterns must be followed by `=`"]),
            NonSimpleClassParameter => (2, &["class predicate parameters may only be type variables, but found "]),
            NonTyVarInSimpleType => (1, &["expected a type variable, but found "]),
            NonUpperIdentInWithClause => (1, &["only identifiers beginning with an uppercase ascii letter are accepted within `with`-clauses"]),
            OnlyOneNewtypeConstructor => (1, &["newtype constructors may only have a single constructor"]),
            PragmaFixityAlreadyDefined => (2, &["the operator ", " has already had a fixity defined"]),
            RangeFromThenToMissingThen => (1, &["(in/de)cremented range expression missing expression before `..`"]),
            RangeNotIsolated => (1, &["range expressions without square brackets may not appear as elements in a nonempty list"]),
            RangeWithoutStart => (1, &["all range expressions must have a start, but found `[..`"]),
            RecordVariantNotCurried => (1, &["data variants using record syntax may not accept further type arguments"]),
            RecordWildcardInList => (1, &["then token `..` is only allowed at the end of records"]),
            RecordWildcardNotLast => (1, &["record fields may not follow the record wildcard `..`"]),
            SimpleTypeNotFlat => (1, &["expected at least 0 consecutive type variables with no groupings, but found "]),
            UnbalancedDelimiter => (2, &["expected closing delimiter ", " but instead found "]),
            UnexpectedEof => (1, &["unexpected end of input"]),
            UnexpectedKeywordInExpr => (2, &["unexpected keyword ", " found in expression"]),
            UnexpectedKeywordInPat => (2, &["unexpected keyword ", " found in pattern"]),
            UnexpectedKeywordInType => (2, &["unexpected keyword ", " found in type"]),
            UnexpectedRepeatedSeparator => (2, &["unexpected separator ", " found; empty items in collections or sequences are not allowed"]),
            UnexpectedToken => (2, &["unexpected token ", " found"]),
            UngroupedClassParameter => (1, &["higher order class paremeters must be wrapped in parentheses"]),
            UngroupedTypeCast => (1, &["casting with `::` may only be done within parentheses"]),
            UngroupedVariantFuncTypeArg => (1, &["function types must be wrapped in parentheses when included as type parameters for data variants"]),
            UngroupedWithClauseNames => (1, &["unexpected `,` in with-clause; multiple class names must be wrapped in parentheses"]),
            UniversalQuantifierWithinType => (1, &["unexpected keyword `forall` found within type"]),
            UnknownLexeme => (1, &["unexpected lexer error for invalid or unknown lexeme"]),
            UnterminatedPragma => (1, &["pragma not terminated with `]`"]),
            UnterminatedRecordSelector => (2, &["expected `}` for record selector, but found "]),
            WithClauseNameInDerivePragma => (2, &["the identifier ", " has already been included in a `derive` pragma"]),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Evidence {
    Empty,
    Tok(Token),
    Lex(Lexeme),
    LexKind(LexKind),
    LexErr(LexError),
    Symbol(Symbol),
    Chain(Chain),
    Assoc(Assoc),
    Prec(Prec),
    Str(&'static str),
}

impl From<()> for Evidence {
    fn from(_: ()) -> Self {
        Evidence::Empty
    }
}

impl From<Token> for Evidence {
    fn from(token: Token) -> Self {
        Evidence::Tok(token)
    }
}

impl From<Lexeme> for Evidence {
    fn from(lexeme: Lexeme) -> Self {
        Evidence::Lex(lexeme)
    }
}

impl From<Symbol> for Evidence {
    fn from(s: Symbol) -> Self {
        Evidence::Symbol(s)
    }
}

impl From<Ident> for Evidence {
    fn from(s: Ident) -> Self {
        Evidence::Symbol(s.get_symbol())
    }
}

impl From<LexKind> for Evidence {
    fn from(lk: LexKind) -> Self {
        Evidence::LexKind(lk)
    }
}

impl From<Chain> for Evidence {
    fn from(chain: Chain) -> Self {
        Evidence::Chain(chain)
    }
}

impl From<Chain<Spanned<Ident>>> for Evidence {
    fn from(chain: Chain<Spanned<Ident>>) -> Self {
        Evidence::Chain(chain.map(Spanned::take_item))
    }
}

impl From<Prec> for Evidence {
    fn from(prec: Prec) -> Self {
        Evidence::Prec(prec)
    }
}

impl From<Assoc> for Evidence {
    fn from(assoc: Assoc) -> Self {
        Evidence::Assoc(assoc)
    }
}

impl fmt::Display for Evidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Evidence::Empty => Ok(()),
            Evidence::Tok(t) => write!(f, "`{}`", &t.lexeme),
            Evidence::Lex(l) => write!(f, "`{l}`"),
            Evidence::LexKind(l) => write!(f, "{l}"),
            Evidence::LexErr(e) => write!(f, "{e}"),
            Evidence::Symbol(s) => write!(f, "`{s}`"),
            Evidence::Chain(c) => write!(f, "`{}`", c.printable()),
            Evidence::Assoc(a) => write!(f, "{a}"),
            Evidence::Prec(p) => write!(f, "{}", p.0),
            Evidence::Str(s) => write!(f, "{s}"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TextSlots<S = &'static str> {
    Zero,
    One([(S, Evidence); 1]),
    Two([(S, Evidence); 2]),
    Three([(S, Evidence); 3]),
    Many(Vec<(S, Evidence)>),
}

impl<S> Default for TextSlots<S> {
    fn default() -> Self {
        Self::Zero
    }
}

impl<S> TextSlots<S> {
    pub fn is_empty(&self) -> bool {
        matches!(self, Self::Zero) || self.len() == 0
    }

    pub fn len(&self) -> usize {
        match self {
            TextSlots::Zero => 0,
            TextSlots::One(_) => 1,
            TextSlots::Two(_) => 2,
            TextSlots::Three(_) => 3,
            TextSlots::Many(m) => m.len(),
        }
    }

    pub fn as_slice(&self) -> &[(S, Evidence)] {
        match self {
            TextSlots::Zero => &[],
            TextSlots::One(one) => one,
            TextSlots::Two(two) => two,
            TextSlots::Three(three) => three,
            TextSlots::Many(many) => many.as_slice(),
        }
    }

    pub fn push(&mut self, pair: (S, Evidence)) {
        match std::mem::take(self) {
            TextSlots::Zero => *self = TextSlots::One([pair]),
            TextSlots::One([one]) => *self = TextSlots::Two([one, pair]),
            TextSlots::Two([one, two]) => *self = TextSlots::Three([one, two, pair]),
            TextSlots::Three([one, two, three]) => {
                *self = TextSlots::Many(vec![one, two, three, pair])
            }
            TextSlots::Many(many) => {
                *self = TextSlots::Many(many.into_iter().chain([pair]).collect())
            }
        }
    }

    pub fn to_vec(self) -> Vec<(S, Evidence)> {
        match self {
            TextSlots::Zero => vec![],
            TextSlots::One([one]) => vec![one],
            TextSlots::Two([one, two]) => vec![one, two],
            TextSlots::Three([one, two, three]) => vec![one, two, three],
            TextSlots::Many(many) => many,
        }
    }
}

impl<S> IntoIterator for TextSlots<S> {
    type Item = (S, Evidence);

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.to_vec().into_iter()
    }
}

impl<S> std::ops::Index<usize> for TextSlots<S> {
    type Output = (S, Evidence);

    fn index(&self, index: usize) -> &Self::Output {
        &self.as_slice()[index]
    }
}

impl<S> std::ops::Index<std::ops::Range<usize>> for TextSlots<S> {
    type Output = [(S, Evidence)];

    fn index(&self, index: std::ops::Range<usize>) -> &Self::Output {
        &self.as_slice()[index]
    }
}

impl<S> std::ops::Index<std::ops::RangeFrom<usize>> for TextSlots<S> {
    type Output = [(S, Evidence)];

    fn index(&self, index: std::ops::RangeFrom<usize>) -> &Self::Output {
        &self.as_slice()[index]
    }
}

impl<S> FromIterator<(S, Evidence)> for TextSlots<S> {
    fn from_iter<I: IntoIterator<Item = (S, Evidence)>>(iter: I) -> Self {
        iter.into_iter().fold(TextSlots::Zero, |a, c| match a {
            TextSlots::Zero => TextSlots::One([c]),
            TextSlots::One([one]) => TextSlots::Two([one, c]),
            TextSlots::Two([one, two]) => TextSlots::Three([one, two, c]),
            TextSlots::Three([one, two, three]) => TextSlots::Many(vec![one, two, three]),
            TextSlots::Many(many) => TextSlots::Many(many.into_iter().chain([c]).collect()),
        })
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
#[derive(Clone, PartialEq, Eq)]
pub struct ParseError<S = &'static str> {
    pub print_kind: bool,
    pub coord_span: CoordSpan,
    pub syntax_err: SyntaxError,
    pub text_slots: TextSlots<S>,
}

impl<S> ParseError<S>
where
    S: fmt::Display,
{
    pub fn new(
        print_kind: bool,
        coord: Coord,
        span: Span,
        syntax_err: SyntaxError,
        text_slots: impl IntoIterator<Item = (S, Evidence)>,
    ) -> Self {
        ParseError {
            print_kind,
            coord_span: CoordSpan { coord, span },
            syntax_err,
            text_slots: text_slots.into_iter().collect(),
        }
    }

    pub fn err<X>(self) -> Result<X, Self> {
        Err(self)
    }

    pub fn label(&self) -> String {
        format!("{:?}:", &self.syntax_err)
    }

    pub fn message(&self) -> Result<String, std::fmt::Error> {
        use std::fmt::Write;
        let mut buf = String::new();
        let (cnt, txt) = self.syntax_err.text();
        for (msg, (s, evidence)) in txt.into_iter().zip(self.text_slots.as_slice()) {
            write!(buf, "{msg}{s}{evidence}")?;
        }
        if cnt > 0 && cnt == self.text_slots.len() + 1 {
            write!(buf, "{}", &txt[cnt - 1])?;
        }
        if cnt < self.text_slots.len() {
            for (s, ev) in &self.text_slots[cnt..] {
                write!(buf, "{s}{ev}")?;
            }
        }
        Ok(buf)
    }
}

impl<S> ReSpan for ParseError<S> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        vec![&mut self.coord_span.span]
    }
}

impl<S: fmt::Display, X> From<ParseError<S>> for Result<X, ParseError<S>> {
    fn from(e: ParseError<S>) -> Self {
        Err(e)
    }
}

impl<S> WithCoordSpan for ParseError<S>
where
    S: fmt::Display,
{
    fn get_coord_span(&self) -> CoordSpan {
        self.coord_span
    }
}

impl<S> fmt::Display for ParseError<S>
where
    S: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.print_kind {
            write!(f, "[{:?}]: ", &self.syntax_err)?;
        }
        let (cnt, txt) = self.syntax_err.text();
        for (msg, (s, evidence)) in txt.into_iter().zip(self.text_slots.as_slice()) {
            write!(f, "{msg}{s}{evidence}")?;
        }
        if cnt > 0 && cnt == self.text_slots.len() + 1 {
            write!(f, "{}", &txt[cnt - 1])?;
        }
        if cnt < self.text_slots.len() {
            for (s, ev) in &self.text_slots[cnt..] {
                write!(f, "{s}{ev}")?;
            }
        }
        write!(f, " on line {}, column {}", self.get_row(), self.get_col())?;

        Ok(())
    }
}

impl<S: std::fmt::Display> std::fmt::Debug for ParseError<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct ParserErrors<S = &'static str>(Vec<ParseError<S>>)
where
    S: fmt::Display;
impl<S> Default for ParserErrors<S>
where
    S: fmt::Display,
{
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<S> ParserErrors<S>
where
    S: fmt::Display,
{
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn first_span(&self) -> Option<Span> {
        self.0.first().map(WithCoordSpan::get_span)
    }

    pub fn last_span(&self) -> Option<Span> {
        self.0.last().map(WithCoordSpan::get_span)
    }

    pub fn as_slice(&self) -> &[ParseError<S>] {
        self.0.as_slice()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, ParseError<S>> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, ParseError<S>> {
        self.0.iter_mut()
    }

    pub fn push(&mut self, error: ParseError<S>) {
        self.0.push(error)
    }
}

impl<S: fmt::Display> ReSpan for ParserErrors<S> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        self.iter_mut()
            .flat_map(|pe| pe.spans_mut())
            .collect::<Vec<_>>()
    }
}

#[derive(Clone, PartialEq)]
pub struct ParseFailure<S: std::fmt::Display = &'static str> {
    pub srcpath: SrcPath,
    pub source: String,
    pub errors: ParserErrors<S>,
}

impl<S: std::fmt::Display> ParseFailure<S> {
    pub fn with_srcpath_root<P: AsRef<std::path::Path>>(self, root: P) -> Self {
        let ParseFailure {
            srcpath,
            source,
            errors,
        } = self;
        let srcpath = match srcpath {
            SrcPath::File(file) => SrcPath::Short {
                root: root.as_ref().to_path_buf(),
                file,
            },
            p => p,
        };
        ParseFailure {
            srcpath,
            source,
            errors,
        }
    }
}

impl<S: fmt::Display> ReSpan for ParseFailure<S> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        self.errors.spans_mut()
    }
}

impl<S: std::fmt::Display> std::fmt::Display for ParseFailure<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let srcpath = &self.srcpath;
        let srctext = &self.source;
        for error in self.errors.as_slice() {
            let label = error.label();
            let message = error.message()?;
            let coordspan = error.coord_span;
            let span = coordspan.span();
            let srcloc = SrcLoc {
                coord: coordspan.coord(),
                pathstr: srcpath.borrowed(),
            };

            Dialogue::new(label.as_str(), message, srctext, &srcloc, span).display(f)?;
        }
        Ok(())
    }
}

impl<S: std::fmt::Display> std::fmt::Debug for ParseFailure<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self)
    }
}

pub type ParseResult<X, S = &'static str> = Result<X, ParseFailure<S>>;
