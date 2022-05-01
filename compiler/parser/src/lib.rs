use std::rc::Rc;

use lexer::*;
use span::{Dummy, WithLoc, WithSpan};
use syntax::{
    fixity::{Assoc, Fixity, FixityTable, Prec},
    tipo::{Field, Record, Tv, Type},
    AliasDecl, Alternative, Arity, Binding, ClassDecl, Context, DataDecl,
    Declaration, Expression, FixityDecl, FnDecl, Ident, Import, ImportDecl,
    InstDecl, Match, Module, Pattern, Program, Signature, Statement, Variant,
};
use token::*;
use wy_common::Deque;
use wy_lexer as lexer;
use wy_span as span;
use wy_syntax as syntax;

pub fn next_token_with_location<'t>(
    lexer: &'t mut Lexer,
) -> span::Located<lexer::Token> {
    lexer.with_loc(Lexer::token)
}

pub trait Streaming {
    type Peeked;
    fn peek(&mut self) -> Option<&Self::Peeked>;
    fn bump(&mut self) -> Self::Peeked;
    fn is_done(&mut self) -> bool;
}

pub trait Parse: Streaming {
    type Lexeme: PartialEq<Self::Peeked>;
    type Err: std::error::Error;

    fn eat<T>(
        &mut self,
        item: impl PartialEq<Self::Lexeme>,
    ) -> Result<Coord, Self::Err>;
    /// Given a predicate `pred` and a parser, applies the given parser `parse`
    /// repeatedly as long as the predicate returns `true` and returning the
    /// results in a vector.
    ///
    /// This method will always check the predicate prior to running
    /// the given parser.
    ///
    /// **Note:** the given predicate *must* be coercible to
    /// `fn` pointer, and hence **must not** capture any variables.
    fn many_while<F, G, X>(
        &mut self,
        mut pred: G,
        mut f: F,
    ) -> Result<Vec<X>, Self::Err>
    where
        G: FnMut(&mut Self) -> bool,
        F: FnMut(&mut Self) -> Result<X, Self::Err>,
    {
        let mut xs = vec![];
        let mut go = pred(self);
        while go {
            xs.push(f(self)?);
            go = pred(self);
        }
        Ok(xs)
    }
}

/// Describing the source path and position, primarily used in error reporting.
/// This should be included in every error message to be able to reproduce
/// tracking information regarding the source code involved during error
/// reporting.
///
/// This struct should effectively be able to produce a string of the form
/// ```txt
///         [PATH/TO/FILE]:[ROW][COL]
/// ```
/// in error messages.
#[derive(Clone, PartialEq)]
pub struct SrcLoc {
    pub pathstr: Option<String>,
    pub coord: Coord,
}

impl std::fmt::Display for SrcLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref s) = self.pathstr {
            write!(f, "{}", s)
        } else {
            write!(f, "<INTERACTIVE>")
        }?;
        // include only starting coordinates?
        write!(f, ":{}", self.coord)
    }
}

impl std::fmt::Debug for SrcLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // same as `Display`
        write!(f, "{}", self)
    }
}

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
#[derive(Clone, Debug, PartialEq)]
pub enum ParseError {
    UnexpectedEof(SrcLoc),
    Expected(SrcLoc, LexKind, Token),
    InvalidLexeme(SrcLoc, Token),
    InvalidPrec(SrcLoc, Token),
    FixityExists(SrcLoc, Token),
    BadContext(SrcLoc, Ident, Span),
    Custom(SrcLoc, Token, &'static str),
    Unbalanced {
        srcloc: SrcLoc,
        found: Token,
        delim: Lexeme,
    },
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::UnexpectedEof(_) => write!(f, "Unexpected EOF"),
            ParseError::Expected(..) => todo!(),
            ParseError::InvalidLexeme(..) => todo!(),
            ParseError::InvalidPrec(..) => todo!(),
            ParseError::FixityExists(..) => todo!(),
            ParseError::Custom(..) => todo!(),
            ParseError::BadContext(..) => todo!(),
            ParseError::Unbalanced {
                srcloc,
                found,
                delim,
            } => todo!(),
        }
    }
}

impl std::error::Error for ParseError {}

pub type Parsed<X> = Result<X, ParseError>;

#[derive(Debug)]
pub struct Parser<'t> {
    lexer: Lexer<'t>,
    queue: Deque<Token>,
    pub fixities: FixityTable,
    pub filepath: Option<std::path::PathBuf>,
}

impl<'t> WithSpan for Parser<'t> {
    fn get_pos(&self) -> BytePos {
        self.lexer.get_pos()
    }
}

impl<'t> WithLoc for Parser<'t> {
    fn get_loc(&self) -> Coord {
        self.lexer.get_loc()
    }
}

impl<'t> Parser<'t> {
    pub fn with_lexer(lexer: Lexer<'t>) -> Self {
        Self {
            lexer,
            filepath: None,
            queue: Deque::new(),
            fixities: FixityTable::new(Ident::Infix),
        }
    }

    pub fn from_str(src: &'t str) -> Self {
        Self {
            lexer: Lexer::new(src),
            filepath: None,
            queue: Deque::new(),
            fixities: FixityTable::new(Ident::Infix),
        }
    }

    pub fn peek(&mut self) -> Option<&Token> {
        if let Some(t) = self.queue.front() {
            Some(t)
        } else {
            self.lexer.peek()
        }
    }

    /// Advance the underlying stream of tokens, retuning the unwrapped result
    /// of `Lexer::next`. If `Lexer::next` returns `None`, then the token
    /// corresponding to the `EOF` lexeme is returned.
    ///
    /// Note that this method first checks the internal lexeme queue before
    /// calling the lexer. If the buffer is non-empty, it simply pops the next
    /// element from the front of the qeueue.
    pub fn bump(&mut self) -> Token {
        if let Some(token) = self.queue.pop_front() {
            return token;
        }
        self.lexer.bump()
    }

    /// Shortcut for branching based on the current lexeme. Given a lexeme, this
    /// will check if the current token is a match and return the (boolean)
    /// result. However, if the result is true, it performs the side effect of
    /// calling `bump` before returning the `true`, combining the pattern `if
    /// self.on_lexeme(..) { self.bump(); ... }`.
    ///
    /// Note that this *discards* the lexeme if a match occurs.
    fn bump_on(&mut self, lexeme: Lexeme) -> bool {
        let on_it = self.on_lexeme(lexeme);
        if on_it {
            self.bump();
        }
        on_it
    }

    pub fn get_srcloc(&mut self) -> SrcLoc {
        let pathstr = self
            .filepath
            .as_ref()
            .and_then(|p| p.to_str())
            .map(String::from);
        let coord = self.lexer.get_loc();
        SrcLoc { pathstr, coord }
    }

    pub fn eat<T>(&mut self, item: T) -> Parsed<Token>
    where
        T: PartialEq<Token>,
        Token: PartialEq<T>,
    {
        match self.peek() {
            Some(t) if &item == t => Ok(self.bump()),
            Some(t) => {
                let tok = t.clone();
                let src_loc = self.get_srcloc();
                Err(ParseError::Expected(
                    src_loc,
                    LexKind::from(tok.lexeme),
                    tok,
                ))
            }
            None => Err(ParseError::UnexpectedEof(self.get_srcloc())),
        }
    }

    pub fn is_done(&mut self) -> bool {
        match self.peek() {
            Some(t) if t.lexeme.is_eof() => true,
            None => true,
            _ => false,
        }
    }

    pub fn ignore<T>(&mut self, item: T)
    where
        T: PartialEq<Token>,
        Token: PartialEq<T>,
    {
        match self.peek() {
            Some(t) if t == &item => {
                self.bump();
            }
            _ => {}
        }
    }

    pub fn on_lexeme(&mut self, lexeme: Lexeme) -> bool {
        matches!(self.peek(), Some(t) if t.lexeme == lexeme)
    }

    pub fn test_lexeme(&mut self, pred: impl Fn(&Lexeme) -> bool) -> bool {
        matches!(
            self.peek().map(|Token { lexeme, .. }| pred(lexeme)),
            Some(true)
        )
    }

    pub fn lookahead<const N: usize>(&mut self) -> [Token; N] {
        let mut array = [Token {
            lexeme: Lexeme::Eof,
            span: Span::DUMMY,
        }; N];
        for arr in &mut array {
            let token = self.bump();
            *arr = token;
            self.queue.push_back(token);
        }
        array
    }

    pub fn delimited<F, X>(
        &mut self,
        [start, mid, end]: [Lexeme; 3],
        mut f: F,
    ) -> Parsed<Vec<X>>
    where
        F: FnMut(&mut Self) -> Parsed<X>,
    {
        let mut nodes = vec![];
        let mut first = true;
        self.eat(start)?;
        while !self.is_done() {
            if self.on_lexeme(end) {
                break;
            }
            if first {
                first = false;
            } else {
                self.eat(mid)?;
            }
            if self.on_lexeme(end) {
                break;
            }
            nodes.push(f(self)?);
        }
        self.eat(end)?;
        Ok(nodes)
    }

    pub fn many_while<F, G, X>(
        &mut self,
        mut pred: G,
        mut f: F,
    ) -> Parsed<Vec<X>>
    where
        G: FnMut(&mut Self) -> bool,
        F: FnMut(&mut Self) -> Parsed<X>,
    {
        let mut xs = vec![];
        let mut go = pred(self);
        while go {
            xs.push(f(self)?);
            go = pred(self);
        }
        Ok(xs)
    }
}

macro_rules! expect_ident {
    ($self:ident $idkind:ident) => {{
        let srcloc = $self.get_srcloc();
        let tok = $self.bump();
        if let Lexeme::$idkind(s) = tok.lexeme {
            Ok(Ident::$idkind(s))
        } else {
            Err(ParseError::Expected(srcloc, LexKind::from(tok.lexeme), tok))
        }
    }};
}

// IDENTIFIERS AND LITERAL
impl<'t> Parser<'t> {
    fn expect_upper(&mut self) -> Parsed<Ident> {
        expect_ident!(self Upper)
    }
    fn expect_lower(&mut self) -> Parsed<Ident> {
        expect_ident!(self Lower)
    }
    fn expect_infix(&mut self) -> Parsed<Ident> {
        expect_ident!(self Infix)
    }
    fn expect_literal(&mut self) -> Parsed<Literal> {
        let srcloc = self.get_srcloc();
        let tok = self.bump();
        if let Lexeme::Lit(lit) = tok.lexeme {
            Ok(lit)
        } else {
            Err(ParseError::Expected(srcloc, LexKind::Literal, tok))
        }
    }
}

// TOP-LEVEL
impl<'t> Parser<'t> {
    pub fn module() -> Module {
        todo!()
    }
    fn import() -> ImportDecl {
        todo!()
    }
    fn import_listing() -> Import {
        todo!()
    }
    fn parse() -> Program {
        todo!()
    }
}

// FIXITY DECLARATIIONS
impl<'t> Parser<'t> {
    fn fixity_assoc(&mut self) -> Parsed<Assoc> {
        let srcloc = self.get_srcloc();
        let tok = self.bump();
        match tok.lexeme {
            lexpat!([infix]) => Ok(Assoc::None),
            lexpat!([infixl]) => Ok(Assoc::Left),
            lexpat!([infixr]) => Ok(Assoc::Right),
            _ => Err(ParseError::Custom(
                srcloc,
                tok,
                "Expected fixity keyword `infix`, `infixl`, or `infixr`",
            )),
        }
    }
    fn fixity_prec(&mut self) -> Parsed<Prec> {
        let srcloc = self.get_srcloc();
        let tok = self.bump();
        let prec = if let Lexeme::Lit(Literal::Int(p)) = tok.lexeme {
            if p < 10 {
                Ok(Prec(p as u8))
            } else {
                Err(ParseError::InvalidPrec(srcloc, tok))
            }
        } else {
            Err(ParseError::InvalidPrec(srcloc, tok))
        }?;
        Ok(prec)
    }

    fn with_fixity(&mut self, fixity: Fixity) -> Parsed<Vec<Ident>> {
        self.many_while(
            |p| p.test_lexeme(Lexeme::is_eof),
            |p| {
                let srcloc = p.get_srcloc();
                let tok = p.bump();
                if let Token {
                    lexeme: Lexeme::Infix(infix),
                    ..
                } = tok
                {
                    let infix = Ident::Infix(infix);
                    if p.fixities.contains_key(&infix) {
                        Err(ParseError::FixityExists(srcloc, tok))
                    } else {
                        p.fixities.insert(infix, fixity);
                        Ok(infix)
                    }
                } else {
                    Err(ParseError::Expected(srcloc, LexKind::Infix, tok))
                }
            },
        )
    }
}

// DECLARATIONS
impl<'t> Parser<'t> {
    pub fn declaration(&mut self) -> Parsed<Declaration> {
        match self.peek() {
            lexpat!(maybe[infixl][infixr][infix]) => {
                self.fixity_decl().map(Declaration::Fixity)
            }
            lexpat!(maybe[data]) => self.data_decl().map(Declaration::Data),
            lexpat!(maybe[fn]) => {
                self.function_decl().map(Declaration::Function)
            }
            lexpat!(maybe[type]) => self.alias_decl().map(Declaration::Alias),
            lexpat!(maybe[class]) => self.class_decl().map(Declaration::Class),
            lexpat!(maybe[impl]) => self.inst_decl().map(Declaration::Instance),
            _ => todo!(),
        }
    }
    fn fixity_decl(&mut self) -> Parsed<FixityDecl> {
        let assoc = self.fixity_assoc()?;
        let prec = self.fixity_prec()?;
        let fixity = Fixity { prec, assoc };
        let infixes = self.with_fixity(fixity)?;
        Ok(FixityDecl { infixes, fixity })
    }
    fn data_decl(&mut self) -> Parsed<DataDecl> {
        todo!()
    }
    fn function_decl(&mut self) -> Parsed<FnDecl> {
        todo!()
    }
    fn alias_decl(&mut self) -> Parsed<AliasDecl> {
        todo!()
    }
    fn class_decl(&mut self) -> Parsed<ClassDecl> {
        todo!()
    }
    fn inst_decl(&mut self) -> Parsed<InstDecl> {
        todo!()
    }
}

// DATA TYPES
impl<'t> Parser<'t> {
    fn data_variant(&mut self) -> Parsed<Variant> {
        self.ignore(Lexeme::Pipe);
        // constructor name
        let name = self.expect_upper()?;
        let mut args = vec![];
        while !(self.is_done() || lexpat!(self on [;] | [|] | [kw])) {
            args.push(self.type_signature()?);
        }
        let arity = Arity::from_len(args.as_slice());
        Ok(Variant { name, args, arity })
    }
}

// TYPES TODO: refactor to differentiate between TYPEs (type only) and
// SIGNATURES (context + type)
impl<'t> Parser<'t> {
    /// This method parses a total type signature, i.e., everythin on the
    /// right-hand side of the lexeme `::`.
    ///
    /// Note: a total signature is only allowed in top-level declarations
    /// (namely, class and instance delcarations, as well as in the type
    /// signature of function declarations). It is illegal for a type to contain
    /// any type constraints in a cast expression or in data declaration
    /// constructor arguments.
    fn total_signature(&mut self) -> Parsed<Signature> {
        let mut ctxt = vec![];
        if lexpat!(self on [|]) {
            ctxt = self.delimited(
                [Lexeme::Pipe, Lexeme::Comma, Lexeme::Pipe],
                Self::type_context,
            )?;
            self.ignore(Lexeme::FatArrow);
        };
        let tipo = self.type_signature()?;
        Ok(Signature { ctxt, tipo })
    }

    /// A context is syntactically simple, yet restrictive, as it must be of the
    /// form `Lexeme::Upper Lexeme::Lower`, where the underlying `u32` value
    /// contained by the lowercase identifier is shared into a `Tv`. This is
    /// because typeclass constraints only accept (free) type variables! The
    /// only case in which a typeclass may precede a non-type variable is in
    /// instance declarations, which are *not* syntactically considered
    /// "contexts".
    ///
    /// Note that this has the effect of mangling the name of the constrained
    /// type variable (as well as that of any lowercase identifiers in the
    /// `Type`), and is therefore motivation for *normalizing* the type
    /// variables of a given type signature prior to finalization.
    ///
    /// For example, suppose the lowercase identifier `car` corresponds to a
    /// `Symbol` wrapping the (for this example, arbitrarily chosen) integer
    /// `11`. When displayed, the `Symbol(11)` is printed as `car`. However, the
    /// type variable `Tv(11)` containing the same value would be rendered as
    /// `k`. Since all lowercase identifiers *must* be type variables in a
    /// `Type` signature, then there is no issue in re-interpreting the `Symbol`
    /// as a `Tv`. However, this proves to be an *one-way transformation*, as
    /// `Symbol`s cannot be reconstructed (as they are *only* produced by the
    /// string interner). In order to simplify type variable representation --
    /// and since the *actual* string representation of a type variable is
    /// itself irrelevant -- a type is *normalized* upon completion, such that a
    /// type `(uvw, xyz)` has its type variables remaped to `(a, b)`.
    fn type_context(&mut self) -> Parsed<Context> {
        let class = self.expect_upper()?;
        let tyvar = self.expect_lower().map(|id| Tv::from(id.get_symbol()))?;
        Ok(Context { class, tyvar })
    }

    fn type_signature(&mut self) -> Parsed<Type> {
        let ty = self.ty_atom()?;
        if self.is_done() {
            return Ok(ty);
        };
        let ty = self.maybe_ty_app(ty)?;
        if self.is_done() {
            return Ok(ty);
        };
        self.arrow_ty(ty)
    }

    fn maybe_ty_app(&mut self, head: Type) -> Parsed<Type> {
        let mut args = vec![];
        while !self.is_done() {
            match self.peek() {
                lexpat!(maybe[var][Var][parenL][brackL][curlyL]) => {
                    args.push(self.type_signature()?);
                }
                _ => break,
            }
        }
        if args.is_empty() {
            Ok(head)
        } else {
            args.into_iter()
                .rev()
                .map(Box::new)
                .fold(Ok(head), |a, c| a.map(|acc| Type::App(Box::new(acc), c)))
        }
    }

    fn ty_atom(&mut self) -> Parsed<Type> {
        match self.peek() {
            lexpat!(~[var]) => self
                .expect_lower()
                .map(|id| Tv::from(id.get_symbol()))
                .map(Type::Var),
            lexpat!(~[Var]) => {
                todo!()
            }
            lexpat!(~[brackL]) => self.brack_ty(),
            lexpat!(~[curlyL]) => self.curly_ty(),
            lexpat!(~[parenL]) => self.paren_ty(),
            _ => {
                todo!()
            }
        }
    }

    fn arrow_ty(&mut self, head: Type) -> Parsed<Type> {
        let mut left = head;
        while lexpat!(self on [->]) {
            self.bump();
            let right = self.type_signature()?;
            left = Type::Fun(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn paren_ty(&mut self) -> Parsed<Type> {
        use Lexeme::{ArrowR, Comma, ParenL, ParenR};
        self.eat(ParenL)?;

        if self.on_lexeme(ParenR) {
            self.bump();
            return Ok(Type::UNIT);
        }

        let first = self.ty_atom()?;
        if self.on_lexeme(Comma) {
            return self.tuple_ty(first);
        }

        let mut ty = first;
        while !(self.is_done() || self.on_lexeme(ParenR)) {
            if self.on_lexeme(Comma) {
                return self.tuple_ty(ty);
            };
            if self.on_lexeme(ArrowR) {
                ty = self.arrow_ty(ty)?;
                break;
            }
            if lexpat!(self on [var]|[Var]|[parenL]|[brackL]|[curlyL]) {
                ty = Type::App(Box::new(ty), self.ty_atom().map(Box::new)?);
                continue;
            }
            return Err(ParseError::Custom(
                self.get_srcloc(),
                self.bump(),
                "unbalanced parentheses in type signature",
            ));
        }

        self.eat(ParenR)?;
        Ok(ty)
    }

    fn tuple_ty(&mut self, head: Type) -> Parsed<Type> {
        use Lexeme::{Comma, ParenR};
        self.delimited([Comma, Comma, ParenR], Self::type_signature)
            .map(|rest| {
                let mut each = vec![head];
                each.extend(rest);
                Type::Tup(each)
            })
    }

    fn brack_ty(&mut self) -> Parsed<Type> {
        use Lexeme::{BrackL, BrackR};
        self.eat(BrackL)?;
        let tipo = self.type_signature()?;
        self.eat(BrackR)?;
        Ok(Type::Vec(Rc::new(tipo)))
    }

    fn curly_ty(&mut self) -> Parsed<Type> {
        use Lexeme::{Comma, CurlyL, CurlyR};
        self.delimited([CurlyL, Comma, CurlyR], |parse| {
            parse.record_entry_ty(Self::type_signature)
        })
        .map(|fields| Type::Rec(Record::Anon(fields)))
    }

    fn record_entry_ty<F>(&mut self, mut f: F) -> Parsed<Field<Type, Ident>>
    where
        F: FnMut(&mut Self) -> Parsed<Type>,
    {
        let key = self.expect_lower()?;
        self.eat(Lexeme::Colon2)?;
        let typ = f(self)?;
        Ok(Field::Entry(key, typ))
    }
}

// PATTERNS
impl<'t> Parser<'t> {
    pub fn pattern(&mut self) -> Parsed<Pattern> {
        use Lexeme::{BrackL, BrackR, Comma, CurlyL, CurlyR};
        fn maybe_cons(parser: &mut Parser) -> Parsed<Pattern> {
            let p = parser.pattern()?;
            parser.cons_pattern(p)
        }

        let genpat = match self.peek() {
            lexpat!(~[_]) => {
                self.bump();
                Ok(Pattern::Wild)
            }

            lexpat!(~[parenL]) => self.grouped_pattern(),

            lexpat!(~[brackL]) => self
                .delimited([BrackL, Comma, BrackR], maybe_cons)
                .map(Pattern::Lst),

            lexpat!(~[curlyL]) => self.curly_pattern(),

            lexpat!(~[var]) => self.expect_lower().map(Pattern::Var),

            lexpat!(~[Var]) => {
                let name = self.expect_upper()?;
                if lexpat!(self on [curlyL]) {
                    self.delimited([CurlyL, Comma, CurlyR], Self::field_pattern)
                        .map(|entries| {
                            Pattern::Rec(Record::Data(name, entries))
                        })
                } else {
                    Ok(Pattern::Con(name, vec![]))
                }
            }

            lexpat!(~[lit]) => self.lit_pattern(),
            _ => todo!(),
        }?;

        if lexpat!(self on [::]) {
            self.bump();
            self.type_signature()
                .map(|ty| Pattern::Cast(Box::new(genpat), ty))
        } else if lexpat!(self on [|]) {
            self.union_pattern()
        } else if let Pattern::Var(name) = genpat {
            if lexpat!(self on [@]) {
                self.bump();
                self.pattern().map(|pat| Pattern::At(name, Box::new(pat)))
            } else {
                Ok(genpat)
            }
        } else {
            Ok(genpat)
        }
    }

    fn lit_pattern(&mut self) -> Parsed<Pattern> {
        todo!()
    }

    fn grouped_pattern(&mut self) -> Parsed<Pattern> {
        todo!()
    }

    fn curly_pattern(&mut self) -> Parsed<Pattern> {
        use Lexeme::{Comma, CurlyL, CurlyR};

        self.delimited([CurlyL, Comma, CurlyR], Self::field_pattern)
            .map(|ps| Pattern::Rec(Record::Anon(ps)))
    }

    fn cons_pattern(&mut self, head: Pattern) -> Parsed<Pattern> {
        let mut elems = vec![head];
        while lexpat!(self on [:]) {
            self.bump();
            elems.push(self.pattern()?);
        }

        Ok(Pattern::Lst(elems))
    }

    fn union_pattern(&mut self) -> Parsed<Pattern> {
        todo!()
    }

    fn field_pattern(&mut self) -> Parsed<Field<Pattern>> {
        todo!()
    }
}

// EXPRESSIONS
impl<'t> Parser<'t> {
    pub fn expression(&mut self) -> Parsed<Expression> {
        self.maybe_binary(&mut Self::subexpression)
    }

    fn subexpression(&mut self) -> Parsed<Expression> {
        self.maybe_apply(Self::atom)
    }

    fn maybe_apply<F>(&mut self, mut f: F) -> Parsed<Expression>
    where
        F: FnMut(&mut Self) -> Parsed<Expression>,
    {
        let head = f(self)?;
        if self.test_lexeme(Lexeme::begins_expr) {
            let mut args = vec![];
            while !(self.is_done()
                || self.test_lexeme(|lx| lx.begins_expr() && !lx.is_infix()))
            {
                args.push(f(self)?);
            }
            Ok(args.into_iter().fold(head, Expression::mk_app))
        } else {
            Ok(head)
        }
    }

    fn maybe_binary<F>(&mut self, f: &mut F) -> Parsed<Expression>
    where
        F: FnMut(&mut Self) -> Parsed<Expression>,
    {
        let mut left = f(self)?;
        while lexpat!(self on [op]) {
            let infix = self.expect_infix()?;
            let right = self.maybe_binary(f).map(Box::new)?;
            left = Expression::Infix {
                left: Box::new(left),
                infix,
                right,
            };
        }
        Ok(left)
    }

    fn negation(&mut self, minus_sign: Lexeme) -> Parsed<Expression> {
        if self.on_lexeme(minus_sign) {
            self.bump();
            self.negation(minus_sign).map(Box::new).map(Expression::Neg)
        } else {
            self.atom()
        }
    }

    fn atom(&mut self) -> Parsed<Expression> {
        fn minus_sign() -> Lexeme {
            Lexeme::Infix(Ident::minus_sign().get_symbol())
        }

        match self.peek() {
            Some(Token { lexeme, .. }) if lexeme == &minus_sign() => {
                self.negation(minus_sign())
            }
            lexpat!(~[parenL]) => self.paren_expr(),
            lexpat!(~[brackL]) => self.brack_expr(),
            lexpat!(~[let]) => self.let_expr(),
            lexpat!(~[case]) => self.case_expr(),
            lexpat!(~[if]) => self.cond_expr(),
            lexpat!(~[lam]) => self.lambda(),
            lexpat!(~[lit]) => self.literal(),
            lexpat!(~[var][Var]) => self.identifier(),
            _ => Err(ParseError::Custom(self.get_srcloc(), self.bump(), "token does not correspond to a lexeme the begins an expression")),
        }
    }

    fn literal(&mut self) -> Parsed<Expression> {
        self.expect_literal().map(Expression::Lit)
    }

    fn identifier(&mut self) -> Parsed<Expression> {
        match self.peek() {
            lexpat!(~[var]) => self.expect_lower(),
            lexpat!(~[Var]) => self.expect_upper(),
            _ => Err(ParseError::Expected(
                self.get_srcloc(),
                LexKind::Identifier,
                self.bump(),
            )),
        }
        .map(Expression::Ident)
    }

    fn paren_expr(&mut self) -> Parsed<Expression> {
        use Lexeme::{Comma, ParenL, ParenR};
        self.eat(ParenL)?;
        if self.on_lexeme(ParenR) {
            self.bump();
            return Ok(Expression::UNIT);
        }

        if lexpat!(self on [op]) {
            let infix = self.expect_infix()?;
            self.eat(ParenR)?;
            return Ok(Expression::Group(Box::new(Expression::Ident(infix))));
        }

        let mut first = self.subexpression()?;

        if self.on_lexeme(Comma) {
            return Ok(Expression::Tuple(
                vec![first]
                    .into_iter()
                    .chain(self.delimited(
                        [Comma, Comma, ParenR],
                        &mut Self::subexpression,
                    )?)
                    .collect::<Vec<_>>(),
            ));
        }

        while !self.on_lexeme(ParenR) {
            first = Expression::mk_app(first, self.subexpression()?)
        }

        self.eat(ParenR)?;
        Ok(first)
    }

    fn brack_expr(&mut self) -> Parsed<Expression> {
        use Lexeme::{BrackL, BrackR, Comma};
        self.eat(BrackL)?;
        if lexpat!(self on [brackR]) {
            self.bump();
            return Ok(Expression::NULL);
        }

        let mut first = self.expression()?;
        if lexpat!(self on [..]) {
            self.bump();
            first = Expression::Range(
                Box::new(first),
                if self.test_lexeme(Lexeme::begins_expr) {
                    self.subexpression().map(Box::new).map(Some)?
                } else {
                    None
                },
            );
        };

        match self.peek() {
            lexpat!(~[brackR]) => {
                self.bump();
                Ok(Expression::Array(vec![first]))
            }
            lexpat!(~[|]) => self.list_comprehension(first),
            lexpat!(~[,]) => self
                .delimited([Comma, Comma, BrackR], Self::expression)
                .map(|xs| vec![first].into_iter().chain(xs).collect::<Vec<_>>())
                .map(Expression::Array),
            _ => Err(ParseError::InvalidLexeme(self.get_srcloc(), self.bump())),
        }
    }

    /// TODO: handle the following statement cases
    /// * a <- [1, 2]
    /// * [a, b] <- [1, 2]
    /// * a b c == [1, 2]
    /// * (a, b) <- c
    fn list_comprehension(&mut self, head: Expression) -> Parsed<Expression> {
        use Lexeme::{ArrowL, BrackR, Comma, Pipe};
        self.eat(Pipe)?;

        let mut stmts = vec![];
        loop {
            if self.on_lexeme(BrackR) {
                break;
            }
            let srcloc = self.get_srcloc();

            match self.peek() {
                lexpat!(maybe[brackL][parenL][_]) => {
                    let pat = self.pattern()?;
                    self.eat(ArrowL)?;
                    let stmt = Statement::Generator(pat, self.expression()?);
                    stmts.push(stmt);
                }
                lexpat!(~[var]) => {
                    let first = self.expect_lower()?;
                    if self.on_lexeme(ArrowL) {
                        self.bump();
                        let stmt = Statement::Generator(
                            Pattern::Var(first),
                            self.expression()?,
                        );
                        stmts.push(stmt)
                    }
                }
                _ => stmts.push(Statement::Predicate(self.expression()?)),
            }
            self.ignore(Comma);
            if self.is_done() {
                return Err(ParseError::UnexpectedEof(srcloc));
            }
        }
        self.eat(BrackR)?;

        Ok(Expression::List(Box::new(head), stmts))
    }

    fn lambda(&mut self) -> Parsed<Expression> {
        use Lexeme::{ArrowR, Lambda};
        self.eat(Lambda)?;
        let mut pats = vec![];

        while !(self.is_done() || !self.on_lexeme(ArrowR)) {
            if self.test_lexeme(Lexeme::begins_pat) {
                pats.push(self.pattern()?)
            } else {
                let srcloc = self.get_srcloc();
                return Err(ParseError::InvalidLexeme(srcloc, self.bump()));
            }
        }

        self.eat(ArrowR)?;

        self.expression().map(|expr| {
            pats.into_iter()
                .rev()
                .fold(expr, |body, arg| Expression::Lambda(arg, Box::new(body)))
        })
    }

    fn binding(&mut self) -> Parsed<Binding> {
        use Lexeme::{At, Colon2, Equal, Pipe, Semi};
        fn with_first_match(
            this: &mut Parser,
            name: Ident,
            tipo: Option<Signature>,
            pred: Option<Expression>,
        ) -> Parsed<Binding> {
            let body = this.expression()?;
            let wher = this.where_clause()?;
            let m1 = Match {
                args: vec![],
                pred,
                body,
                wher,
            };
            let arms = vec![m1]
                .into_iter()
                .chain(this.match_arms()?)
                .collect::<Vec<_>>();
            Ok(Binding { name, arms, tipo })
        }

        if lexpat!(self on [var]) {
            let first = self.expect_lower()?;
            if self.on_lexeme(Colon2) {
                let sig = self.total_signature().map(Some)?;
                let arms = self.match_arms()?;
                return Ok(Binding {
                    name: first,
                    arms,
                    tipo: sig,
                });
            }
            if self.on_lexeme(Equal) {
                self.bump();
                return with_first_match(self, first, None, None);
            }
            if lexpat!(self on [if]) {
                let tipo = None;
                let pred = {
                    self.bump();
                    self.expression().map(Some)?
                };
                self.eat(Equal)?;
                return with_first_match(self, first, tipo, pred);
            }

            if self.test_lexeme(Lexeme::begins_pat) {
                let arms = self.match_arms()?;
                return Ok(Binding {
                    name: first,
                    arms,
                    tipo: None,
                });
            }

            todo!()
        }

        todo!()
    }

    fn match_arms(&mut self) -> Parsed<Vec<Match>> {
        use Lexeme::{Equal, Pipe};
        self.many_while(
            |parser| parser.on_lexeme(Pipe),
            |parser| {
                let args = parser.many_while(
                    |parser| {
                        parser.test_lexeme(Lexeme::begins_pat)
                            && parser.on_lexeme(Equal)
                    },
                    Self::pattern,
                )?;
                let pred = if lexpat!(parser on [if]) {
                    parser.bump();
                    parser.expression().map(Some)?
                } else {
                    None
                };
                parser.eat(Equal)?;
                let body = parser.expression()?;
                let wher = parser.where_clause()?;
                Ok(Match {
                    args,
                    pred,
                    body,
                    wher,
                })
            },
        )
    }

    fn where_clause(&mut self) -> Parsed<Vec<Binding>> {
        use Lexeme::Semi;
        Ok(if lexpat!(self on [where]) {
            self.bump();
            let binds =
                self.many_while(|p| !p.on_lexeme(Semi), Self::binding)?;
            self.ignore(Semi);
            binds
        } else {
            vec![]
        })
    }

    fn let_expr(&mut self) -> Parsed<Expression> {
        use Keyword::{In, Let};
        use Lexeme::Kw;
        self.eat(Kw(Let))?;
        let binds = self.many_while(|p| !p.on_lexeme(Kw(In)), Self::binding)?;
        self.eat(Kw(In))?;
        let body = self.expression().map(Box::new)?;
        Ok(Expression::Let(binds, body))
    }
    fn case_expr(&mut self) -> Parsed<Expression> {
        todo!()
    }

    fn case_alt(&mut self) -> Parsed<Alternative> {
        let mut pat = self.pattern()?;
        if lexpat!(self on [@]) {
            if let Pattern::Var(name) = pat {
                let rhspat = self.pattern()?;
                pat = Pattern::At(name, Box::new(rhspat))
            } else {
                return Err(ParseError::InvalidLexeme(
                    self.get_srcloc(),
                    self.bump(),
                ));
            }
        };

        let pred = if lexpat!(self on [if]) {
            self.bump();
            self.expression().map(Some)?
        } else {
            None
        };

        self.eat(Lexeme::ArrowR)?;

        let body = self.expression()?;
        let wher = self.where_clause()?;
        Ok(Alternative {
            pat,
            pred,
            body,
            wher,
        })
    }

    fn cond_expr(&mut self) -> Parsed<Expression> {
        use Keyword::{Else, If, Then};
        use Lexeme::Kw;
        let mut exprs: [Expression; 3] = [Expression::UNIT; 3];
        for (i, kw) in [If, Then, Else].into_iter().enumerate() {
            self.eat(Kw(kw))?;
            exprs[i] = self.expression()?
        }

        Ok(Expression::Cond(Box::new(exprs)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn infixed(
        left: Expression,
        infix: wy_intern::Symbol,
        right: Expression,
    ) -> Expression {
        Expression::Infix {
            infix: Ident::Infix(infix),
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    fn tuplex<const N: usize>(subexps: [Expression; N]) -> Expression {
        Expression::Tuple(subexps.to_vec())
    }

    #[test]
    fn it_works() {
        use Expression::Lit;
        println!("{}", std::mem::size_of::<Expression>());
        let [op1, op2, plus, times, minus] =
            wy_intern::intern_many(["<>", "><", "+", "*", "-"]);
        let int = |n| Lit(Literal::Int(n));

        let tests = [
            (
                "1 + 2 * 3 - 4",
                infixed(
                    int(1),
                    plus,
                    infixed(int(2), times, infixed(int(3), minus, int(4))),
                ),
            ),
            (
                "(1, 2, 3) <> (4, 5, 6) >< (7, 8, 9)",
                infixed(
                    tuplex([int(1), int(2), int(3)]),
                    op1,
                    infixed(
                        tuplex([int(4), int(5), int(6)]),
                        op2,
                        tuplex([int(7), int(8), int(9)]),
                    ),
                ),
            ),
        ];

        for (src, expected) in tests {
            assert_eq!(Parser::from_str(src).expression().unwrap(), expected);
        }
    }
}
