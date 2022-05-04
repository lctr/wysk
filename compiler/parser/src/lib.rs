use std::rc::Rc;

use lexer::*;
use span::{Dummy, WithLoc, WithSpan};
use syntax::{
    fixity::{Assoc, Fixity, FixityTable, Prec},
    tipo::{Field, Record, Tv, Type},
    AliasDecl, Alternative, Arity, Binding, ClassDecl, Context, DataDecl, Declaration, Expression,
    FixityDecl, FnDecl, Ident, Import, ImportSpec, InstDecl, Match, Method, Module, Pattern,
    Program, Signature, Statement, Tag, Variant,
};
use token::*;

use wy_common as common;
use wy_failure as failure;
use wy_lexer as lexer;
use wy_span as span;
use wy_syntax as syntax;

use common::Deque;
use failure::*;

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
        let gutter = srcloc.gutter();
        let underline = (0..srcloc.coord.col.as_usize())
            .map(|_| ' ')
            .chain(
                (&src.lines()[srcloc.coord.row])
                    .char_indices()
                    .filter_map(|(b, c)| {
                        let col = srcloc.coord.col.as_usize();
                        if b < col {
                            Some('-')
                        } else if b >= col && !c.is_whitespace() {
                            Some('^')
                        } else {
                            None
                        }
                    })
                    .take_while(|c| !c.is_whitespace()),
            )
            .collect::<String>();
        let line = &src.lines()[srcloc.coord.row];
        write!(f, "\n{}=> {}\n", &gutter, &srcloc)?;
        write!(f, "{}|\n", &gutter)?;
        write!(f, "  [{}] | {}\n", srcloc.coord.row, line.trim())?;
        write!(f, "{}| {}\n", &gutter, underline.trim())?;
        Ok(())
    }
}

impl std::error::Error for ParseError {}

pub type Parsed<X> = Result<X, ParseError>;

pub trait Streaming {
    type Peeked: Lexlike;
    type Lexeme: Lexlike;
    type Err;
    fn peek(&mut self) -> Option<&Self::Peeked>;

    /// Peeks at the current `Peeked` item and calls the `Lexlike::cmp_tok`
    /// method on the provided input, returning whether a match was found.
    fn peek_on<T>(&mut self, item: T) -> bool
    where
        T: Lexlike<Self::Peeked, Self::Lexeme>,
    {
        match self.peek() {
            Some(t) => item.cmp_tok(t),
            None => false, // item.cmp_lex(&Lexeme::Eof),
        }
    }

    /// Advance the underlying stream of tokens. If the stream
    /// is not over, then the *current* token is returned; otherwise the token
    /// corresponding to the `EOF` lexeme is returned.
    ///
    /// Note that this method first checks the internal lexeme queue before
    /// calling the lexer. If the buffer is non-empty, it simply pops the next
    /// element from the front of the qeueue.
    fn bump(&mut self) -> Self::Peeked;

    /// Conditionally advances the token stream based on the given argument
    /// matching -- via the `Lexlike::cmp_tok` method -- the inner token
    /// referenced by the result of calling `Stream::peek`. Returns the same
    /// boolean value used to decide whether to advance or not.
    ///
    ///
    /// This method is useful as a shortcut to the pattern involved in
    /// conditionally advancing the inner stream of tokens as the side effect of
    /// a predicate (as in the following code snippet):
    /// ```rust,no-test
    /// if self.peek_on(...) {
    ///     self.bump();
    ///     /* do something */
    /// } /* do something else */
    /// ```
    fn bump_on<T>(&mut self, item: T) -> bool
    where
        T: Lexlike<Self::Peeked, Self::Lexeme>,
    {
        let on_it = self.peek_on(item);
        if on_it {
            self.bump();
        }
        on_it
    }
    fn is_done(&mut self) -> bool;

    /// Given a predicate `pred` and a parser, applies the given parser `parse`
    /// repeatedly as long as the predicate returns `true` and returning the
    /// results in a vector.
    ///
    /// This method will always check the predicate prior to running
    /// the given parser.
    ///
    /// **Note:** the given predicate *must* be coercible to
    /// `fn` pointer, and hence **must not** capture any variables.
    fn many_while<F, G, X>(&mut self, mut pred: G, mut f: F) -> Result<Vec<X>, Self::Err>
    where
        G: FnMut(&mut Self) -> bool,
        F: FnMut(&mut Self) -> Result<X, Self::Err>,
    {
        let mut xs = vec![];
        while pred(self) {
            xs.push(f(self)?);
        }
        Ok(xs)
    }

    fn many_while_on<L, F, X>(&mut self, item: L, mut f: F) -> Result<Vec<X>, Self::Err>
    where
        L: Lexlike<Self::Peeked, Self::Lexeme>,
        F: FnMut(&mut Self) -> Result<X, Self::Err>,
    {
        let mut xs = vec![];
        while matches!(self.peek(), Some(t) if item.cmp_tok(t)) {
            xs.push(f(self)?)
        }
        Ok(xs)
    }
}

type Spath = std::path::PathBuf;

#[derive(Debug)]
pub struct Parser<'t> {
    lexer: Lexer<'t>,
    queue: Deque<Token>,
    pub fixities: FixityTable,
    pub filepath: Option<Spath>,
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
    pub fn new(src: &'t str, filepath: Option<Spath>) -> Self {
        Self {
            lexer: Lexer::new(src),
            filepath,
            queue: Deque::new(),
            fixities: FixityTable::new(Ident::Infix),
        }
    }

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
        if self.queue.is_empty() {
            self.lexer.peek()
        } else {
            self.queue.front()
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
            token
        } else {
            self.lexer.bump()
        }
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
        Lexeme: From<T>,
    {
        match self.peek() {
            Some(t) if &item == t => Ok(self.bump()),
            Some(t) => match Lexeme::from(item) {
                delim @ (Lexeme::CurlyR | Lexeme::ParenR | Lexeme::BrackR) => {
                    let found = t.clone();
                    let srcloc = self.get_srcloc();
                    Err(ParseError::Unbalanced {
                        srcloc,
                        found,
                        delim,
                        source: self.source_string(),
                    })
                }
                found => {
                    let tok = t.clone();
                    let src_loc = self.get_srcloc();
                    Err(ParseError::Expected(
                        src_loc,
                        LexKind::Specified(found),
                        tok,
                        self.source_string(),
                    ))
                }
            },
            None => Err(ParseError::UnexpectedEof(
                self.get_srcloc(),
                self.source_string(),
            )),
        }
    }

    fn source_string(&self) -> String {
        let mut buf = String::new();
        self.lexer.write_to_string(&mut buf);
        buf
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
        T: Lexlike,
    {
        match self.peek() {
            Some(t) if item.cmp_tok(t) => {
                self.bump();
            }
            _ => (),
        }
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

    pub fn delimited<F, X>(&mut self, [start, mid, end]: [Lexeme; 3], mut f: F) -> Parsed<Vec<X>>
    where
        F: FnMut(&mut Self) -> Parsed<X>,
    {
        let mut nodes = vec![];
        let mut first = true;
        self.eat(start)?;
        while !self.is_done() {
            if self.peek_on(end) {
                break;
            }
            if first {
                first = false;
            } else {
                self.eat(mid)?;
            }
            if self.peek_on(end) {
                break;
            }
            nodes.push(f(self)?);
        }
        self.eat(end)?;
        Ok(nodes)
    }

    pub fn many_while<F, G, X>(&mut self, mut pred: G, mut f: F) -> Parsed<Vec<X>>
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

impl<'t> Streaming for Parser<'t> {
    type Peeked = Token;
    type Lexeme = Lexeme;
    type Err = ParseError;

    fn peek(&mut self) -> Option<&Self::Peeked> {
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
    /// Note that this method first checks the internal token queue before
    /// calling the lexer. If the buffer is non-empty, it simply pops the next
    /// element from the front of the qeueue.
    fn bump(&mut self) -> Token {
        if let Some(token) = self.queue.pop_front() {
            return token;
        }
        self.lexer.bump()
    }

    fn is_done(&mut self) -> bool {
        match self.peek() {
            Some(t) if t.lexeme.is_eof() => true,
            None => true,
            _ => false,
        }
    }
}

macro_rules! expect {
    ($self:ident $lexkind:ident) => {{
        let srcloc = $self.get_srcloc();
        if let Some(Token {
            lexeme: Lexeme::$lexkind(s),
            ..
        }) = $self.peek().copied()
        {
            $self.bump();
            Ok(Ident::$lexkind(s))
        } else {
            Err(ParseError::Expected(
                srcloc,
                LexKind::$lexkind,
                $self.bump(),
                $self.source_string(),
            ))
        }
    }};
}

// IDENTIFIERS AND LITERAL
impl<'t> Parser<'t> {
    fn expect_upper(&mut self) -> Parsed<Ident> {
        expect!(self Upper)
    }
    fn expect_lower(&mut self) -> Parsed<Ident> {
        expect!(self Lower)
    }
    fn expect_infix(&mut self) -> Parsed<Ident> {
        expect!(self Infix)
    }
    fn expect_literal(&mut self) -> Parsed<Literal> {
        let srcloc = self.get_srcloc();
        if let Some(Token {
            lexeme: Lexeme::Lit(lit),
            ..
        }) = self.peek().copied()
        {
            self.bump();
            Ok(lit)
        } else {
            Err(ParseError::Expected(
                srcloc,
                LexKind::Literal,
                self.bump(),
                self.source_string(),
            ))
        }
    }
}

// TOP-LEVEL
type ModuleParser<'t> = Parser<'t>;
impl<'t> ModuleParser<'t> {
    pub fn module(&mut self) -> Parsed<Module> {
        self.eat(Keyword::Module)?;
        let modname = self.expect_upper()?;
        self.eat(Keyword::Where)?;
        let imports = self.many_while_on(Keyword::Import, Self::import_spec)?;
        let mut module = Module {
            modname,
            imports,
            ..Default::default()
        };

        self.unfold_decls(&mut module)?;

        Ok(module)
    }

    fn unfold_decls(&mut self, module: &mut Module) -> Parsed<()> {
        while !self.is_done() {
            match self.declaration()? {
                Declaration::Data(data) => module.datatys.push(data),
                Declaration::Alias(alias) => module.aliases.push(alias),
                Declaration::Fixity(fixity) => module.infixes.push(fixity),
                Declaration::Class(class) => module.classes.push(class),
                Declaration::Instance(inst) => module.implems.push(inst),
                Declaration::Function(fun) => module.fundefs.push(fun),
            }
            if !self.is_done() {
                self.ignore(Lexeme::Semi)
            }
        }
        Ok(())
    }

    fn import_spec(&mut self) -> Parsed<ImportSpec> {
        use Keyword::{Hiding, Import, Qualified};
        use Lexeme::{Comma, CurlyL, CurlyR, Pipe};
        self.eat(Import)?;
        let qualified = self.bump_on(Qualified);
        let name = self.expect_upper()?;
        let rename = if self.bump_on(Pipe) {
            let rename = self.expect_upper()?;
            self.eat(Pipe)?;
            Some(rename)
        } else {
            None
        };
        let hidden = self.bump_on(Hiding);
        let imports = if lexpat!(self on [curlyL]) {
            self.delimited([CurlyL, Comma, CurlyR], Self::import_item)?
        } else {
            vec![]
        };
        Ok(ImportSpec {
            name,
            qualified,
            rename,
            hidden,
            imports,
        })
    }
    fn import_item(&mut self) -> Parsed<Import> {
        match self.peek() {
            lexpat!(~[var]) => Ok(Import::Function(self.expect_lower()?)),
            lexpat!(~[parenL]) => {
                self.eat(Lexeme::ParenL)?;
                let infix = self.expect_infix()?;
                self.eat(Lexeme::ParenR)?;
                Ok(Import::Operator(infix))
            }
            lexpat!(~[Var]) => {
                let first = self.expect_upper()?;
                if self.bump_on(Lexeme::ParenL) {
                    if self.bump_on(Lexeme::Dot2) {
                        self.eat(Lexeme::ParenR)?;
                        return Ok(Import::Total(first));
                    }

                    let ctors = self.many_while_on(Lexeme::is_upper, |p| {
                        let con = p.expect_upper()?;
                        p.ignore(Lexeme::Comma);
                        Ok(con)
                    })?;
                    self.eat(Lexeme::ParenR)?;
                    Ok(Import::Partial(first, ctors))
                } else {
                    Ok(Import::Abstract(first))
                }
            }
            _ => Err(ParseError::Custom(
                self.get_srcloc(),
                self.lookahead::<1>()[0],
                "is not a valid import",
                self.source_string(),
            )),
        }
    }

    fn parse(mut self) -> Parsed<Program> {
        use Keyword::Import;
        Ok(Program {
            module: if lexpat!(self on [module]) {
                self.module()?
            } else {
                let mut module = Module::default();
                module.imports = self.many_while_on(Import, Self::import_spec)?;
                self.unfold_decls(&mut module)?;
                module
            },
            fixities: self.fixities,
        })
    }
}

// FIXITY DECLARATIIONS
type FixityParser<'t> = Parser<'t>;
impl<'t> FixityParser<'t> {
    fn fixity_assoc(&mut self) -> Parsed<Assoc> {
        let assoc = match self.peek() {
            lexpat!(~[infix]) => Ok(Assoc::None),
            lexpat!(~[infixl]) => Ok(Assoc::Left),
            lexpat!(~[infixr]) => Ok(Assoc::Right),
            _ => Err(ParseError::Custom(
                self.get_srcloc(),
                self.bump(),
                "expected fixity keyword `infix`, `infixl`, or `infixr`",
                self.source_string(),
            )),
        }?;
        self.bump();
        Ok(assoc)
    }
    fn fixity_prec(&mut self) -> Parsed<Prec> {
        match self.peek() {
            Some(Token {
                lexeme: Lexeme::Lit(Literal::Int(p)),
                ..
            }) if *p < 10 => {
                let prec = Prec(*p as u8);
                self.bump();
                Ok(prec)
            }
            _ => Err(ParseError::InvalidPrec(
                self.get_srcloc(),
                self.bump(),
                self.source_string(),
            )),
        }
    }

    fn with_fixity(&mut self, fixity: Fixity) -> Parsed<Vec<Ident>> {
        self.many_while_on(Lexeme::is_infix, |p| {
            let srcloc = p.get_srcloc();
            let Spanned(infix, span) = p.spanned(Self::expect_infix);
            let infix = infix?;
            if p.fixities.contains_key(&infix) {
                Err(ParseError::FixityExists(
                    srcloc,
                    infix,
                    span,
                    p.source_string(),
                ))
            } else {
                p.fixities.insert(infix, fixity);
                Ok(infix)
            }
        })
    }
}

type DeclParser<'t> = Parser<'t>;
// DECLARATIONS
impl<'t> DeclParser<'t> {
    pub fn declaration(&mut self) -> Parsed<Declaration> {
        match self.peek() {
            lexpat!(maybe[infixl][infixr][infix]) => self.fixity_decl().map(Declaration::Fixity),
            lexpat!(maybe[data]) => self.data_decl().map(Declaration::Data),
            lexpat!(maybe[fn]) => self.function_decl().map(Declaration::Function),
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
        use Keyword::{Data, With};
        use Lexeme::{Comma, Equal, Kw, ParenL, ParenR, Pipe};

        self.eat(Kw(Data))?;

        let ctxt = if self.peek_on(Pipe) {
            self.delimited([Pipe, Comma, Pipe], Self::type_context)?
        } else {
            vec![]
        };
        let name = self.expect_upper()?;
        let mut decl = DataDecl {
            name,
            ctxt,
            poly: self.many_while(
                |p| !lexpat!(p on [=] | [;]),
                |p| p.expect_lower().map(|id| Tv(id.get_symbol().get())),
            )?,
            vnts: vec![],
            with: vec![],
        };

        if !self.bump_on(Equal) {
            return Ok(decl);
        }

        decl.vnts = self.many_while(
            |p| p.bump_on(Pipe) || p.peek_on(Lexeme::is_upper),
            Self::data_variant,
        )?;

        if self.bump_on(Kw(With)) {
            decl.with = if self.peek_on(ParenL) {
                self.delimited([ParenL, Comma, ParenR], Self::expect_upper)?
            } else {
                vec![self.expect_upper()?]
            }
        };

        Ok(decl.enumer_tags())
    }

    fn function_decl(&mut self) -> Parsed<FnDecl> {
        use Keyword::Fn;
        use Lexeme::{Colon2, ParenL, ParenR, Pipe};
        self.eat(Fn)?;

        let name = if self.bump_on(ParenL) {
            let name = self.expect_infix()?;
            self.eat(ParenR)?;
            name
        } else {
            self.expect_lower()?
        };

        let sign = if self.bump_on(Colon2) {
            self.total_signature().map(Some)?
        } else {
            None
        };

        self.ignore(Pipe);

        let mut defs = vec![self.match_arm()?];

        while self.bump_on(Pipe) {
            defs.push(self.match_arm()?);
        }

        Ok(FnDecl { name, defs, sign })
    }

    fn alias_decl(&mut self) -> Parsed<AliasDecl> {
        use Keyword::Type;
        use Lexeme::Equal;
        self.eat(Type)?;
        let name = self.expect_upper()?;
        let poly = self.many_while(
            |p| !p.peek_on(Equal),
            |p| p.expect_lower().map(|id| Tv(id.get_symbol().get())),
        )?;
        self.eat(Equal)?;
        let sign = self.total_signature()?;
        Ok(AliasDecl { name, poly, sign })
    }

    fn class_decl(&mut self) -> Parsed<ClassDecl> {
        self.eat(Keyword::Class)?;
        let ctxt = self.contexts()?;
        let name = self.expect_upper()?;
        let poly = self.many_while_on(Lexeme::is_lower, |p| {
            p.expect_lower().map(|id| Tv(id.get_symbol().get()))
        })?;
        self.eat(Lexeme::CurlyL)?;
        let mut defs = vec![];
        while !self.peek_on(Lexeme::CurlyR) {
            match self.binding()? {
                Binding {
                    name,
                    arms,
                    tipo: Some(sig),
                } if arms.is_empty() => defs.push(Method::Sig(name, sig)),
                binding => defs.push(Method::Impl(binding)),
            };
            self.ignore(Lexeme::Semi);
        }
        self.eat(Lexeme::CurlyR)?;
        Ok(ClassDecl {
            name,
            poly,
            ctxt,
            defs,
        })
    }

    fn inst_decl(&mut self) -> Parsed<InstDecl> {
        self.eat(Keyword::Impl)?;
        let ctxt = self.contexts()?;
        let name = self.expect_upper()?;
        let tipo = self.type_signature()?;
        self.eat(Lexeme::CurlyL)?;
        let mut defs = vec![];
        while !self.peek_on(Lexeme::CurlyR) {
            defs.push(self.binding()?);
            self.ignore(Lexeme::Semi);
        }
        self.eat(Lexeme::CurlyR)?;
        Ok(InstDecl {
            name,
            ctxt,
            defs,
            tipo,
        })
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
        Ok(Variant {
            name,
            args,
            arity,
            tag: Tag(0),
        })
    }
}

// TYPES TODO: refactor to differentiate between TYPEs (type only) and
// SIGNATURES (context + type)
type TypeParser<'t> = Parser<'t>;
impl<'t> TypeParser<'t> {
    /// This method parses a total type signature, i.e., everythin on the
    /// right-hand side of the lexeme `::`.
    ///
    /// Note: a total signature is only allowed in top-level declarations
    /// (namely, class and instance delcarations, as well as in the type
    /// signature of function declarations). It is illegal for a type to contain
    /// any type constraints in a cast expression or in data declaration
    /// constructor arguments.
    fn total_signature(&mut self) -> Parsed<Signature> {
        let ctxt = self.contexts()?;
        let tipo = self.type_signature()?;
        Ok(Signature { ctxt, tipo })
    }

    fn contexts(&mut self) -> Parsed<Vec<Context>> {
        let mut ctxt = vec![];
        if lexpat!(self on [|]) {
            ctxt = self.delimited(
                [Lexeme::Pipe, Lexeme::Comma, Lexeme::Pipe],
                Self::type_context,
            )?;
            self.ignore(Lexeme::FatArrow);
        };
        Ok(ctxt)
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
        let col = self.get_col();
        let ty = self.ty_atom()?;
        if lexpat!(self on [->]) {
            self.arrow_ty(ty)
        } else if self.get_col() > col {
            let ty = self.maybe_ty_app(ty)?;
            self.arrow_ty(ty)
        } else {
            Ok(ty)
        }
    }

    fn maybe_ty_app(&mut self, head: Type) -> Parsed<Type> {
        let on_ty = |p: &mut Self| lexpat!(p on [var]|[Var]|[parenL]|[brackL]|[curlyL]);
        match head {
            Type::Con(id, mut args) => {
                args.extend(self.many_while_on(Lexeme::begins_ty, Self::ty_atom)?);
                Ok(Type::Con(id, args))
            }
            head => {
                let mut args = vec![];
                while on_ty(self) {
                    args.push(self.ty_atom()?);
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
        }
    }

    fn ty_atom(&mut self) -> Parsed<Type> {
        match self.peek() {
            lexpat!(~[var]) => self
                .expect_lower()
                .map(|id| Tv::from(id.get_symbol()))
                .map(Type::Var),
            lexpat!(~[Var]) => Ok(Type::Con(self.expect_upper()?, vec![])),
            lexpat!(~[brackL]) => self.brack_ty(),
            lexpat!(~[curlyL]) => self.curly_ty(),
            lexpat!(~[parenL]) => self.paren_ty(),
            _ => Err(ParseError::Custom(
                self.get_srcloc(),
                self.bump(),
                "does not begin a type",
                self.source_string(),
            )),
        }
    }

    fn arrow_ty(&mut self, head: Type) -> Parsed<Type> {
        let mut rest = vec![];
        while lexpat!(self on [->]) {
            self.bump();
            let right = {
                let right = self.ty_atom()?;
                self.maybe_ty_app(right)?
            };
            rest.push(right);
        }
        Ok(rest
            .into_iter()
            .fold(head, |a, c| Type::Fun(Box::new(a), Box::new(c))))
    }

    fn paren_ty(&mut self) -> Parsed<Type> {
        use Lexeme::{ParenL, ParenR};
        self.eat(ParenL)?;

        if self.peek_on(ParenR) {
            self.bump();
            return Ok(Type::UNIT);
        }

        let mut ty = self.ty_atom()?;

        while !(self.is_done() || self.peek_on(ParenR)) {
            match self.peek() {
                lexpat!(~[,]) => return self.tuple_ty(ty),
                lexpat!(~[->]) => {
                    ty = self.arrow_ty(ty)?;
                    break;
                }
                Some(t) if t.begins_ty() => {
                    ty = Type::App(Box::new(ty), self.ty_atom().map(Box::new)?);
                    continue;
                }
                _ => {
                    return Err(ParseError::Custom(
                        self.get_srcloc(),
                        self.bump(),
                        "unbalanced parentheses in type signature",
                        self.source_string(),
                    ));
                }
            }
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
        self.eat(Lexeme::BrackL)?;
        let tipo = self.type_signature()?;
        self.eat(Lexeme::BrackR)?;
        Ok(Type::Vec(Rc::new(tipo)))
    }

    fn curly_ty(&mut self) -> Parsed<Type> {
        use Lexeme::{Comma, CurlyL, CurlyR};

        Ok(Type::Rec(Record::Anon(
            self.delimited([CurlyL, Comma, CurlyR], |parse| {
                parse.record_entry_ty(Self::type_signature)
            })?,
        )))
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
type PatParser<'t> = Parser<'t>;
impl<'t> PatParser<'t> {
    pub fn pattern(&mut self) -> Parsed<Pattern> {
        use Lexeme::{BrackL, BrackR, Comma, CurlyL, CurlyR, Underline};

        if self.bump_on(Underline) {
            return Ok(Pattern::Wild);
        };

        let genpat = match self.peek() {
            lexpat!(~[parenL]) => self.grouped_pattern(),

            lexpat!(~[brackL]) => self
                .delimited([BrackL, Comma, BrackR], Self::pattern)
                .map(Pattern::Vec),

            lexpat!(~[curlyL]) => self.curly_pattern(),

            lexpat!(~[var]) => self.expect_lower().map(Pattern::Var),

            lexpat!(~[Var]) => {
                let name = self.expect_upper()?;
                if lexpat!(self on [curlyL]) {
                    self.delimited([CurlyL, Comma, CurlyR], Self::field_pattern)
                        .map(|entries| Pattern::Rec(Record::Data(name, entries)))
                } else {
                    Ok(Pattern::Dat(name, vec![]))
                }
            }

            lexpat!(~[lit]) => self.lit_pattern(),

            _ => {
                return Err(ParseError::Custom(
                    self.get_srcloc(),
                    self.lookahead::<1>()[0],
                    "does not begin a valid pattern",
                    self.source_string(),
                ))
            }
        }?;

        if let Pattern::Var(name) = genpat {
            if lexpat!(self on [@]) {
                self.bump();
                return Ok(Pattern::At(name, Box::new(self.pattern()?)));
            }
        }

        if lexpat!(self on [|]) {
            self.union_pattern(genpat)
        } else if lexpat!(self on [::]) {
            self.bump();
            Ok(Pattern::Cast(Box::new(genpat), self.type_signature()?))
        } else {
            Ok(genpat)
        }
    }

    fn lit_pattern(&mut self) -> Parsed<Pattern> {
        Ok(Pattern::Lit(self.expect_literal()?))
    }

    fn grouped_pattern(&mut self) -> Parsed<Pattern> {
        use Lexeme::{Comma, ParenL, ParenR};
        fn tuple_tail(this: &mut Parser, fst: Pattern) -> Parsed<Pattern> {
            let mut tupes = vec![fst];
            tupes.extend(this.delimited([Comma, Comma, ParenR], Parser::pattern)?);
            Ok(Pattern::Tup(tupes))
        }

        let pat_err = |this: &mut Self| {
            Err(ParseError::Unbalanced {
                srcloc: this.get_srcloc(),
                found: this.lookahead::<1>()[0],
                delim: ParenR,
                source: this.source_string(),
            })
        };

        self.eat(ParenL)?;

        match self.peek() {
            lexpat!(~[parenR]) => {
                self.bump();
                Ok(Pattern::UNIT)
            }

            lexpat!(~[Var]) => {
                let upper = self.expect_upper()?;
                let args = self.many_while_on(Lexeme::begins_pat, Self::pattern)?;
                let arity = args.len();
                let mut first = Pattern::Dat(upper, args);
                loop {
                    match self.peek() {
                        lexpat!(~[parenR]) => break,
                        lexpat!(~[,]) => return tuple_tail(self, first),
                        lexpat!(~[curlyL]) if arity == 0 => {
                            first = self.con_curly_pattern(upper)?;
                        }
                        lexpat!(~[|]) => {
                            first = self.union_pattern(first)?;
                        }
                        lexpat!(~[:]) => {
                            first = self.cons_pattern(first)?;
                        }
                        _ => break,
                    }
                }
                self.eat(ParenR)?;
                Ok(first)
            }

            lexpat!(~[var]) => {
                let var = self.expect_lower()?;
                let pat = if self.bump_on(Lexeme::At) {
                    Pattern::At(var, Box::new(self.pattern()?))
                } else {
                    Pattern::Var(var)
                };
                match self.peek() {
                    lexpat!(~[parenR]) => {
                        self.bump();
                        Ok(pat)
                    }
                    lexpat!(~[,]) => tuple_tail(self, pat),
                    lexpat!(~[|]) => {
                        let pat = self.union_pattern(pat)?;
                        self.eat(ParenR)?;
                        Ok(pat)
                    }
                    lexpat!(~[:]) => {
                        let pat = self.cons_pattern(pat)?;
                        if lexpat!(self on [,]) {
                            return tuple_tail(self, pat);
                        }
                        self.eat(ParenR)?;
                        Ok(pat)
                    }
                    lexpat!(~[curlyL]) if matches!(&pat, Pattern::Var(_)) => {
                        let pat = self.con_curly_pattern(var)?;
                        self.eat(ParenR)?;
                        Ok(pat)
                    }
                    _ => pat_err(self),
                }
            }

            Some(t) if t.lexeme.begins_pat() => {
                let first = self.pattern()?;
                if self.bump_on(ParenR) {
                    return Ok(first);
                };

                match self.peek() {
                    lexpat! {~[,]} => tuple_tail(self, first),
                    lexpat!(~[:]) => {
                        let pat = self.cons_pattern(first)?;
                        self.eat(ParenR)?;
                        Ok(pat)
                    }
                    lexpat!(~[|]) => {
                        let pat = self.union_pattern(first)?;
                        self.eat(ParenR)?;
                        Ok(pat)
                    }
                    _ => pat_err(self),
                }
            }

            _ => pat_err(self),
        }
    }

    fn con_curly_pattern(&mut self, conid: Ident) -> Parsed<Pattern> {
        use Lexeme::{Comma, CurlyL, CurlyR};
        Ok(Pattern::Rec(Record::Data(
            conid,
            self.delimited([CurlyL, Comma, CurlyR], Self::field_pattern)?,
        )))
    }

    fn curly_pattern(&mut self) -> Parsed<Pattern> {
        use Lexeme::{Comma, CurlyL, CurlyR};

        self.delimited([CurlyL, Comma, CurlyR], Self::field_pattern)
            .map(|ps| Pattern::Rec(Record::Anon(ps)))
    }

    /// List cons patterns
    /// [a, b, c] = a:b:c:[]
    /// * (a : b)           ==> [a, b]
    /// * (a:[])            ==> [a]
    /// * (a:b:[c, d])      ==> [a, b, c, d]
    /// * (a:b:(c:d))       ==> [a, b, [c, d]]
    fn cons_pattern(&mut self, head: Pattern) -> Parsed<Pattern> {
        let mut elems = vec![head];
        while lexpat!(self on [:]) {
            if lexpat!(self on [brackL]) {
                match self.pattern()? {
                    Pattern::Vec(xs) => {
                        elems.extend(xs);
                    }
                    pat => elems.push(pat),
                }
                continue;
            }
            self.bump();
            elems.push(self.pattern()?);
        }
        Ok(Pattern::Vec(elems))
    }

    fn union_pattern(&mut self, first: Pattern) -> Parsed<Pattern> {
        let mut rest = Deque::new();
        while self.bump_on(Lexeme::Pipe) {
            rest.push_back(self.pattern()?);
        }
        if rest.is_empty() {
            Ok(first)
        } else {
            Ok(Pattern::Or({
                rest.push_front(first);
                rest.into_iter().collect()
            }))
        }
    }

    fn field_pattern(&mut self) -> Parsed<Field<Pattern>> {
        Ok(Field::Entry(self.expect_lower()?, {
            self.eat(Lexeme::Colon2)?;
            self.pattern()?
        }))
    }
}

// EXPRESSIONS
pub type ExprParser<'t> = Parser<'t>;
impl<'t> ExprParser<'t> {
    /// Parses an expression. An expression may begin with either the keywores
    /// `let`, `if`, `case`, or `do`.
    ///
    /// Application binds tigher than infixes do, thus parsing an expression can
    /// be broken down into two steps:
    /// 1. try and parse an application
    /// 2. try and parse a binary expression
    /// Notice that the order above is contravariant to the methods called when
    /// parsing: this is because a binary expression will first try and parse an
    /// application for both left and right-hand sides.
    pub fn expression(&mut self) -> Parsed<Expression> {
        self.maybe_binary(&mut Self::subexpression)
    }

    /// A subexpression is synonymous to an application not only because a
    /// single terminal may be interpreted as a trivial application, but also
    /// because applications have higher precedence than infix operators do.
    fn subexpression(&mut self) -> Parsed<Expression> {
        self.maybe_apply(Self::atom)
    }

    fn maybe_apply<F>(&mut self, mut f: F) -> Parsed<Expression>
    where
        F: FnMut(&mut Self) -> Parsed<Expression>,
    {
        let head = f(self)?;
        let args = self.many_while_on(Lexeme::begins_expr, f)?;
        Ok(args.into_iter().fold(head, Expression::mk_app))
    }

    /// Applies a the given parser and, if encountering an operator, will
    /// continuously repeat parsing after consuming each operator to generate
    /// an infix expression.
    ///
    /// __Note__: *all* operators are initially parsed as though they were
    /// *left* associative with precedence *9*. It is not until after a module
    /// parsed (as well as any dependencies) that fixities are resolved and the
    /// infix expressions "fixed" (read: reordered) to reflect their fixities.
    /// The only instance in which this does not happen is when expressions
    /// are *grouped*, where they are (from a separate method) parsed as
    /// `Grouped` nodes regardless as to whether they contain infix expressions.
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

        if self.bump_on(Lexeme::Colon2) {
            let tipo = self.type_signature()?;
            Ok(Expression::Cast(Box::new(left), tipo))
        } else {
            Ok(left)
        }
    }

    fn negation(&mut self, minus_sign: Lexeme) -> Parsed<Expression> {
        if self.peek_on(minus_sign) {
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
            Some(Token { lexeme, .. }) if lexeme == &minus_sign() => self.negation(minus_sign()),
            lexpat!(~[parenL]) => self.paren_expr(),
            lexpat!(~[brackL]) => self.brack_expr(),
            lexpat!(~[let]) => self.let_expr(),
            lexpat!(~[case]) => self.case_expr(),
            lexpat!(~[if]) => self.cond_expr(),
            lexpat!(~[lam]) => self.lambda(),
            lexpat!(~[lit]) => self.literal(),
            lexpat!(~[var][Var]) => self.identifier(),
            _ => Err(ParseError::Custom(
                self.get_srcloc(),
                self.bump(),
                "does not correspond to a lexeme that begins an expression",
                self.source_string(),
            )),
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
                self.source_string(),
            )),
        }
        .map(Expression::Ident)
    }

    fn paren_expr(&mut self) -> Parsed<Expression> {
        use Lexeme::{Comma, ParenL, ParenR};
        self.eat(ParenL)?;
        if self.peek_on(ParenR) {
            self.bump();
            return Ok(Expression::UNIT);
        }

        if lexpat!(self on [op]) {
            let infix = self.expect_infix()?;
            self.eat(ParenR)?;
            return Ok(Expression::Group(Box::new(Expression::Ident(infix))));
        }

        let mut first = self.expression()?;

        if self.peek_on(Comma) {
            let mut tups = vec![first];
            tups.extend(self.delimited([Comma, Comma, ParenR], &mut Self::subexpression)?);
            return Ok(Expression::Tuple(tups));
        }

        while !self.peek_on(ParenR) {
            first = Expression::mk_app(first, self.subexpression()?)
        }

        self.eat(ParenR)?;
        // only represent as grouped if containing an infix expression to
        // preserve explicit groupings during fixity resolution and retraversal
        if let Expression::Infix { .. } = &first {
            Ok(Expression::Group(Box::new(first)))
        } else {
            Ok(first)
        }
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
                if self.peek_on(Lexeme::begins_expr) {
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
            _ => Err(ParseError::InvalidLexeme(
                self.get_srcloc(),
                self.bump(),
                self.source_string(),
            )),
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
            if self.peek_on(BrackR) {
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
                    if self.peek_on(ArrowL) {
                        self.bump();
                        let stmt = Statement::Generator(Pattern::Var(first), self.expression()?);
                        stmts.push(stmt)
                    }
                }
                _ => stmts.push(Statement::Predicate(self.expression()?)),
            }
            self.ignore(Comma);
            if self.is_done() {
                return Err(ParseError::UnexpectedEof(srcloc, self.source_string()));
            }
        }
        self.eat(BrackR)?;

        Ok(Expression::List(Box::new(head), stmts))
    }

    fn lambda(&mut self) -> Parsed<Expression> {
        use Lexeme::{ArrowR, Lambda};
        self.eat(Lambda)?;
        let mut pats = vec![];

        while !(self.is_done() || !self.peek_on(ArrowR)) {
            if self.peek_on(Lexeme::begins_pat) {
                pats.push(self.pattern()?)
            } else {
                let srcloc = self.get_srcloc();
                return Err(ParseError::InvalidLexeme(
                    srcloc,
                    self.bump(),
                    self.source_string(),
                ));
            }
        }

        self.eat(ArrowR)?;

        self.expression().map(|expr| {
            pats.into_iter()
                .rev()
                .fold(expr, |body, arg| Expression::Lambda(arg, Box::new(body)))
        })
    }

    fn binder_name(&mut self) -> Parsed<Ident> {
        use Lexeme::{ParenL, ParenR};
        if self.bump_on(ParenL) {
            let infix = self.expect_infix()?;
            self.eat(ParenR)?;
            Ok(infix)
        } else if lexpat!(self on [var]) {
            self.expect_lower()
        } else {
            Err(ParseError::Custom(
                self.get_srcloc(),
                self.bump(),
                "is not a valid binding name: expected a lowercase-initial identifier or an infix wrapped in parentheses", 
                self.source_string()
            ))
        }
    }

    fn binding_lhs(&mut self) -> Parsed<(Vec<Pattern>, Option<Expression>)> {
        use Keyword::If;
        use Lexeme::Pipe;
        self.ignore(Pipe);
        let args = self.many_while_on(Lexeme::begins_pat, Self::pattern)?;
        if lexpat!(self on [|]|[;]|[=]) {
            return Ok((args, None));
        } else if self.bump_on(If) {
            Ok((args, Some(self.expression()?)))
        } else {
            Err(ParseError::Custom(
                self.get_srcloc(),
                self.bump(),
                "is not a valid binding argument pattern",
                self.source_string(),
            ))
        }
    }

    fn binding_rhs(&mut self) -> Parsed<(Expression, Vec<Binding>)> {
        let body = self.expression()?;
        let wher = self.where_clause()?;
        Ok((body, wher))
    }

    fn binding(&mut self) -> Parsed<Binding> {
        use Lexeme::Pipe;

        let name = self.binder_name()?;

        match self.peek() {
            lexpat!(~[::]) => {
                self.bump();
                let tipo = self.total_signature()?;
                Ok(Binding {
                    name,
                    arms: self.match_arms()?,
                    tipo: Some(tipo),
                })
            }
            lexpat!(~[=]) => {
                self.bump();
                let (body, wher) = self.binding_rhs()?;
                let mut arms = vec![Match {
                    args: vec![],
                    pred: None,
                    body,
                    wher,
                }];
                arms.extend(self.match_arms()?);
                Ok(Binding {
                    name,
                    tipo: None,
                    arms,
                })
            }
            Some(t) if t.begins_pat() || t.lexeme == Pipe => Ok(Binding {
                name,
                tipo: None,
                arms: self.match_arms()?,
            }),
            lexpat!(~[;]) => Ok(Binding {
                name,
                arms: vec![],
                tipo: None,
            }),
            _ => Err(ParseError::Custom(
                self.get_srcloc(),
                self.lookahead::<1>()[0],
                "unable to parse binding",
                self.source_string(),
            )),
        }
    }

    fn match_arms(&mut self) -> Parsed<Vec<Match>> {
        use Lexeme::Pipe;
        self.many_while(
            |parser| parser.bump_on(Pipe) || parser.peek_on(Lexeme::begins_pat),
            Self::match_arm,
        )
    }

    fn match_arm(&mut self) -> Parsed<Match> {
        use Lexeme::Equal;
        let (args, pred) = self.binding_lhs()?;
        self.eat(Equal)?;
        let (body, wher) = self.binding_rhs()?;
        Ok(Match {
            args,
            pred,
            body,
            wher,
        })
    }

    fn where_clause(&mut self) -> Parsed<Vec<Binding>> {
        use Lexeme::Pipe;

        if lexpat!(self on [where]) {
            self.bump();
            self.many_while(
                |p| p.bump_on(Pipe) || p.peek_on(Lexeme::begins_pat),
                Self::binding,
            )
        } else {
            Ok(vec![])
        }
    }

    fn let_expr(&mut self) -> Parsed<Expression> {
        use Keyword::{In, Let};
        use Lexeme::{Kw, Pipe};
        Ok(Expression::Let(
            {
                self.eat(Kw(Let))?;
                self.many_while(
                    |p| !p.peek_on(Kw(In)) && (p.bump_on(Pipe) || p.peek_on(Lexeme::begins_pat)),
                    Self::binding,
                )?
            },
            {
                self.eat(Kw(In))?;
                Box::new(self.expression()?)
            },
        ))
    }

    fn case_expr(&mut self) -> Parsed<Expression> {
        use Keyword::{Case, Of};
        use Lexeme::{CurlyL, CurlyR, Pipe, Semi};

        self.eat(Case)?;
        let scrut = self.expression()?;
        self.eat(Of)?;
        let alts = if self.peek_on(CurlyL) {
            self.delimited([CurlyL, Semi, CurlyR], Self::case_alt)?
        } else {
            let col = self.get_col();
            self.many_while(
                |p| (p.get_col() == col) && (p.bump_on(Pipe) || p.peek_on(Lexeme::begins_pat)),
                Self::case_alt,
            )?
        };

        Ok(Expression::Case(Box::new(scrut), alts))
    }

    fn case_alt(&mut self) -> Parsed<Alternative> {
        let mut pat = if lexpat!(self on [Var]) {
            let con = self.expect_upper()?;
            let args = self.many_while_on(Lexeme::begins_pat, Self::pattern)?;
            Pattern::Dat(con, args)
        } else {
            self.pattern()?
        };

        if lexpat!(self on [@]) {
            if let Pattern::Var(name) = pat {
                let rhspat = self.pattern()?;
                pat = Pattern::At(name, Box::new(rhspat))
            } else {
                return Err(ParseError::InvalidLexeme(
                    self.get_srcloc(),
                    self.bump(),
                    self.source_string(),
                ));
            }
        };

        let pred = if self.peek_on(Keyword::If) {
            self.eat(Keyword::If)?;
            self.subexpression().map(Some)?
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

    fn infixed(left: Expression, infix: wy_intern::Symbol, right: Expression) -> Expression {
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
    fn test_infix_exprs() {
        use Expression::Lit;
        let [op1, op2, plus, times, minus, fun] =
            wy_intern::intern_many(["<>", "><", "+", "*", "-", "fun"]);
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
            (
                "fun 1 2",
                Expression::App(
                    Box::new(Expression::App(
                        Box::new(Expression::Ident(Ident::Lower(fun))),
                        Box::new(int(1)),
                    )),
                    Box::new(int(2)),
                ),
            ),
        ];

        for (src, expected) in tests {
            assert_eq!(Parser::from_str(src).expression().unwrap(), expected);
        }

        println!(
            "{:#?}",
            Parser::from_str(
                r#"
fn foo :: a -> (a, a)
| x = (x, x)
| _ = let some x y if x > y = Some (x, y) 
    | x y = Some (y, x) in some 1 1
"#
            )
            .function_decl()
        )
    }

    #[test]
    fn case_expr() {
        let src = r#"
case f x of {
  A c -> c;
  B d if c d -> h;
  y -> y;
}
"#;
        let [a, b, c, d, h, f, x, y] =
            wy_intern::intern_many(["A", "B", "c", "d", "h", "f", "x", "y"]);
        let expr = Parser::from_str(src).case_expr();
        println!("{:#?}", &expr);
        let expected = Expression::Case(
            Box::new(Expression::App(
                Box::new(Expression::Ident(Ident::Lower(f))),
                Box::new(Expression::Ident(Ident::Lower(x))),
            )),
            vec![
                Alternative {
                    pat: Pattern::Dat(Ident::Upper(a), vec![Pattern::Var(Ident::Lower(c))]),
                    pred: None,
                    body: Expression::Ident(Ident::Lower(c)),
                    wher: vec![],
                },
                Alternative {
                    pat: Pattern::Dat(Ident::Upper(b), vec![Pattern::Var(Ident::Lower(d))]),
                    pred: Some(Expression::App(
                        Box::new(Expression::Ident(Ident::Lower(c))),
                        Box::new(Expression::Ident(Ident::Lower(d))),
                    )),
                    body: Expression::Ident(Ident::Lower(h)),
                    wher: vec![],
                },
                Alternative {
                    pat: Pattern::Var(Ident::Lower(y)),
                    pred: None,
                    body: Expression::Ident(Ident::Lower(y)),
                    wher: vec![],
                },
            ],
        );
        assert_eq!(expr, Ok(expected))
    }

    #[test]
    fn test_pattern() {
        let int = |n| Pattern::Lit(Literal::Int(n));
        let [a, b, c, d] = wy_intern::intern_many(["a", "b", "c", "d"]);
        let id = |s| Pattern::Var(Ident::Lower(s));
        let pairs = [
            ("(a, b)", Pattern::Tup(vec![id(a), id(b)])),
            (
                "(a:b:(c:d))",
                Pattern::Vec(vec![id(a), id(b), Pattern::Vec(vec![id(c), id(d)])]),
            ),
            (
                "a @ [1, 2, 3]",
                Pattern::At(
                    Ident::Lower(a),
                    Box::new(Pattern::Vec(vec![int(1), int(2), int(3)])),
                ),
            ),
            (
                "(a:b:[c, d])",
                Pattern::Vec(vec![id(a), id(b), id(c), id(d)]),
            ),
            ("(a:[])", Pattern::Vec(vec![id(a)])),
        ];

        for (s, x) in pairs {
            assert_eq!(Parser::from_str(s).pattern(), Ok(x))
        }
    }

    #[test]
    fn test_module() {
        let src = r#"
module Prelude where

data Bool = False | True 

infixl 2 ||
infixl 3 &&

fn (||) :: Bool -> Bool -> Bool
| True _ = True
| False y = y

fn (&&) :: Bool -> Bool -> Bool
| True y = y
| False _ = False

fn any :: (a -> Bool) -> [a] -> Bool
| f [] = False
| f [x] = f x
| f (x:xs) = f x || any f xs

fn all :: (a -> Bool) -> [a] -> Bool
| f [] = False
| f [x] = f x
| f (x:xs) = f x && all f xs

fn not :: Bool -> Bool
| True = False
| False = True

infix 4 == !=

class Eq a {
    (==) :: a -> a -> Bool;
    (!=) :: a -> a -> Bool
    | x y = not (x == y)
}

"#;
        let parser = Parser::from_str(src);
        println!("{:#?}", parser.parse());
    }

    #[test]
    fn test_prelude_module() {
        let src = include_str!("../../../language/prim.ws");
        // let src = "-5";
        // println!("{:?}", Parser::from_str(src).expression());
        let result = Parser::from_str(src).module();

        println!("{:#?}", result);
        let mut parser = Parser::from_str(src);
        for _ in 0..10 {
            println!("{:?}", parser.get_loc());
            println!("{:?}", parser.peek());
            println!("{:?}", parser.get_loc());
            println!("{:?}", parser.bump());
        }
    }
}
