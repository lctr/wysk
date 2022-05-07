use std::rc::Rc;

use token::*;
use wy_lexer::*;
use wy_span::{Dummy, WithLoc, WithSpan};
use wy_syntax::{
    fixity::{Assoc, Fixity, FixityTable, Prec},
    ident::{Chain, Ident},
    tipo::{Field, Record, Tv, Type},
    AliasDecl, Alternative, Arity, Binding, ClassDecl, Context, DataDecl, Declaration, Expression,
    FixityDecl, FnDecl, Import, ImportSpec, InstDecl, Match, Method, Module, Pattern, Program,
    Signature, Statement, Tag, Variant,
};

use wy_common::Deque;

pub mod error;

use error::*;

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
                        source: self.text(),
                    })
                }
                found => {
                    let tok = t.clone();
                    let src_loc = self.get_srcloc();
                    Err(ParseError::Expected(
                        src_loc,
                        LexKind::Specified(found),
                        tok,
                        self.text(),
                    ))
                }
            },
            None => Err(ParseError::UnexpectedEof(self.get_srcloc(), self.text())),
        }
    }

    fn text(&self) -> String {
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
                $self.text(),
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
        if self.bump_on(Lexeme::Colon) {
            Ok(Ident::cons_sign())
        } else {
            expect!(self Infix)
        }
    }
    fn expect_ident(&mut self) -> Parsed<Ident> {
        match self.peek().map(|t| t.lexeme) {
            Some(Lexeme::Upper(s)) => {
                self.bump();
                Ok(Ident::Upper(s))
            }
            Some(Lexeme::Lower(s)) => {
                self.bump();
                Ok(Ident::Lower(s))
            }
            Some(Lexeme::Infix(s)) => {
                self.bump();
                Ok(Ident::Infix(s))
            }
            _ => Err(ParseError::Expected(
                self.get_srcloc(),
                LexKind::Identifier,
                self.lookahead::<1>()[0],
                self.text(),
            )),
        }
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
                self.text(),
            ))
        }
    }
}

// TOP-LEVEL
type ModuleParser<'t> = Parser<'t>;
impl<'t> ModuleParser<'t> {
    pub fn module(&mut self) -> Parsed<Module> {
        self.eat(Keyword::Module)?;
        let rootname = self.expect_upper()?;
        let tailnames = self.many_while(|p| p.bump_on(Lexeme::Dot), Self::expect_upper)?;
        self.eat(Keyword::Where)?;
        let imports = self.imports()?;
        let mut module = Module {
            modname: Chain::new(rootname, tailnames.into_iter().collect()),
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

    fn imports(&mut self) -> Parsed<Vec<ImportSpec>> {
        self.many_while(
            |p| p.bump_on(Keyword::Import) || p.bump_on(Lexeme::Pipe),
            Self::import_spec,
        )
    }

    fn import_spec(&mut self) -> Parsed<ImportSpec> {
        use Keyword::{Hiding, Qualified};
        use Lexeme::{At, Comma, CurlyL, CurlyR};

        let qualified = self.bump_on(Qualified);
        let name = Chain::new(
            self.expect_upper()?,
            // todo: specialize/optimize this
            self.id_path_tail()?.into_iter().collect(),
        );
        let rename = if self.bump_on(At) {
            Some(self.expect_upper()?)
        } else {
            None
        };
        let hidden = self.bump_on(Hiding);
        let imports = if self.peek_on(CurlyL) {
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

                    let ctors = self.many_while_on(Lexeme::is_ident, |p| {
                        let con = p.expect_ident()?;
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
                self.text(),
            )),
        }
    }

    pub fn parse(mut self) -> Parsed<Program> {
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
            comments: self.lexer.comments,
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
                self.text(),
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
                self.text(),
            )),
        }
    }

    fn with_fixity(&mut self, fixity: Fixity) -> Parsed<Vec<Ident>> {
        self.many_while_on(Lexeme::is_infix, |p| {
            let srcloc = p.get_srcloc();
            let Spanned(infix, span) = p.spanned(Self::expect_infix);
            let infix = infix?;
            if p.fixities.contains_key(&infix) {
                Err(ParseError::FixityExists(srcloc, infix, span, p.text()))
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
            self.delimited([Pipe, Comma, Pipe], Self::ty_constraint)?
        } else {
            vec![]
        };
        let name = self.expect_upper()?;
        let mut decl = DataDecl {
            name,
            ctxt,
            poly: self.many_while(
                |p| !lexpat!(p on [=] | [;]),
                |p| p.expect_lower().map(Tv::from_ident),
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
            |p| p.expect_lower().map(Tv::from_ident),
        )?;
        self.eat(Equal)?;
        let sign = self.total_signature()?;
        Ok(AliasDecl { name, poly, sign })
    }

    fn class_decl(&mut self) -> Parsed<ClassDecl> {
        self.eat(Keyword::Class)?;
        let ctxt = self.ty_contexts()?;
        let name = self.expect_upper()?;
        let poly =
            self.many_while_on(Lexeme::is_lower, |p| p.expect_lower().map(Tv::from_ident))?;
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
        let ctxt = self.ty_contexts()?;
        let name = self.expect_upper()?;
        let tipo = self.ty_atom()?;
        self.ignore(Keyword::With);
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
            args.push(self.ty_node()?);
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

// fn on_ty_start(parser: &mut Parser) -> bool {
//     lexpat!(parser on [var][Var])
// }

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
        let ctxt = self.ty_contexts()?;
        let tipo = self.ty_node()?;
        Ok(Signature { ctxt, tipo })
    }

    fn ty_contexts(&mut self) -> Parsed<Vec<Context>> {
        if lexpat!(self on [|]) {
            let ctxt = self.delimited(
                [Lexeme::Pipe, Lexeme::Comma, Lexeme::Pipe],
                Self::ty_constraint,
            )?;
            self.ignore(Lexeme::FatArrow);
            Ok(ctxt)
        } else {
            Ok(vec![])
        }
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
    fn ty_constraint(&mut self) -> Parsed<Context> {
        let class = self.expect_upper()?;
        let tyvar = self.expect_lower().map(|id| Tv::from(id.get_symbol()))?;
        Ok(Context { class, tyvar })
    }

    fn ty_node(&mut self) -> Parsed<Type> {
        let col = self.get_col();
        let ty = self.ty_atom()?;
        if lexpat!(self on [->]) {
            self.arrow_ty(ty)
        } else if self.peek_on(Lexeme::begins_ty) && self.get_col() > col {
            let ty = self.maybe_ty_app(ty)?;
            self.arrow_ty(ty)
        } else {
            Ok(ty)
        }
    }

    fn maybe_ty_app(&mut self, head: Type) -> Parsed<Type> {
        match head {
            Type::Con(id, mut args) => {
                args.extend(self.many_while_on(Lexeme::begins_ty, Self::ty_atom)?);
                Ok(Type::Con(id, args))
            }
            head => self
                .many_while_on(Lexeme::begins_ty, Self::ty_atom)
                .map(|args| {
                    if args.is_empty() {
                        head
                    } else {
                        args.into_iter()
                            .rev()
                            .map(Box::new)
                            .fold(head, |a, c| Type::App(Box::new(a), c))
                    }
                }),
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
                self.text(),
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

        if self.bump_on(ParenR) {
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
                        self.text(),
                    ));
                }
            }
        }

        self.eat(ParenR)?;
        Ok(ty)
    }

    fn tuple_ty(&mut self, head: Type) -> Parsed<Type> {
        use Lexeme::{Comma, ParenR};
        self.delimited([Comma, Comma, ParenR], Self::ty_node)
            .map(|rest| {
                let mut each = vec![head];
                each.extend(rest);
                Type::Tup(each)
            })
    }

    fn brack_ty(&mut self) -> Parsed<Type> {
        self.eat(Lexeme::BrackL)?;
        let tipo = self.ty_node()?;
        self.eat(Lexeme::BrackR)?;
        Ok(Type::Vec(Rc::new(tipo)))
    }

    fn curly_ty(&mut self) -> Parsed<Type> {
        use Lexeme::{Comma, CurlyL, CurlyR};

        Ok(Type::Rec(Record::Anon(
            self.delimited([CurlyL, Comma, CurlyR], |parse| {
                parse.record_entry_ty(Self::ty_node)
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
                    self.text(),
                ))
            }
        }?;

        if let Pattern::Var(name) = genpat {
            if lexpat!(self on [@]) {
                self.bump();
                return Ok(Pattern::At(name, Box::new(self.pattern()?)));
            }
        }

        // TODO: refactor out `or` patterns so that: 1.) they are only
        // recognized in grouped patterns for alternatives 2.) to stress (1), NO
        // OR PATS IN LAMBDAS 3.) or-patterns will be desugared later anyway
        //
        // if lexpat!(self on [|]) {
        //     self.union_pattern(genpat)
        // } else

        // TODO: restrict casts to grouped patterns only? so as to avoid
        // the ambiguity in function types, e.g., in the case-expression `case
        // EXPR of { PAT :: Foo -> Bar x; ... }` the alternative is semantically
        // complete, but syntactically incomplete, as `PAT :: Foo -> Bar x`
        // would be parsed as the pattern `PAT` being cast as having the type
        // `Foo -> Bar x` before abruptly hitting the end of the entire
        // alternative branch. Compare this with the unambiguous form `case EXPR
        // of { (PAT :: Foo) -> x; ... }`, which is well-formed both
        // semantically and syntactically
        if lexpat!(self on [::]) {
            self.bump();
            Ok(Pattern::Cast(Box::new(genpat), self.ty_node()?))
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
                source: this.text(),
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
    ///
    /// *Identity:* `[a, b, c] = a:b:c:[] = (a:b:c)`
    ///
    /// * `(a : b)       <=> [a, b]`         (bc `[a, b] = a:[b] = a:b:[]`)
    /// * `(a:[])        <=> [a]`            (bc `[a] = a:[]`)
    /// * `(a:[b, c])    <=> [a, b, c]`      (bc `_:[c,d] = _:c:[d] = _:c:d:[]`)
    /// * `(a:b:c:d)     <=> [a, b, c, d]`
    /// * `(a:b:(c:d))   <=> [a, b, c, d]`   (bc right-associative)
    /// * `((a:b):c:d)   <=> [[a, b], c, d]` (implies (a,b :: t) => c,d :: [t])
    fn cons_pattern(&mut self, head: Pattern) -> Parsed<Pattern> {
        let mut elems = vec![head];
        while self.bump_on(Lexeme::Colon) {
            elems.push(self.pattern()?);
        }
        elems.reverse();
        elems
            .into_iter()
            .reduce(|a, c| Pattern::Lnk(Box::new(c), Box::new(a)))
            .ok_or_else(|| {
                ParseError::Custom(
                    self.get_srcloc(),
                    self.lookahead::<1>()[0],
                    "after failure to reduce cons pattern",
                    self.text(),
                )
            })
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
        Ok(self
            .many_while_on(Lexeme::begins_expr, f)?
            .into_iter()
            .fold(head, Expression::mk_app))
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
            let tipo = self.ty_node()?;
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
                self.text(),
            )),
        }
    }

    fn literal(&mut self) -> Parsed<Expression> {
        self.expect_literal().map(Expression::Lit)
    }

    fn identifier(&mut self) -> Parsed<Expression> {
        let ident = match self.peek() {
            lexpat!(~[var]) => self.expect_lower(),
            lexpat!(~[Var]) => self.expect_upper(),
            _ => Err(ParseError::Expected(
                self.get_srcloc(),
                LexKind::Identifier,
                self.bump(),
                self.text(),
            )),
        }?;
        if lexpat!(self on [.]) {
            let tail = self.id_path_tail()?;
            Ok(Expression::Path(ident, tail))
        } else {
            Ok(Expression::Ident(ident))
        }
    }

    fn id_path_tail(&mut self) -> Parsed<Vec<Ident>> {
        self.many_while(
            |p| p.bump_on(Lexeme::Dot) && p.peek_on(Lexeme::is_ident),
            |p| match p.peek() {
                Some(t) if t.is_lower() => p.expect_lower(),
                Some(t) if t.is_upper() => p.expect_upper(),
                Some(t) if t.is_infix() => p.expect_infix(),
                _ => Err(ParseError::Expected(
                    p.get_srcloc(),
                    LexKind::Identifier,
                    p.bump(),
                    p.text(),
                )),
            },
        )
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
                self.text(),
            )),
        }
    }

    /// Syntactic sugar for generating a list of values based on an expression
    /// and a list of satisfied statements. A list comprehension *must* contain
    /// at least __one__ *generator* statement, i.e., a statement of the form
    /// `PAT <- EXPR`. In the event the list of statements is *empty*, the
    /// expression corresponding to each list element is only evaluated once,
    /// and is identical (in value) to an array containing the single
    /// expression.
    ///
    /// Note however, that the expression within the list may introduce new
    /// bindings from the included list of statements. These bindings are scoped
    /// list comprehension, and may shadow any outer free variables.
    ///
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
                return Err(ParseError::UnexpectedEof(srcloc, self.text()));
            }
        }
        self.eat(BrackR)?;

        Ok(Expression::List(Box::new(head), stmts))
    }

    fn lambda(&mut self) -> Parsed<Expression> {
        use Lexeme::{ArrowR, Lambda};
        self.eat(Lambda)?;
        let pats = self.many_while_on(Lexeme::begins_pat, Self::pattern)?;
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
                self.text()
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
                self.text(),
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
            lexpat!(~[|]) => Ok(Binding {
                name,
                tipo: None,
                arms: self.match_arms()?,
            }),
            lexpat!(~[::]) => {
                self.bump();
                let tipo = self.total_signature()?;
                Ok(Binding {
                    name,
                    arms: self.match_arms()?,
                    tipo: Some(tipo),
                })
            }
            lexpat!(maybe[=]) => {
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
            // this shouldn't semantically be ok, BUT i need to check that this
            // method isn't iterated over (instead of match arms)
            lexpat!(~[;]) => Ok(Binding {
                name,
                arms: vec![],
                tipo: None,
            }),
            _ => Err(ParseError::Custom(
                self.get_srcloc(),
                self.lookahead::<1>()[0],
                "unable to parse binding",
                self.text(),
            )),
        }
    }

    /// *SIDE-EFFECT ALERT* this method will advance the parser to the next
    /// token in the beginning of each iteration *if the current token matches*
    /// the pipe `|`.
    fn match_arms(&mut self) -> Parsed<Vec<Match>> {
        use Lexeme::Pipe;
        self.many_while(
            |parser| {
                parser.ignore(Pipe);
                parser.peek_on(Lexeme::begins_pat)
            },
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
        use Keyword::Where;
        use Lexeme::Comma;
        let mut binds = vec![];
        if self.bump_on(Where) {
            binds.push(self.binding()?);
            binds.extend(self.many_while(|p| p.bump_on(Comma), Self::binding)?);
        };
        Ok(binds)
    }

    fn let_expr(&mut self) -> Parsed<Expression> {
        use Keyword::{In, Let};
        use Lexeme::{Comma, Kw};
        Ok(Expression::Let(
            self.delimited([Kw(Let), Comma, Kw(In)], Self::binding)?,
            Box::new(self.expression()?),
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
                pat = Pattern::At(name, Box::new(self.pattern()?))
            } else {
                return Err(ParseError::Custom(
                    self.get_srcloc(),
                    self.bump(),
                    "can only follow simple variable patterns",
                    self.text(),
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

        Ok(Alternative {
            pat,
            pred,
            body: self.expression()?,
            wher: self.where_clause()?,
        })
    }

    fn cond_expr(&mut self) -> Parsed<Expression> {
        self.eat(Keyword::If)?;
        let cond = self.expression()?;
        self.eat(Keyword::Then)?;
        let pass = self.expression()?;
        self.eat(Keyword::Else)?;
        let fail = self.expression()?;

        Ok(Expression::Cond(Box::new([cond, pass, fail])))
    }
}

pub fn try_parse_file<P: AsRef<std::path::Path>>(
    filepath: P,
) -> Result<Program, Failure<ParseError>> {
    let path = filepath.as_ref();
    debug_assert_eq!("ws", path.extension().unwrap());
    let content = std::fs::read_to_string(path)?;
    Parser::new(content.as_str(), Some(path.to_owned()))
        .parse()
        .map_err(Failure::Err)
}

#[cfg(test)]
#[allow(unused)]
mod test;
