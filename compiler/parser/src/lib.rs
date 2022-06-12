use std::iter;

use meta::*;
use token::*;

use wy_intern::Symbol;
use wy_lexer::*;
use wy_span::{Dummy, WithLoc, WithSpan};
use wy_syntax::{
    attr::Attribute,
    decl::{
        AliasDecl, Arity, ClassDecl, DataDecl, Declaration, FixityDecl, FnDecl, InstDecl, Method,
        MethodDef, NewtypeArg, NewtypeDecl, Tag, Variant,
    },
    expr::{Expression, Section},
    fixity::{Assoc, Fixity, FixityTable, Prec},
    ident::{Chain, Ident},
    pattern::Pattern,
    stmt::{Alternative, Binding, Match, Statement},
    tipo::{Con, Context, Field, Record, Signature, Tv, Type},
    Ast, Import, ImportSpec, Module, Program,
};

use wy_common::Deque;

pub mod error;
pub mod stream;

use error::*;

use stream::Streaming;

type Spath = std::path::PathBuf;

#[derive(Debug)]
pub struct Parser<'t> {
    lexer: Lexer<'t>,
    queue: Deque<Token>,
    pub fixities: FixityTable,
    pub filepath: Option<Spath>,
    pub pragmas: Vec<(Pragma, Placement)>,
}

impl<'t> WithSpan for Parser<'t> {
    fn get_pos(&self) -> BytePos {
        self.lexer.get_pos()
    }
}

impl<'t> WithLoc for Parser<'t> {
    fn get_coord(&self) -> Coord {
        self.lexer.get_coord()
    }
}

impl<'t> Parser<'t> {
    pub fn new(src: &'t str, filepath: Option<Spath>) -> Self {
        Self {
            lexer: Lexer::new(src),
            filepath,
            queue: Deque::new(),
            fixities: FixityTable::new(Ident::Infix),
            pragmas: Vec::new(),
        }
    }

    pub fn from_str(src: &'t str) -> Self {
        Self {
            lexer: Lexer::new(src),
            filepath: None,
            queue: Deque::new(),
            fixities: FixityTable::new(Ident::Infix),
            pragmas: Vec::new(),
        }
    }

    // pub fn peek(&mut self) -> Option<&Token> {
    //     if self.queue.is_empty() {
    //         self.lexer.peek()
    //     } else {
    //         self.queue.front()
    //     }
    // }

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

    pub fn srcloc(&mut self) -> SrcLoc {
        let pathstr = self
            .filepath
            .as_ref()
            .and_then(|p| p.to_str())
            .map(String::from);
        let coord = self.lexer.get_coord();
        SrcLoc { pathstr, coord }
    }

    pub fn eat<T>(&mut self, item: T) -> Parsed<Token>
    where
        T: PartialEq<Token>,
        Token: PartialEq<T>,
        Lexeme: From<T>,
    {
        match self.peek() {
            None
            | Some(Token {
                lexeme: Lexeme::Eof,
                ..
            }) => Err(ParseError::UnexpectedEof(self.srcloc(), self.text())),

            Some(t) if &item == t => Ok(self.bump()),

            Some(t) => match Lexeme::from(item) {
                delim @ (Lexeme::CurlyR | Lexeme::ParenR | Lexeme::BrackR) => {
                    Err(self.unbalanced(delim))
                }
                found => {
                    let tok = t.clone();
                    let src_loc = self.srcloc();
                    Err(ParseError::Expected(
                        src_loc,
                        LexKind::Specified(found),
                        tok,
                        self.text(),
                    ))
                }
            },
        }
    }

    pub fn text(&self) -> String {
        let mut buf = String::new();
        self.lexer.write_to_string(&mut buf);
        buf
    }

    pub fn peek_ahead(&mut self) -> &Token {
        let tok = self.bump();
        self.queue.push_front(tok);
        &self.queue[0]
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
        while pred(self) {
            xs.push(f(self)?);
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
            token
        } else {
            self.lexer.bump()
        }
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
    ($self:ident in [$lexeme:ident $(, $rest:ident)*]) => {{
        let src = $self.get_srcloc();
        let tok = $self.peek().map(|Token {lexeme, ..}| lexeme).copied().unwrap_or_else(|| Lexeme::Eof);
        let any = [$lexeme(_) $(, $rest(_))*];
        if any.cmp_tok(&tok) {
            Ok(tok)
        } else {
            Err($self.expected(LexKind::Any(&[$lexeme(_) $(, $rest(_))*])))
        }
    }};
}

impl<'t> Report for Parser<'t> {
    fn get_srcloc(&mut self) -> SrcLoc {
        Parser::srcloc(self)
    }

    fn get_source(&self) -> String {
        Parser::text(self)
    }

    fn next_token(&mut self) -> Token {
        *self.peek_ahead()
    }
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
                self.srcloc(),
                LexKind::Identifier,
                self.lookahead::<1>()[0],
                self.text(),
            )),
        }
    }

    fn expect_literal(&mut self) -> Parsed<Literal> {
        if let Some(Token {
            lexeme: Lexeme::Lit(lit),
            ..
        }) = self.peek()
        {
            let lit = *lit;
            self.bump();
            Ok(lit)
        } else {
            Err(self.expected(LexKind::Literal))
        }
    }
}

// TOP-LEVEL
type ModuleParser<'t> = Parser<'t>;
impl<'t> ModuleParser<'t> {
    pub fn id_chain(&mut self) -> Parsed<Chain> {
        self.expect_upper().and_then(|root| {
            self.many_while(|p| p.bump_on(Lexeme::Dot), Self::expect_ident)
                .map(|tail| Chain::new(root, tail.into()))
        })
    }

    pub fn module(&mut self) -> Parsed<Module> {
        self.eat(Keyword::Module)?;
        let modname = self.id_chain()?;
        self.eat(Keyword::Where)?;
        let imports = self.imports()?;
        let mut module = Module {
            modname,
            imports,
            ..Default::default()
        };

        self.populate_module(&mut module)?;
        Ok(module)
    }

    fn populate_module(&mut self, module: &mut Module) -> Parsed<()> {
        while !self.is_done() {
            match self.declaration()? {
                Declaration::Data(data) => module.datatys.push(data),
                Declaration::Alias(alias) => module.aliases.push(alias),
                Declaration::Fixity(fixity) => module.infixes.push(fixity),
                Declaration::Class(class) => module.classes.push(class),
                Declaration::Instance(inst) => module.implems.push(inst),
                Declaration::Function(fun) => module.fundefs.push(fun),
                Declaration::Newtype(newty) => module.newtyps.push(newty),
                Declaration::Attribute(attr) => module.pragmas.push(attr),
            }
            self.ignore(Lexeme::Semi)
        }
        Ok(())
    }

    fn imports(&mut self) -> Parsed<Vec<ImportSpec>> {
        use Keyword::Import;
        use Lexeme::{Kw, Pipe};
        self.many_while(|p| p.bump_on([Kw(Import), Pipe]), Self::import_spec)
    }

    fn import_spec(&mut self) -> Parsed<ImportSpec> {
        use Keyword::{Hiding, Qualified};
        use Lexeme::{At, Comma, CurlyL, CurlyR};

        Ok(ImportSpec {
            qualified: self.bump_on(Qualified),
            name: self.id_chain()?,
            rename: if self.bump_on(At) {
                Some(self.expect_upper()?)
            } else {
                None
            },
            hidden: self.bump_on(Hiding),
            imports: if self.peek_on(CurlyL) {
                self.delimited([CurlyL, Comma, CurlyR], Self::import_item)?
            } else {
                Vec::new()
            },
        })
    }

    fn import_item(&mut self) -> Parsed<Import> {
        use Import as I;
        use Lexeme as L;

        match self.peek() {
            lexpat!(~[var]) => self.expect_lower().map(I::Function),
            lexpat!(~[parenL]) => {
                self.eat(L::ParenL)?;
                let infix = self.expect_infix()?;
                self.eat(L::ParenR)?;
                Ok(I::Operator(infix))
            }
            lexpat!(~[Var]) => {
                let first = self.expect_upper()?;
                if self.bump_on(L::ParenL) {
                    if self.bump_on(L::Dot2) {
                        self.eat(L::ParenR)?;
                        return Ok(I::Total(first));
                    }

                    let ctors = self.many_while_on(L::is_ident, |p| {
                        let con = p.expect_ident()?;
                        p.ignore(L::Comma);
                        Ok(con)
                    })?;

                    self.eat(L::ParenR)?;
                    Ok(I::Partial(first, ctors))
                } else {
                    Ok(I::Abstract(first))
                }
            }
            _ => Err(self.custom_error("is not a valid import")),
        }
    }

    pub fn parse(mut self) -> Parsed<Program> {
        use Keyword as K;
        use Module as M;
        Ok(Program {
            module: if self.peek_on(K::Module) {
                self.module()?
            } else {
                let mut module = M::default();
                module.imports = self.many_while_on(K::Import, Self::import_spec)?;
                self.populate_module(&mut module)?;
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
        use Assoc as A;
        let assoc = match self.peek() {
            lexpat!(~[infix]) => Ok(A::None),
            lexpat!(~[infixl]) => Ok(A::Left),
            lexpat!(~[infixr]) => Ok(A::Right),
            _ => Err(self.custom_error("expected fixity keyword `infix`, `infixl`, or `infixr`")),
        }?;
        self.bump();
        Ok(assoc)
    }

    fn fixity_prec(&mut self) -> Parsed<Prec> {
        use Lexeme::Lit;
        use Literal::Int;
        match self.peek() {
            Some(Token {
                lexeme: Lit(Int(p)),
                ..
            }) if *p < 10 => {
                let prec = Prec(*p as u8);
                self.bump();
                Ok(prec)
            }
            _ => Err(ParseError::InvalidPrec(
                self.srcloc(),
                self.bump(),
                self.text(),
            )),
        }
    }

    fn with_fixity(&mut self, fixity: Fixity) -> Parsed<Vec<Ident>> {
        self.many_while_on(Lexeme::is_infix, |p| {
            let srcloc = p.srcloc();
            p.spanned(Self::expect_infix)
                .as_result()
                .and_then(|Spanned(infix, span)| {
                    if p.fixities.contains_key(&infix) {
                        Err(ParseError::FixityExists(srcloc, infix, span, p.text()))
                    } else {
                        p.fixities.insert(infix, fixity);
                        Ok(infix)
                    }
                })
        })
    }
}

type DeclParser<'t> = Parser<'t>;
// DECLARATIONS
impl<'t> DeclParser<'t> {
    pub fn declaration(&mut self) -> Parsed<Declaration> {
        use Declaration as D;
        match self.peek() {
            lexpat!(maybe[infixl][infixr][infix]) => self.fixity_decl().map(D::Fixity),
            lexpat!(~[data]) => self.data_decl().map(D::Data),
            lexpat!(~[fn]) => self.function_decl().map(D::Function),
            lexpat!(~[type]) => self.alias_decl().map(D::Alias),
            lexpat!(~[class]) => self.class_decl().map(D::Class),
            lexpat!(~[impl]) => self.inst_decl().map(D::Instance),
            lexpat!(~[newtype]) => self.newtype_decl().map(D::Newtype),
            lexpat!(~[#]) => self.attribute().map(D::Attribute),
            _ => Err(self.expected(LexKind::Keyword)),
        }
    }

    fn attribute(&mut self) -> Parsed<Attribute<Ident, Ident>> {
        self.eat(Lexeme::Pound)?;
        let _bang = self.bump_on(Lexeme::Bang);
        let is_after = self.lexer.get_mode().is_meta_after();
        self.eat(Lexeme::BrackL)?;
        let _attr = match self.bump() {
            Token {
                lexeme: Lexeme::Meta(pragma),
                span: _,
            } => {
                let pl = if is_after {
                    Placement::After
                } else {
                    Placement::Before
                };
                self.pragmas.push((pragma, pl));
                Ok(())
            }
            t @ Token {
                lexeme: Lexeme::Unknown(_lex),
                span: _,
            } => Err(ParseError::InvalidLexeme(
                self.get_srcloc(),
                t,
                self.get_source(),
            )),
            Token {
                lexeme: Lexeme::Eof,
                span: _,
            } => Err(ParseError::UnexpectedEof(
                self.get_srcloc(),
                self.get_source(),
            )),
            t => Err(self.expected(LexKind::from(t.lexeme))),
        }?;
        self.eat(Lexeme::BrackR)?;
        self.lexer.reset_mode();
        todo!()
    }

    fn fixity_decl(&mut self) -> Parsed<FixityDecl> {
        let assoc = self.fixity_assoc()?;
        let prec = self.fixity_prec()?;
        let fixity = Fixity { prec, assoc };
        let infixes = self.with_fixity(fixity)?;
        Ok(FixityDecl { infixes, fixity })
    }

    fn data_decl(&mut self) -> Parsed<DataDecl<Ident, Ident>> {
        use Keyword::{Data, With};
        use Lexeme::{Comma, Equal, Kw, ParenL, ParenR, Pipe, Semi};

        self.eat(Kw(Data))?;

        let ctxt = if self.peek_on(Pipe) {
            self.delimited([Pipe, Comma, Pipe], Self::ty_constraint)?
        } else {
            vec![]
        };
        let name = self.expect_upper()?;
        let poly = self.many_while_on(Not([Equal, Semi]), |p| {
            p.expect_lower().map(|ident| Ident::Fresh(ident.symbol()))
        })?;
        let mut decl = DataDecl {
            name,
            ctxt,
            poly,
            vnts: vec![],
            with: vec![],
        };

        if self.peek_on(Semi) {
            return Ok(decl);
        }

        self.eat(Equal)?;

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
        let poly = self.many_while_on(Not(Equal), |p| {
            p.expect_lower().map(|ident| Ident::Fresh(ident.symbol()))
        })?;
        self.eat(Equal)?;
        let sign = self.total_signature()?;
        Ok(AliasDecl { name, poly, sign })
    }

    fn class_decl(&mut self) -> Parsed<ClassDecl> {
        self.eat(Keyword::Class)?;
        let ctxt = self.ty_contexts()?;
        let name = self.expect_upper()?;
        let poly = self.many_while_on(Lexeme::is_lower, |p| {
            p.expect_lower().map(|ident| Ident::Fresh(ident.symbol()))
        })?;
        self.eat(Lexeme::CurlyL)?;
        let mut defs = vec![];
        while !self.peek_on(Lexeme::CurlyR) {
            self.ignore(Keyword::Def);
            if let Binding {
                name,
                arms,
                tipo: Some(sign),
            } = self.binding()?
            {
                defs.push(MethodDef {
                    name,
                    sign,
                    body: arms,
                })
            } else {
                return Err(self.custom_error("class method definition without type signature"));
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

    #[allow(unused)]
    fn method_signature(&mut self) -> Parsed<Method> {
        self.eat(Lexeme::Kw(Keyword::Def))?;
        let name = self.binder_name()?;
        self.eat(Lexeme::Colon2)?;
        let tipo = self.total_signature()?;
        Ok(Method::Sig(name, tipo))
    }

    fn inst_decl(&mut self) -> Parsed<InstDecl> {
        self.eat(Keyword::Impl)?;
        let ctxt = self.ty_contexts()?;
        let name = self.expect_upper()?;
        let tipo = self.ty_atom()?;
        self.ignore([Keyword::With, Keyword::Where]);
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

    fn newtype_decl(&mut self) -> Parsed<NewtypeDecl> {
        use Keyword::{Newtype, With};
        use Lexeme::{Colon2, Comma, CurlyL, CurlyR, Equal, ParenL, ParenR};

        fn until_semi_kw(parser: &mut Parser) -> bool {
            !lexpat!(parser on [;] | [kw])
        }

        self.eat(Newtype)?;
        let name = self.expect_upper()?;
        let poly = self.many_while_on(Lexeme::is_lower, Self::expect_lower)?;
        self.eat(Equal)?;
        let ctor = self.expect_upper()?;
        let narg = if self.bump_on(CurlyL) {
            let label = self.expect_lower()?;
            self.eat(Colon2)?;
            let tysig = self.total_signature()?;
            self.eat(CurlyR)?;
            NewtypeArg::Record(label, tysig)
        } else {
            self.many_while(until_semi_kw, Self::ty_node)
                .map(NewtypeArg::Stacked)?
        };
        let with = if self.bump_on(With) {
            if self.peek_on(ParenL) {
                self.delimited([ParenL, Comma, ParenR], Self::expect_upper)?
            } else {
                vec![self.expect_upper()?]
            }
        } else {
            vec![]
        };
        Ok(NewtypeDecl {
            name,
            poly,
            ctor,
            narg,
            with,
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
            args.push(if lexpat!(self on [curlyL]) {
                self.curly_ty()
            } else {
                self.ty_atom()
            }?);
        }
        let arity = Arity::new(args.len());
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
        Ok(Signature {
            each: self.maybe_quantified()?,
            ctxt: self.ty_contexts()?,
            tipo: self.ty_node()?,
        })
    }

    fn maybe_quantified(&mut self) -> Parsed<Vec<Ident>> {
        let mut quants = vec![];
        if self.bump_on(Keyword::Forall) {
            quants = self.many_while_on(Lexeme::is_lower, Self::expect_lower)?;
            self.eat(Lexeme::Dot)?;
        }
        Ok(quants)
    }

    fn ty_contexts(&mut self) -> Parsed<Vec<Context>> {
        use Lexeme::{Comma, Pipe};

        let mut ctxts = vec![];
        if self.peek_on(Pipe) {
            ctxts = self.delimited([Pipe, Comma, Pipe], Self::ty_constraint)?;
        }
        Ok(ctxts)
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
        let head = self.expect_lower()?;
        Ok(Context { class, head })
    }

    fn ty_node(&mut self) -> Parsed<Type> {
        let coord = self.get_coord();
        let ty = self.ty_atom()?;
        if self.peek_on(Lexeme::ArrowR) {
            self.arrow_ty(ty)
        } else if self.peek_on(Lexeme::begins_ty)
            && (self.get_row() == coord.row || self.get_col() > coord.col)
        {
            let ty = self.maybe_ty_app(ty)?;
            self.arrow_ty(ty)
        } else {
            Ok(ty)
        }
    }

    fn maybe_ty_app(&mut self, head: Type) -> Parsed<Type> {
        fn var_or_con(id: Ident) -> impl FnMut(Vec<Type>) -> Type {
            move |args| {
                if args.is_empty() {
                    if id.is_lower() {
                        Type::Var(id)
                    } else {
                        Type::Con(Con::Data(id), vec![])
                    }
                } else {
                    Type::Con(
                        if id.is_lower() {
                            Con::Free(id)
                        } else {
                            Con::Data(id)
                        },
                        args,
                    )
                }
            }
        }
        match head {
            Type::Var(id) => self
                .many_while_on(Lexeme::begins_ty, Self::ty_atom)
                .map(var_or_con(id)),
            Type::Con(id, mut args) => self
                .many_while_on(Lexeme::begins_ty, Self::ty_atom)
                .map(|mut rest| args.append(&mut rest))
                .map(|_| Type::Con(id, args)),
            head => Ok(head),
        }
    }

    fn ty_atom(&mut self) -> Parsed<Type> {
        match self.peek() {
            lexpat!(~[var]) => self.expect_lower().map(Type::Var),
            lexpat!(~[Var]) => self
                .expect_upper()
                .map(|con| Type::Con(Con::Data(con), vec![])),
            lexpat!(~[brackL]) => self.brack_ty(),
            // lexpat!(~[curlyL]) => self.curly_ty(),
            lexpat!(~[parenL]) => self.paren_ty(),
            _ => Err(self.custom_error("does not begin a type")),
        }
    }

    fn arrow_ty(&mut self, head: Type) -> Parsed<Type> {
        let mut rest = vec![];
        while self.bump_on(Lexeme::ArrowR) {
            rest.push(self.ty_atom().and_then(|right| self.maybe_ty_app(right))?);
        }

        Ok(if rest.is_empty() {
            head
        } else {
            iter::once(head)
                .chain(rest)
                .rev()
                .reduce(|a, c| Type::mk_fun(c, a))
                .unwrap()
        })
    }

    fn paren_ty(&mut self) -> Parsed<Type> {
        use Lexeme::{ParenL, ParenR};
        self.eat(ParenL)?;

        if self.bump_on(ParenR) {
            return Ok(Type::UNIT);
        }

        let mut ty = self.ty_atom()?;

        let mut args = vec![];
        match ty {
            Type::Var(n) | Type::Con(Con::Data(n) | Con::Free(n), _)
                if self.peek_on(Lexeme::begins_pat) =>
            {
                while !(self.is_done() || lexpat!(self on [parenR]|[,]|[->])) {
                    if !self.peek_on(Lexeme::begins_ty) {
                        return Err(ParseError::Expected(
                            self.srcloc(),
                            LexKind::AnyOf(&[LexKind::Upper, LexKind::Lower]),
                            self.lookahead::<1>()[0],
                            self.text(),
                        ));
                    };
                    args.push(self.ty_atom()?);
                }
                ty = Type::Con(Con::Data(n), args)
            }
            _ => (),
        }
        while !(self.is_done() || self.peek_on(ParenR)) {
            match self.peek() {
                lexpat!(~[,]) => return self.tuple_ty_tail(ty),
                lexpat!(~[->]) => {
                    ty = self.arrow_ty(ty)?;
                    break;
                }
                _ => {
                    return Err(ParseError::Unbalanced {
                        srcloc: self.srcloc(),
                        found: self.bump(),
                        delim: Lexeme::ParenR,
                        source: self.text(),
                    })
                }
            }
        }

        self.eat(ParenR)?;
        Ok(ty)
    }

    fn tuple_ty_tail(&mut self, head: Type) -> Parsed<Type> {
        use Lexeme::{Comma, ParenR};
        self.delimited([Comma, Comma, ParenR], Self::ty_node)
            .map(|rest| Type::Tup(std::iter::once(head).chain(rest).collect()))
    }

    fn brack_ty(&mut self) -> Parsed<Type> {
        self.eat(Lexeme::BrackL)?;
        if self.bump_on(Lexeme::BrackR) {
            let var = Type::Var(Ident::Lower(Symbol::from_str("a")));
            Ok(Type::Vec(Box::new(var)))
        } else {
            let tipo = self.ty_node()?;
            self.eat(Lexeme::BrackR)?;
            Ok(Type::Vec(Box::new(tipo)))
        }
    }

    pub fn curly_ty(&mut self) -> Parsed<Type> {
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
        use Lexeme::{At, BrackL, BrackR, Colon2, Comma, CurlyL, CurlyR, Underline};

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

            _ => Err(self.custom_error("does not begin a valid pattern")),
        }?;

        if let Pattern::Var(name) = genpat {
            if self.bump_on(At) {
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
        if self.bump_on(Colon2) {
            Ok(Pattern::Cast(Box::new(genpat), self.ty_node()?))
        } else {
            Ok(genpat)
        }
    }

    fn lit_pattern(&mut self) -> Parsed<Pattern> {
        Ok(Pattern::Lit(self.expect_literal()?))
    }

    fn tuple_pattern_tail(&mut self, first: Pattern) -> Parsed<Pattern> {
        use Lexeme::{Comma, ParenR};
        self.delimited([Comma, Comma, ParenR], Self::pattern)
            .map(|rest| std::iter::once(first).chain(rest).collect())
            .map(Pattern::Tup)
    }

    fn grouped_pattern(&mut self) -> Parsed<Pattern> {
        use Lexeme::{ParenL, ParenR};

        let pat_err = |this: &mut Self| {
            Err(ParseError::Unbalanced {
                srcloc: this.srcloc(),
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
                        lexpat!(~[,]) => return self.tuple_pattern_tail(first),
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
                    lexpat!(~[,]) => self.tuple_pattern_tail(pat),
                    lexpat!(~[|]) => {
                        let pat = self.union_pattern(pat)?;
                        self.eat(ParenR)?;
                        Ok(pat)
                    }
                    lexpat!(~[:]) => {
                        let pat = self.cons_pattern(pat)?;
                        if lexpat!(self on [,]) {
                            return self.tuple_pattern_tail(pat);
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
                    lexpat! {~[,]} => self.tuple_pattern_tail(first),
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
                    self.srcloc(),
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
        let key = self.expect_lower()?;
        if self.bump_on(Lexeme::Equal) {
            Ok(Field::Entry(key, self.pattern()?))
        } else {
            Ok(Field::Key(key))
        }
    }

    fn maybe_at_pattern(&mut self) -> Parsed<Pattern> {
        let mut pat = if self.peek_on(Lexeme::is_upper) {
            let con = self.expect_upper()?;
            let args = self.many_while_on(Lexeme::begins_pat, Self::pattern)?;
            Pattern::Dat(con, args)
        } else {
            self.pattern()?
        };

        if self.peek_on(Lexeme::At) {
            if let Pattern::Var(name) = pat {
                pat = Pattern::At(name, Box::new(self.pattern()?))
            } else {
                return Err(self.custom_error("can only follow simple variable patterns"));
            }
        };

        Ok(pat)
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
        while self.peek_on(Lexeme::is_infix) {
            let infix = self.expect_infix()?;
            left = Expression::Infix {
                left: Box::new(left),
                infix,
                right: self.maybe_binary(f).map(Box::new)?,
            };
        }

        if self.bump_on(Lexeme::Colon2) {
            self.ty_node()
                .map(|tipo| Expression::Cast(Box::new(left), tipo))
        } else {
            Ok(left)
        }
    }

    fn negation(&mut self) -> Parsed<Expression> {
        if self.bump_on(Lexeme::is_minus_sign) {
            self.negation().map(Box::new).map(Expression::Neg)
        } else {
            self.atom()
        }
    }

    fn atom(&mut self) -> Parsed<Expression> {
        match self.peek() {
            Some(t) if t.lexeme.is_minus_sign() => self.negation(),
            lexpat!(~[parenL]) => self.paren_expr(),
            lexpat!(~[brackL]) => self.brack_expr(),
            lexpat!(~[let]) => self.let_expr(),
            lexpat!(~[case]) => self.case_expr(),
            lexpat!(~[if]) => self.cond_expr(),
            lexpat!(~[do]) => self.do_expr(),
            lexpat!(~[lam]) => self.lambda(),
            lexpat!(~[lit]) => self.literal(),
            lexpat!(~[var][Var]) => self.identifier(),
            _ => {
                Err(self.custom_error("does not correspond to a lexeme that begins an expression"))
            }
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
                self.srcloc(),
                LexKind::Identifier,
                self.bump(),
                self.text(),
            )),
        }?;
        match self.peek() {
            lexpat!(~[.]) => {
                let tail = self.id_path_tail()?;
                Ok(Expression::Path(ident, tail))
            }
            lexpat!(~[curlyL]) => Ok(Expression::Dict(Record::Data(ident, self.curly_expr()?))),
            _ => Ok(Expression::Ident(ident)),
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
                    p.srcloc(),
                    LexKind::Identifier,
                    p.bump(),
                    p.text(),
                )),
            },
        )
    }

    fn comma_section(&mut self) -> Parsed<Expression> {
        use Lexeme::{Comma, ParenR};
        let mut commas = 0;
        while self.bump_on(Comma) {
            commas += 1;
        }
        let prefix = Ident::mk_tuple_commas(commas);

        Ok(if self.bump_on(ParenR) {
            Expression::Ident(prefix)
        } else {
            let section = self
                .expression()
                .map(Box::new)
                .map(|right| Section::Prefix { prefix, right })?;
            self.eat(ParenR)?;
            Expression::Section(section)
        })
    }

    fn maybe_prefix_section(&mut self) -> Parsed<Expression> {
        let prefix = self.expect_infix()?;
        if !self.peek_on(Lexeme::ParenR) {
            let right = self.subexpression().map(Box::new)?;
            self.eat(Lexeme::ParenR)?;
            return Ok(Expression::Section(Section::Prefix { prefix, right }));
        }
        self.eat(Lexeme::ParenR)?;
        Ok(Expression::Group(Box::new(Expression::Ident(prefix))))
    }

    fn suffix_section(&mut self, left: Expression) -> Parsed<Expression> {
        let suffix = self.expect_infix()?;
        self.eat(Lexeme::ParenR)?;
        return Ok(Expression::Section(Section::Suffix {
            suffix,
            left: Box::new(left),
        }));
    }

    fn paren_expr(&mut self) -> Parsed<Expression> {
        use Lexeme::{Comma, ParenL, ParenR};
        self.eat(ParenL)?;
        if self.peek_on(ParenR) {
            self.bump();
            return Ok(Expression::UNIT);
        }

        if self.bump_on(Comma) {
            return self.comma_section();
        }

        if self.peek_on(Lexeme::is_infix) {
            return self.maybe_prefix_section();
        }

        let mut first = self.expression()?;

        if self.peek_on(Lexeme::is_infix) {
            return self.suffix_section(first);
        }

        if self.peek_on(Comma) {
            use std::iter::once;
            return self
                .delimited([Comma, Comma, ParenR], &mut Self::subexpression)
                .map(|rest| once(first).chain(rest).collect())
                .map(Expression::Tuple);
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
        use Lexeme::{BrackL, BrackR, Comma, Dot2};
        self.eat(BrackL)?;
        if self.bump_on(BrackR) {
            return Ok(Expression::NULL);
        }

        let first = self.expression()?;

        if self.bump_on(Dot2) {
            return Ok(Expression::Range(
                Box::new(first),
                if self.bump_on(BrackR) {
                    None
                } else {
                    let end = self.subexpression()?;
                    self.eat(BrackR)?;
                    Some(Box::new(end))
                },
            ));
        };

        match self.peek() {
            lexpat!(~[brackR]) => {
                self.bump();
                Ok(Expression::Array(vec![first]))
            }
            lexpat!(~[|]) => self.list_comprehension(first),

            lexpat!(~[,]) => self
                .delimited([Comma, Comma, BrackR], Self::expression)
                .map(|xs| std::iter::once(first).chain(xs).collect::<Vec<_>>())
                .map(Expression::Array),

            _ => Err(ParseError::Unbalanced {
                srcloc: self.srcloc(),
                found: self.bump(),
                delim: BrackR,
                source: self.text(),
            }),
        }
    }

    fn curly_expr(&mut self) -> Parsed<Vec<Field<Expression>>> {
        use Lexeme::{Comma, CurlyL, CurlyR, Dot2, Equal};
        self.delimited([CurlyL, Comma, CurlyR], |p| {
            if p.bump_on(Dot2) {
                return Ok(Field::Rest);
            }

            let label = p.expect_lower()?;
            Ok(if p.bump_on(Equal) {
                Field::Entry(label, p.expression()?)
            } else {
                Field::Key(label)
            })
        })
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
        use Lexeme::{BrackR, Comma, Pipe};
        self.eat(Pipe)?;

        let mut stmts = vec![];
        loop {
            if self.bump_on(BrackR) {
                break Ok(Expression::List(Box::new(head), stmts));
            }
            let srcloc = self.srcloc();

            stmts.push(self.statement()?);
            self.ignore(Comma);
            if self.is_done() {
                break Err(ParseError::UnexpectedEof(srcloc, self.text()));
            }
        }
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
            Err(self.custom_error("is not a valid binding name: expected a lowercase-initial identifier or an infix wrapped in parentheses"))
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
            Err(self.custom_error("is not a valid binding argument pattern"))
        }
    }

    fn binding_rhs(&mut self) -> Parsed<(Expression, Vec<Binding>)> {
        let body = self.expression()?;
        let wher = self.where_clause()?;
        Ok((body, wher))
    }

    fn caf_binding(&mut self, name: Ident, tipo: Option<Signature>) -> Parsed<Binding> {
        self.binding_rhs().map(|(body, wher)| Binding {
            name,
            tipo,
            arms: vec![Match::caf(body, wher)],
        })
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
                let tipo = self.total_signature().map(Some)?;
                self.ignore(Lexeme::Comma);
                if lexpat!(self on [=]|[=>]) {
                    self.bump();
                    self.caf_binding(name, tipo)
                } else {
                    self.match_arms().map(|arms| Binding { name, arms, tipo })
                }
            }
            lexpat!(~[=>]) => {
                self.bump();
                self.caf_binding(name, None)
            }
            lexpat!(~[=]) => {
                self.bump();
                self.binding_rhs().and_then(|(body, wher)| {
                    self.match_arms().map(|arms| Binding {
                        name,
                        tipo: None,
                        arms: iter::once(Match::caf(body, wher)).chain(arms).collect(),
                    })
                })
            }
            Some(t) if t.begins_pat() || t.lexeme == Pipe => {
                self.match_arms().map(|arms| Binding {
                    name,
                    tipo: None,
                    arms,
                })
            }
            // this shouldn't semantically be ok, BUT i need to check that this
            // method isn't iterated over (instead of match arms)
            lexpat!(~[;]) => Ok(Binding {
                name,
                arms: vec![],
                tipo: None,
            }),
            _ => Err(self.custom_error("unable to parse binding")),
        }
    }

    fn match_arms(&mut self) -> Parsed<Vec<Match>> {
        use Lexeme::Pipe;
        self.many_while(
            |this| {
                this.ignore(Pipe);
                this.peek_on(Lexeme::begins_pat)
            },
            Self::match_arm,
        )
    }

    fn match_arm(&mut self) -> Parsed<Match> {
        use Lexeme::{Equal, FatArrow};

        // syntactic shorthand for `| =`
        let (args, pred) = if self.bump_on(FatArrow) {
            (vec![], None)
        } else {
            let (args, pred) = self.binding_lhs()?;
            self.eat(Equal)?;
            (args, pred)
        };

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
        Ok(Alternative {
            pat: self.maybe_at_pattern()?,
            pred: if self.bump_on(Keyword::If) {
                Some(self.subexpression()?)
            } else {
                None
            },
            body: {
                self.eat(Lexeme::ArrowR)?;
                self.expression()?
            },
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

    fn do_expr(&mut self) -> Parsed<Expression> {
        self.eat(Keyword::Do)?;
        self.eat(Lexeme::CurlyL)?;

        let mut statements = self.many_while_on(Not(Lexeme::is_brack_r), |p| {
            let stmt = p.statement()?;
            p.ignore(Lexeme::Semi);
            Ok(stmt)
        })?;

        self.eat(Lexeme::CurlyR)?;

        let msg = "do expression must end in an expression";
        statements
            .pop()
            .ok_or_else(|| self.custom_error(msg))
            .and_then(|s| {
                if let Statement::Predicate(g) = s {
                    Ok(Box::new(g))
                } else {
                    Err(self.custom_error(msg))
                }
            })
            .map(|tail| Expression::Do(statements, tail))
    }

    fn statement(&mut self) -> Parsed<Statement> {
        fn bump_comma(parser: &mut Parser) -> bool {
            parser.bump_on(Lexeme::Comma)
        }
        match self.peek() {
            lexpat!(~[do]) => self.do_expr().map(Statement::Predicate),
            lexpat!(~[let]) => {
                self.eat(Keyword::Let)?;
                let mut bindings = vec![self.binding()?];
                self.many_while(bump_comma, Self::binding)
                    .map(|binds| bindings.extend(binds))?;
                if self.bump_on(Keyword::In) {
                    Ok(Statement::Predicate(Expression::Let(
                        bindings,
                        Box::new(self.expression()?),
                    )))
                } else {
                    Ok(Statement::JustLet(bindings))
                }
            }
            lexpat!(~[var]) => {
                let lower = self.expect_ident()?;
                if self.bump_on(Lexeme::ArrowL) {
                    self.expression()
                        .map(|ex| Statement::Generator(Pattern::Var(lower), ex))
                } else {
                    Ok(Statement::Predicate(
                        self.many_while_on(Lexeme::begins_expr, Self::expression)?
                            .into_iter()
                            .fold(Expression::Ident(lower), Expression::mk_app),
                    ))
                }
            }
            lexpat!(~[Var]) => {
                let pat = self.pattern()?;
                self.eat(Lexeme::ArrowL)?;
                Ok(Statement::Generator(pat, self.expression()?))
            }
            lexpat!(~[_]) => {
                self.bump();
                self.eat(Lexeme::ArrowL)?;
                let expr = self.expression()?;
                Ok(Statement::Generator(Pattern::Wild, expr))
            }
            Some(t) if t.begins_pat() => {
                let lexer = self.lexer.clone();
                let queue = self.queue.clone();
                let pat = self.pattern()?;
                if self.bump_on(Lexeme::ArrowL) {
                    Ok(Statement::Generator(pat, self.expression()?))
                } else {
                    self.lexer = lexer;
                    self.queue = queue;
                    Ok(Statement::Predicate(self.expression()?))
                }
            }
            Some(t) if t.begins_expr() => self.expression().map(Statement::Predicate),
            _ => Err(self.custom_error("is not supported in `do` expressions")),
        }
    }
}

pub fn parse_input(src: &str) -> Parsed<Program> {
    Parser::from_str(src).parse()
}

/// Parsing the type portion of a type signature in an isolated context
#[allow(unused)]
pub fn parse_type_node(src: &str) -> Parsed<Type> {
    Parser::from_str(src).ty_node()
}

/// Parsing a type signature in an isolated context
#[allow(unused)]
pub fn parse_type_signature(src: &str) -> Parsed<Signature> {
    Parser::from_str(src).total_signature()
}

/// Parsing en expression in an isolated context
#[allow(unused)]
pub fn parse_expression(src: &str) -> Parsed<Expression> {
    Parser::from_str(src).expression()
}

pub fn try_parse_file<P: AsRef<std::path::Path>>(
    filepath: P,
) -> Result<Program, Failure<ParseError>> {
    let path = filepath.as_ref();
    let content = std::fs::read_to_string(path)?;
    Parser::new(content.as_str(), Some(path.to_owned()))
        .parse()
        .map_err(Failure::Err)
}

pub fn parse_prelude() -> Parsed<Program> {
    let dirp = "../../../language";
    let src = include_str!("../../../language/prim.wy");
    let prim = Parser::from_str(src).parse()?.map_t(&mut |t| Tv::from(t));
    let ast = Ast::with_program(prim);
    let imported_modules =
        ast.imported_modules()
            .into_iter()
            .map(|(uid, chain)| {
                let path = chain.symbols().map(|sym| sym.display()).fold(
                    String::from(dirp),
                    |mut a, c| {
                        a.push('/');
                        a.push_str(&*c);
                        a
                    },
                );
                (uid, path)
            })
            .collect::<Vec<_>>();
    println!("imported modules: {:?}", &imported_modules);
    let mut newpaths = vec![];
    for dir in std::fs::read_dir(dirp) {
        for item in dir {
            match item {
                Ok(entry) => {
                    for (_uid, pth) in &imported_modules {
                        if entry.path().ends_with(pth) {
                            newpaths.push(entry.path());
                        }
                    }
                }
                Err(e) => {
                    println!("{}", e);
                }
            }
        }
    }
    println!("newpaths: {:?}", &newpaths);
    let ast2: Parsed<Ast<Ident>> = newpaths.into_iter().fold(Ok(ast), |a, c| {
        let mut a = a?;
        a.add_program(try_parse_file(c).map_err(|failure| match failure {
            Failure::Err(p) => p,
            Failure::Io(e) => panic!("{}", e),
        })?);
        Ok(a)
    });
    println!("AST2: {:#?}", &ast2);
    todo!()
}

#[cfg(test)]
#[allow(unused)]
mod test;
