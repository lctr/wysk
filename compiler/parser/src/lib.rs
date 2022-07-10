use std::iter;

use meta::*;
use token::*;

use wy_intern::Symbol;
use wy_lexer::*;
use wy_name::ident::{Chain, Ident};
use wy_span::{WithLoc, WithSpan};
use wy_syntax::{
    attr::Attribute,
    decl::{
        AliasDecl, Arity, ClassDecl, DataDecl, Declaration, FixityDecl, FnDecl, InstDecl, Method,
        MethodDef, NewtypeArg, NewtypeDecl, Tag, Variant,
    },
    expr::RawExpression,
    fixity::{Assoc, Fixity, Prec},
    pattern::RawPattern,
    stmt::RawBinding,
    tipo::{Con, Context, Field, Record, Signature, Tv, Type},
    Ast, Import, ImportSpec, Module, Program, RawModule, RawProgram, SyntaxTree,
};

use wy_common::Deque;

pub mod error;
mod expr;
mod fixity;
mod pat;
pub mod stream;

use error::*;

use stream::{Parser, Streaming};

// IDENTIFIERS AND LITERAL
impl<'t> Parser<'t> {
    fn expect_upper(&mut self) -> Parsed<Ident> {
        self.peek()
            .and_then(|t| t.upper_symbol().map(Ident::Upper))
            .map(|id| self.bumped(id))
            .ok_or_else(|| self.expected(LexKind::Upper))
    }

    fn expect_lower(&mut self) -> Parsed<Ident> {
        self.peek()
            .and_then(|t| t.lower_symbol().map(Ident::Lower))
            .map(|id| self.bumped(id))
            .ok_or_else(|| self.expected(LexKind::Lower))
    }

    fn expect_infix(&mut self) -> Parsed<Ident> {
        self.peek()
            .and_then(|t| t.infix_symbol().map(Ident::Infix))
            .map(|id| self.bumped(id))
            .ok_or_else(|| self.expected(LexKind::Infix))
    }

    fn expect_ident(&mut self) -> Parsed<Ident> {
        self.peek()
            .and_then(Token::lift(Lexeme::mk_id(Ident::NAMES)))
            .map(|id| self.bumped(id))
            .ok_or_else(|| self.expected(LexKind::Identifier))
    }

    fn expect_literal(&mut self) -> Parsed<Literal> {
        self.peek()
            .and_then(|t| t.literal())
            .map(|lit| self.bumped(lit))
            .ok_or_else(|| self.expected(LexKind::Literal))
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

    pub fn module(&mut self) -> Parsed<RawModule> {
        self.eat(Keyword::Module)?;
        let modname = self.id_chain()?;
        self.eat(Keyword::Where)?;
        let imports = self.imports()?;
        let mut module = Module {
            modname,
            imports,
            uid: self.filepath.clone(),
            ..Default::default()
        };

        self.populate_module(&mut module)?;
        Ok(module)
    }

    fn populate_module(&mut self, module: &mut RawModule) -> Parsed<()> {
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
            Some(t) if t.is_ident() => self.expect_lower().map(I::Function),
            Some(t) if t.is_infix() => self.expect_infix().map(I::Operator),
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

                    let ctors = self
                        .many_while_on(L::is_ident, |p| p.trailing(L::Comma, Self::expect_ident))?;

                    self.eat(L::ParenR)?;
                    Ok(I::Partial(first, ctors))
                } else {
                    Ok(I::Abstract(first))
                }
            }
            _ => Err(self.custom_error("is not a valid import")),
        }
    }

    pub fn parse(mut self) -> Parsed<RawProgram> {
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
            if let RawBinding {
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
            _ => self.invalid_type().err(),
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

    fn record_entry_ty<F>(&mut self, mut f: F) -> Parsed<Field<Ident, Type>>
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
    pub fn pattern(&mut self) -> Parsed<RawPattern> {
        use Lexeme::{At, BrackL, BrackR, Colon2, Comma, CurlyL, CurlyR, Underline};

        if self.bump_on(Underline) {
            return Ok(RawPattern::Wild);
        };

        let genpat = match self.peek() {
            lexpat!(~[parenL]) => self.grouped_pattern(),

            lexpat!(~[brackL]) => self
                .delimited([BrackL, Comma, BrackR], Self::pattern)
                .map(RawPattern::Vec),

            lexpat!(~[curlyL]) => self.curly_pattern(),

            lexpat!(~[var]) => self.expect_lower().map(RawPattern::Var),

            lexpat!(~[Var]) => {
                let name = self.expect_upper()?;
                if lexpat!(self on [curlyL]) {
                    self.delimited([CurlyL, Comma, CurlyR], Self::field_pattern)
                        .map(|entries| RawPattern::Rec(Record::Data(name, entries)))
                } else {
                    Ok(RawPattern::Dat(name, vec![]))
                }
            }

            lexpat!(~[lit]) => self.lit_pattern(),

            _ => Err(self.custom_error("does not begin a valid pattern")),
        }?;

        if let RawPattern::Var(name) = genpat {
            if self.bump_on(At) {
                return Ok(RawPattern::At(name, Box::new(self.pattern()?)));
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
            Ok(RawPattern::Cast(Box::new(genpat), self.ty_node()?))
        } else {
            Ok(genpat)
        }
    }

    fn lit_pattern(&mut self) -> Parsed<RawPattern> {
        Ok(RawPattern::Lit(self.expect_literal()?))
    }

    fn tuple_pattern_tail(&mut self, first: RawPattern) -> Parsed<RawPattern> {
        use Lexeme::{Comma, ParenR};
        self.delimited([Comma, Comma, ParenR], Self::pattern)
            .map(|rest| std::iter::once(first).chain(rest).collect())
            .map(RawPattern::Tup)
    }

    fn grouped_pattern(&mut self) -> Parsed<RawPattern> {
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
                Ok(RawPattern::UNIT)
            }

            lexpat!(~[Var]) => {
                let upper = self.expect_upper()?;
                let args = self.many_while_on(Lexeme::begins_pat, Self::pattern)?;
                let arity = args.len();
                let mut first = RawPattern::Dat(upper, args);
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
                    RawPattern::At(var, Box::new(self.pattern()?))
                } else {
                    RawPattern::Var(var)
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
                    lexpat!(~[curlyL]) if matches!(&pat, RawPattern::Var(_)) => {
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

    fn con_curly_pattern(&mut self, conid: Ident) -> Parsed<RawPattern> {
        use Lexeme::{Comma, CurlyL, CurlyR};
        Ok(RawPattern::Rec(Record::Data(
            conid,
            self.delimited([CurlyL, Comma, CurlyR], Self::field_pattern)?,
        )))
    }

    fn curly_pattern(&mut self) -> Parsed<RawPattern> {
        use Lexeme::{Comma, CurlyL, CurlyR};

        self.delimited([CurlyL, Comma, CurlyR], Self::field_pattern)
            .map(|ps| RawPattern::Rec(Record::Anon(ps)))
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
    fn cons_pattern(&mut self, head: RawPattern) -> Parsed<RawPattern> {
        let mut elems = vec![head];
        while self.bump_on(Lexeme::Colon) {
            elems.push(self.pattern()?);
        }
        elems.reverse();
        elems
            .into_iter()
            .reduce(|a, c| RawPattern::Lnk(Box::new(c), Box::new(a)))
            .ok_or_else(|| {
                ParseError::Custom(
                    self.srcloc(),
                    self.lookahead::<1>()[0],
                    "after failure to reduce cons pattern",
                    self.text(),
                )
            })
    }

    fn union_pattern(&mut self, first: RawPattern) -> Parsed<RawPattern> {
        let mut rest = Deque::new();
        while self.bump_on(Lexeme::Pipe) {
            rest.push_back(self.pattern()?);
        }
        if rest.is_empty() {
            Ok(first)
        } else {
            Ok(RawPattern::Or({
                rest.push_front(first);
                rest.into_iter().collect()
            }))
        }
    }

    fn field_pattern(&mut self) -> Parsed<Field<Ident, RawPattern>> {
        let key = self.expect_lower()?;
        if self.bump_on(Lexeme::Equal) {
            Ok(Field::Entry(key, self.pattern()?))
        } else {
            Ok(Field::Key(key))
        }
    }

    fn maybe_at_pattern(&mut self) -> Parsed<RawPattern> {
        let mut pat = if self.peek_on(Lexeme::is_upper) {
            let con = self.expect_upper()?;
            let args = self.many_while_on(Lexeme::begins_pat, Self::pattern)?;
            RawPattern::Dat(con, args)
        } else {
            self.pattern()?
        };

        if self.peek_on(Lexeme::At) {
            if let RawPattern::Var(name) = pat {
                pat = RawPattern::At(name, Box::new(self.pattern()?))
            } else {
                return Err(self.custom_error("can only follow simple variable patterns"));
            }
        };

        Ok(pat)
    }
}

pub fn parse_input(src: &str) -> Parsed<RawProgram> {
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
pub fn parse_expression(src: &str) -> Parsed<RawExpression> {
    Parser::from_str(src).expression()
}

pub fn try_parse_file<P: AsRef<std::path::Path>>(
    filepath: P,
) -> Result<RawProgram, Failure<ParseError>> {
    let path = filepath.as_ref();
    let content = std::fs::read_to_string(path)?;
    Parser::new(content.as_str(), Some(path.to_owned()))
        .parse()
        .map_err(Failure::Err)
}

pub fn parse_prelude() -> Parsed<RawProgram> {
    let dirp = "../../../language";
    let src = include_str!("../../../language/prim.wy");
    let prim = Parser::from_str(src).parse()?.map_t(&mut |t| Tv::from(t));
    let ast = SyntaxTree::with_program(prim);
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
    let ast2: Parsed<Ast> = newpaths.into_iter().fold(Ok(ast), |a, c| {
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
