use std::iter;

use wy_intern::Symbol;
use wy_lexer::lexpat;
use wy_lexer::token::{LexKind, Token};
use wy_lexer::Keyword;
use wy_lexer::Lexeme;
use wy_name::ident::Ident;
use wy_span::WithLoc;
use wy_syntax::record::Field;
use wy_syntax::record::Record;
use wy_syntax::tipo::Con;
use wy_syntax::tipo::Context;
use wy_syntax::tipo::Signature;
use wy_syntax::tipo::Type;

use crate::error::*;
use crate::stream::*;

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
    pub(crate) fn total_signature(&mut self) -> Parsed<Signature> {
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

    pub(crate) fn ty_contexts(&mut self) -> Parsed<Vec<Context>> {
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
    pub(crate) fn ty_constraint(&mut self) -> Parsed<Context> {
        let class = self.expect_upper()?;
        let head = self.expect_lower()?;
        Ok(Context { class, head })
    }

    pub(crate) fn ty_node(&mut self) -> Parsed<Type> {
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

    pub(crate) fn ty_atom(&mut self) -> Parsed<Type> {
        match self.peek() {
            Some(t) if t.is_lower() => self.expect_lower().map(Type::Var),
            Some(t) if t.is_upper() => self
                .expect_upper()
                .map(|con| Type::Con(Con::Data(con), vec![])),
            Some(t) if t.is_brack_l() => self.brack_ty(),
            // Some(t) if t.is_curly_l()  => self.curly_ty(),
            Some(t) if t.is_paren_l() => self.paren_ty(),
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_type_app() {
        let src = "Foo x y z -> Bar (z, y) x";
        let result = Parser::from_str(src).ty_node().unwrap();
        println!("{}", &result);
        let var = Ident::Lower;
        let [foo_ty, x, y, z, bar_ty] = wy_intern::intern_many(["Foo", "x", "y", "z", "Bar"]);
        assert_eq!(
            result,
            Type::Fun(
                Box::new(Type::Con(
                    Con::Data(Ident::Upper(foo_ty)),
                    vec![Type::Var(var(x)), Type::Var(var(y)), Type::Var(var(z))],
                )),
                Box::new(Type::Con(
                    Con::Data(Ident::Upper(bar_ty)),
                    vec![
                        Type::Tup(vec![Type::Var(var(z)), Type::Var(var(y)),]),
                        Type::Var(var(x))
                    ]
                ))
            )
        )
    }

    #[test]
    fn test_arrow_ty_assoc() {
        let src = "a -> b -> c -> d";
        let result = Parser::from_str(src).ty_node().unwrap();
        println!("{}", &result);
        let [a, b, c, d] = wy_intern::intern_many(["a", "b", "c", "d"]);
        let expected = Type::Fun(
            Box::new(Type::Var(Ident::Lower(a))),
            Box::new(Type::Fun(
                Box::new(Type::Var(Ident::Lower(b))),
                Box::new(Type::Fun(
                    Box::new(Type::Var(Ident::Lower(c))),
                    Box::new(Type::Var(Ident::Lower(d))),
                )),
            )),
        );
        assert_eq!(result, expected)
    }

    #[test]
    fn test_ty_sigs() {
        let src = r#"forall a b. m a -> (a -> m b) -> m b"#;
        let sig = Parser::from_str(src).total_signature().unwrap();
        let [a, b, m] = wy_intern::intern_many(["a", "b", "m"]);
        let expected = Signature {
            each: vec![Ident::Lower(a), Ident::Lower(b)],
            ctxt: vec![],
            tipo: Type::Fun(
                Box::new(Type::Con(
                    Con::Free(Ident::Lower(m)),
                    vec![Type::Var(Ident::Lower(a))],
                )),
                Box::new(Type::Fun(
                    Box::new(Type::Fun(
                        Box::new(Type::Var(Ident::Lower(a))),
                        Box::new(Type::Con(
                            Con::Free(Ident::Lower(m)),
                            vec![Type::Var(Ident::Lower(b))],
                        )),
                    )),
                    Box::new(Type::Con(
                        Con::Free(Ident::Lower(m)),
                        vec![Type::Var(Ident::Lower(b))],
                    )),
                )),
            ),
        };
        println!("showing ty sigs: {:#?}\n{}", &sig, &sig.tipo);
        assert_eq!(expected, sig)
    }
}
