use std::iter;

use wy_intern::Symbol;
use wy_lexer::lexpat;
use wy_lexer::token::{LexKind, Token};
use wy_lexer::Keyword;
use wy_lexer::Lexeme;
use wy_name::ident::Ident;
use wy_span::{Span, Spanned, WithLoc, WithSpan};
use wy_syntax::record::Field;
use wy_syntax::record::Record;
use wy_syntax::tipo::{Annotation, Type};
use wy_syntax::tipo::{Con, Quantified, Signature};
use wy_syntax::tipo::{Parameter, Predicate};
use wy_syntax::tipo::{Qualified, SimpleType};
use wy_syntax::SpannedIdent;

use crate::error::*;
use crate::stream::*;

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
    pub(crate) fn ty_signature(&mut self) -> Parsed<Signature> {
        Ok(if self.bump_on(Lexeme::Colon2) {
            Signature::Explicit(self.ty_annotation()?)
        } else {
            Signature::Implicit
        })
    }

    pub(crate) fn ty_annotation(&mut self) -> Parsed<Annotation> {
        let quant = self.maybe_quantified()?;
        let qual = self.maybe_qualified()?;
        Ok(Annotation { quant, qual })
    }

    pub(crate) fn maybe_quantified(&mut self) -> Parsed<Quantified<SpannedIdent, SpannedIdent>> {
        let mut quants = vec![];
        if self.bump_on(Keyword::Forall) {
            quants = self.many_while_on(Lexeme::is_lower, Self::expect_lower)?;
            self.eat(Lexeme::Dot)?;
        }
        Ok(quants.into_iter().map(|id| (id, id)).collect())
    }

    pub(crate) fn maybe_qualified(&mut self) -> Parsed<Qualified> {
        let pred = self.ty_predicates()?;
        let tipo = self.ty_node()?;
        Ok(Qualified { pred, tipo })
    }

    pub(crate) fn ty_predicates(&mut self) -> Parsed<Vec<Predicate>> {
        use Lexeme::{Comma, Pipe};

        let mut ctxts = vec![];
        if self.peek_on(Pipe) {
            ctxts = self
                .delimited([Pipe, Comma, Pipe], Self::ty_predicates_sugared)?
                .into_iter()
                .flatten()
                .collect();
        }
        Ok(ctxts)
    }

    #[allow(unused)]
    fn ty_predicate(&mut self) -> Parsed<Predicate> {
        let class = self.expect_upper()?;
        let head = self.predicate_parameter()?;
        Ok(Predicate { class, head })
    }

    fn predicate_parameter(&mut self) -> Parsed<Parameter<SpannedIdent>> {
        Ok(if self.bump_on(Lexeme::ParenL) {
            let con = self.expect_lower()?;
            let tail = self.many_while_on(Lexeme::is_lower, Self::expect_lower)?;
            Parameter(con, tail)
        } else {
            Parameter(self.expect_lower()?, vec![])
        })
    }

    /// Experimental syntax sugar for parsing predicates.
    /// A predicate of the form `|A x1, A x2, ..., A xn|` may be
    /// written in the more compact form `|A {x1, x2, ..., xn}|`.
    ///
    /// Thus it follows that this method returns a vector of
    /// predicates, all of which are to be flattened together.
    fn ty_predicates_sugared(&mut self) -> Parsed<Vec<Predicate>> {
        let class = self.expect_upper()?;
        if self.peek_on(Lexeme::CurlyL) {
            self.delimited(
                [Lexeme::CurlyL, Lexeme::Comma, Lexeme::CurlyR],
                Self::predicate_parameter,
            )
            .map(|parameters| {
                parameters
                    .into_iter()
                    .map(|head| Predicate { class, head })
                    .collect()
            })
        } else {
            self.predicate_parameter()
                .map(|head| vec![Predicate { class, head }])
        }
    }

    pub(crate) fn ty_simple(&mut self) -> Parsed<SimpleType> {
        let con = self.expect_upper()?;
        let vars = self.many_while_on(Lexeme::is_lower, Self::expect_lower)?;
        Ok(SimpleType(con, vars))
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
        fn var_or_con(id: SpannedIdent) -> impl FnMut(Vec<Type>) -> Type {
            move |args| {
                if args.is_empty() {
                    if id.item().is_lower() {
                        Type::Var(id)
                    } else {
                        Type::Con(Con::Named(id), vec![])
                    }
                } else {
                    Type::Con(
                        if id.item().is_lower() {
                            Con::Free(id)
                        } else {
                            Con::Named(id)
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
                .map(|con| Type::Con(Con::Named(con), vec![])),
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
        use Lexeme::{Comma, ParenL, ParenR};
        self.eat(ParenL)?;

        if self.bump_on(ParenR) {
            return Ok(Type::UNIT);
        }

        // check if we are on `(,···,)` where `···` represents
        // arbitrarily many commas
        if self.peek_on(Comma) {
            let mut ct = 0;
            while self.bump_on(Comma) {
                ct += 1;
            }
            self.eat(ParenR)?;
            // TODO LATER: ensure in type checking that the number of
            // type atoms is AT MOST one more than the comma count
            // `ct` above
            return self
                .many_while_on(Lexeme::begins_ty, Self::ty_atom)
                .map(|args| Type::Con(Con::Tuple(ct), args));
        }

        let mut ty = self.ty_atom()?;

        let mut args = vec![];
        match ty {
            Type::Var(n) | Type::Con(Con::Named(n) | Con::Free(n), _)
                if self.peek_on(Lexeme::begins_ty) =>
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
                ty = Type::Con(Con::Named(n), args)
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
        let start = self.get_pos();
        self.eat(Lexeme::BrackL)?;
        if self.bump_on(Lexeme::BrackR) {
            let end = self.get_pos();
            if self.peek_on(Lexeme::begins_ty) {
                let of = self.ty_atom()?;
                if self.peek_on(Lexeme::begins_ty) {
                    Err(self.custom_error("invalid type application of `[]`! The type constructor `[]` expects only one type argument, but a second argument was found"))
                } else {
                    Ok(Type::Con(Con::List, vec![of]))
                }
            } else {
                let var = Type::Var(Spanned(
                    Ident::Lower(Symbol::from_str("a")),
                    Span(start, end),
                ));
                Ok(Type::Vec(Box::new(var)))
            }
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

    fn record_entry_ty<F>(&mut self, mut f: F) -> Parsed<Field<SpannedIdent, Type>>
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
    use wy_common::functor::{Func, MapFst, MapSnd};
    use wy_syntax::{ast::spanless_eq::Spanless, tipo::Var};

    use super::*;

    const LOWER: fn(Symbol) -> Ident = Ident::Lower;
    const UPPER: fn(Symbol) -> Ident = Ident::Upper;
    const VAR_T: fn(Symbol) -> Type<Ident, Ident> = |id| Type::Var(LOWER(id));

    #[test]
    fn test_tuple_prefix_form() {
        let [a, b, c, b00l] = Symbol::intern_many(["a", "b", "c", "Bool"]);
        let bool_tycon = Con::Named(UPPER(b00l));
        for (src, expected) in [
            (
                "(,,,) a b c Bool",
                Type::Con(
                    Con::Tuple(3),
                    vec![VAR_T(a), VAR_T(b), VAR_T(c), Type::Con(bool_tycon, vec![])],
                ),
            ),
            (
                "(,,,) ((,,) a b c) ((,) a Bool) ((,) b Bool) ((,) c Bool)",
                Type::Con(
                    Con::Tuple(3),
                    vec![
                        Type::Con(Con::Tuple(2), vec![VAR_T(a), VAR_T(b), VAR_T(c)]),
                        Type::Con(Con::Tuple(1), vec![VAR_T(a), Type::Con(bool_tycon, vec![])]),
                        Type::Con(Con::Tuple(1), vec![VAR_T(b), Type::Con(bool_tycon, vec![])]),
                        Type::Con(Con::Tuple(1), vec![VAR_T(c), Type::Con(bool_tycon, vec![])]),
                    ],
                ),
            ),
        ] {
            Parser::from_str(src)
                .ty_node()
                .map(|ty| {
                    ty.map_fst(&mut Func::Fresh(Spanned::take_item))
                        .map_snd(&mut Func::Fresh(Spanned::take_item))
                })
                .map(|result| assert_eq!(result, expected))
                .unwrap();
        }
    }

    #[test]
    fn test_list_prefix_form() {
        let a = Symbol::intern("a");
        for (src, expected) in [
            ("[] a", Type::Con(Con::List, vec![VAR_T(a)])),
            (
                "[] ([] a)",
                Type::Con(Con::List, vec![Type::Con(Con::List, vec![VAR_T(a)])]),
            ),
            (
                "[] ((,,) a)",
                Type::Con(Con::List, vec![Type::Con(Con::Tuple(2), vec![VAR_T(a)])]),
            ),
        ] {
            Parser::from_str(src)
                .ty_node()
                .map(|ty| {
                    ty.map_fst(&mut Func::Fresh(Spanned::take_item))
                        .map_snd(&mut Func::Fresh(Spanned::take_item))
                })
                .map(|result| assert_eq!(result, expected))
                .unwrap();
        }
    }

    #[test]
    fn test_type_app() {
        let src = "Foo x y z -> Bar (z, y) x";
        let result = Parser::from_str(src)
            .ty_node()
            .map(|ty| {
                ty.map_fst(&mut Func::Fresh(Spanned::take_item))
                    .map_snd(&mut Func::Fresh(Spanned::take_item))
            })
            .unwrap();
        let [foo_ty, x, y, z, bar_ty] = Symbol::intern_many(["Foo", "x", "y", "z", "Bar"]);
        assert_eq!(
            result,
            Type::Fun(
                Box::new(Type::Con(
                    Con::Named(UPPER(foo_ty)),
                    vec![VAR_T(x), VAR_T(y), VAR_T(z)],
                )),
                Box::new(Type::Con(
                    Con::Named(UPPER(bar_ty)),
                    vec![Type::Tup(vec![VAR_T(z), VAR_T(y),]), VAR_T(x)]
                ))
            )
        )
    }

    #[test]
    fn test_parse_arrow_type() {
        let src = "a -> b -> c -> d";
        let result = Parser::from_str(src)
            .ty_node()
            .map(|ty| {
                ty.map_fst(&mut Func::Fresh(Spanned::take_item))
                    .map_snd(&mut Func::Fresh(Spanned::take_item))
            })
            .unwrap();
        println!("{}", &result);
        let [a, b, c, d] = Symbol::intern_many(["a", "b", "c", "d"]);
        let expected = Type::Fun(
            Box::new(VAR_T(a)),
            Box::new(Type::Fun(
                Box::new(VAR_T(b)),
                Box::new(Type::Fun(Box::new(VAR_T(c)), Box::new(VAR_T(d)))),
            )),
        );
        assert_eq!(result, expected)
    }

    #[test]
    fn test_parse_predicate_syntax_sugar() {
        let one = ":: |A a, A b, A c| (a, b, c)";
        let two = ":: |A {a, b, c}| (a, b, c)";
        // testing without regards to span since these two syntactic
        // forms are different but their resulting data (span-aside)
        // should be the same
        Spanless(Parser::from_str(one).ty_signature().unwrap())
            .assert_eq(Parser::from_str(two).ty_signature().unwrap())
    }

    #[test]
    fn test_parse_type_signature() {
        let src = r#":: forall a b. |A a, B b| m a -> (a -> m b) -> m b"#;
        let sig = Parser::from_str(src)
            .ty_signature()
            .map(|ty| {
                ty.map_fst(&mut Func::Fresh(Spanned::take_item))
                    .map_snd(&mut Func::Fresh(Spanned::take_item))
            })
            .unwrap();
        let [a, b, m] = Symbol::intern_many_with(["a", "b", "m"], Ident::Lower);
        let [class_a, class_b] = Symbol::intern_many_with(["A", "B"], UPPER);
        let expected = Signature::Explicit(Annotation {
            quant: Quantified(vec![Var(a, a), Var(b, b)]),
            qual: Qualified {
                pred: vec![
                    Predicate {
                        class: class_a,
                        head: Parameter(a, vec![]),
                    },
                    Predicate {
                        class: class_b,
                        head: Parameter(b, vec![]),
                    },
                ],
                tipo: Type::Fun(
                    Box::new(Type::Con(Con::Free(m), vec![Type::Var(a)])),
                    Box::new(Type::Fun(
                        Box::new(Type::Fun(
                            Box::new(Type::Var(a)),
                            Box::new(Type::Con(Con::Free(m), vec![Type::Var(b)])),
                        )),
                        Box::new(Type::Con(Con::Free(m), vec![Type::Var(b)])),
                    )),
                ),
            },
        });
        assert_eq!(expected, sig)
    }
}
