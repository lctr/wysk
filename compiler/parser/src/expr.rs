use std::iter;

use wy_lexer::token::{LexKind, Not};
use wy_lexer::*;
use wy_name::ident::Ident;
use wy_span::{Span, Spanned, WithLoc, WithSpan};
use wy_syntax::expr::{Expression, Range, Section};
use wy_syntax::pattern::RawPattern;
use wy_syntax::record::{Field, Record};
use wy_syntax::stmt::{Binding, RawAlternative, RawArm, RawBinding, RawStatement};

use wy_syntax::SpannedIdent;

use crate::error::*;
use crate::stream::*;

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
    ///
    /// This method will parse expression application but NOT infix
    /// ("binary") expressions! In order words, applying this method
    /// to the source text `foo a b + 3` will only parse `foo a b`.
    fn subexpression(&mut self) -> Parsed<Expression> {
        self.maybe_apply(Self::atom)
    }

    fn maybe_apply<F>(&mut self, mut f: F) -> Parsed<Expression>
    where
        F: FnMut(&mut Self) -> Parsed<Expression>,
    {
        let head = f(self)?;
        // TODO: maybe simplify this to checking that `head` isn't a
        // literal, list, tuple, range, or record
        if head.maybe_callable() {
            Ok(self
                .many_while_on(Lexeme::begins_expr, f)?
                .into_iter()
                .fold(head, Expression::mk_app))
        } else {
            Ok(head)
        }
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
            Some(t) if t.is_minus_sign() => self.negation(),
            lexpat!(~[parenL]) => self.paren_expr(),
            lexpat!(~[brackL]) => self.brack_expr(),
            lexpat!(~[let]) => self.let_expr(),
            lexpat!(~[case]) => self.case_expr(),
            lexpat!(~[if]) => self.cond_expr(),
            lexpat!(~[do]) => self.do_expr(),
            lexpat!(~[lam]) => self.lambda(),
            lexpat!(~[lit]) => self.literal(),
            lexpat!(~[var][Var]) => self.identifier(),
            Some(t) => {
                let t = *t;
                self.custom_error(
                    t,
                    " does not correspond to a lexeme that begins an expression",
                )
                .err()
            }
            None => self.unexpected_eof().err(),
        }
    }

    #[inline]
    fn literal(&mut self) -> Parsed<Expression> {
        self.expect_literal().map(Expression::Lit)
    }

    fn identifier(&mut self) -> Parsed<Expression> {
        let ident = match self.peek().copied().ok_or_else(|| self.unexpected_eof())? {
            Token {
                lexeme: Lexeme::Lower(s),
                span,
            } => {
                self.bump();
                Ok(Spanned(Ident::Lower(s), span))
            }
            Token {
                lexeme: Lexeme::Upper(s),
                span,
            } => {
                self.bump();
                Ok(Spanned(Ident::Upper(s), span))
            }
            t => self.expected(LexKind::Identifier, t).err(),
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

    fn id_path_tail(&mut self) -> Parsed<Vec<SpannedIdent>> {
        self.many_while(
            |p| p.bump_or_peek_on(Lexeme::Dot, Lexeme::is_ident),
            Self::expect_ident,
        )
    }

    fn comma_section(&mut self) -> Parsed<Expression> {
        use Lexeme::{Comma, ParenR};
        let mut commas = 0;
        let start = self.get_pos();
        while self.bump_on(Comma) {
            commas += 1;
        }
        let prefix = Spanned(Ident::mk_tuple_commas(commas), Span(start, self.get_pos()));

        Ok(if self.bump_on(ParenR) {
            Expression::Ident(prefix)
        } else {
            let section = self
                .expression()
                .map(Section::with_prefix(prefix))?
                .into_expression();
            self.eat(ParenR)?;
            section
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
        Ok(Expression::mk_group(Expression::Ident(prefix)))
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
        match self.peek() {
            // [a]
            lexpat!(~[brackR]) => {
                self.bump();
                Ok(Expression::Array(vec![first]))
            }
            // [a | stmts]
            lexpat!(~[|]) => self.list_comprehension(first),
            // [a..] or [a..b]
            lexpat!(~[..]) => {
                self.bump();
                let range = if self.bump_on(BrackR) {
                    Range::From(first)
                } else {
                    self.expression()
                        .map(|second| Range::FromTo([first, second]))
                        .map(|range| self.bumped(range))?
                };
                Ok(Expression::Range(Box::new(range)))
            }
            lexpat!(~[,]) => {
                self.bump();
                let second = self.expression()?;
                if self.peek_on(Comma) {
                    // [a, b, <rest>]
                    self.delimited([Comma, Comma, BrackR], Self::expression)
                        .map(|xs| [first, second].into_iter().chain(xs).collect::<Vec<_>>())
                        .map(Expression::Array)
                } else if self.bump_on(Dot2) {
                    // [a, b..c]
                    let third = self.expression()?;
                    self.eat(BrackR)?;
                    Ok(Expression::Range(Box::new(Range::FromThenTo([
                        first, second, third,
                    ]))))
                } else {
                    // [a, b]
                    self.eat(BrackR)?;
                    Ok(Expression::Array(vec![first, second]))
                }
            }

            Some(t) => {
                let t = *t;
                self.unbalanced_brack(t).err()
            }
            None => self.unexpected_eof().err(),
        }
    }

    fn curly_expr(&mut self) -> Parsed<Vec<Field<SpannedIdent, Expression>>> {
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

            stmts.push(self.statement()?);
            self.ignore(Comma);
            if self.is_done() {
                break self.unbalanced_brack(self.lexer.eof_token()).err();
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

    pub(crate) fn binder_name(&mut self) -> Parsed<SpannedIdent> {
        use Lexeme::ParenR;
        match self.peek() {
            lexpat![~[parenL]] => {
                self.bump();
                let infix = self.expect_infix()?;
                self.eat(ParenR)?;
                Ok(infix)
            }
            lexpat![~[var]] => self.expect_lower(),
            Some(t) => {
                let t = *t;
                self.invalid_fn_ident(t).err()
            }
            None => self.unexpected_eof().err(),
        }
    }

    pub(crate) fn binding_lhs(&mut self) -> Parsed<(Vec<RawPattern>, Option<Expression>)> {
        use Keyword::If;
        use Lexeme::{Equal, Kw, Pipe, Semi};
        self.ignore(Pipe);
        let args = self.many_while_on(Lexeme::begins_pat, Self::pattern)?;
        match self.peek().copied().ok_or_else(|| self.unexpected_eof())? {
            Token { lexeme: Pipe | Semi | Equal, .. } => {
                Ok((args, None))
            }
            Token { lexeme: Kw(If), ..} => {
                self.bump();
                Ok((args, Some(self.expression()?)))
            }
            t => {
                self.custom_error(t, " does not terminate the left-hand side of a binding; expected `|`, `;`, `=`, or `if`").err()
            }
        }
    }

    fn binding_rhs(&mut self) -> Parsed<(Expression, Vec<RawBinding>)> {
        let body = self.expression()?;
        let wher = self.where_clause()?;
        Ok((body, wher))
    }

    pub(crate) fn binding(&mut self) -> Parsed<RawBinding> {
        let name = self.binder_name()?;
        let tsig = self.ty_signature()?;

        match self.peek() {
            Some(t) if t.begins_pat() || t.is_pipe() => Ok(Binding {
                name,
                tsig,
                arms: self.match_arms()?,
            }),
            lexpat!(~[=]) => {
                self.bump();
                let (body, wher) = self.binding_rhs()?;
                let arms = iter::once(RawArm::caf(body, wher))
                    .chain(self.match_arms()?)
                    .collect();
                Ok(RawBinding { name, tsig, arms })
            }
            Some(t) => {
                let t = *t;
                self.custom_error(t, " after binder name").err()
            }
            None => self.unexpected_eof().err(),
        }
    }

    pub(crate) fn match_arms(&mut self) -> Parsed<Vec<RawArm>> {
        use Lexeme::Pipe;
        self.many_while(
            |this| {
                this.ignore(Pipe);
                this.peek_on(Lexeme::begins_pat)
            },
            Self::match_arm,
        )
    }

    pub(crate) fn match_arm(&mut self) -> Parsed<RawArm> {
        use Lexeme::Equal;
        let (args, cond) = self.binding_lhs()?;
        self.eat(Equal)?;
        let (body, wher) = self.binding_rhs()?;

        Ok(RawArm {
            args,
            cond,
            body,
            wher,
        })
    }

    pub(crate) fn where_clause(&mut self) -> Parsed<Vec<RawBinding>> {
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
                |p| (p.get_col() == col) && p.bump_or_peek_on(Pipe, Lexeme::begins_pat),
                Self::case_alt,
            )?
        };

        Ok(Expression::Case(Box::new(scrut), alts))
    }

    fn case_alt(&mut self) -> Parsed<RawAlternative> {
        Ok(RawAlternative {
            pat: self.maybe_at_pattern()?,
            cond: if self.bump_on(Keyword::If) {
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

    pub(crate) fn do_expr(&mut self) -> Parsed<Expression> {
        self.eat(Keyword::Do)?;
        self.eat(Lexeme::CurlyL)?;

        let mut tok = self.current_token()?;
        let mut statements = self.many_while_on(Not(Lexeme::is_curly_r), |p| {
            tok = p.current_token()?;
            p.trailing(Lexeme::Semi, Self::statement)
        })?;

        self.eat(Lexeme::CurlyR)?;

        let msg = "do expression must end in an expression";
        statements
            .pop()
            .ok_or_else(|| self.custom_error(tok, msg))
            .and_then(|s| {
                if let RawStatement::Predicate(g) = s {
                    Ok(Box::new(g))
                } else {
                    Err(self.custom_error(tok, msg))
                }
            })
            .map(|tail| Expression::Do(statements, tail))
    }
}

#[cfg(test)]
mod test {
    use wy_common::functor::{Func, MapFst, MapSnd};
    use wy_failure::diff::diff_assert_eq;
    use wy_intern::Symbol;
    use wy_syntax::{
        ast::spanless_eq::de_span2,
        expr::Expression,
        pattern::Pattern,
        stmt::{Alternative, Arm, Statement},
        tipo::Signature,
    };

    use super::*;

    fn infixed(
        left: Expression<Ident, Ident>,
        infix: wy_intern::Symbol,
        right: Expression<Ident, Ident>,
    ) -> Expression<Ident, Ident> {
        Expression::Infix {
            infix: Ident::Infix(infix),
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    fn tuplex<const N: usize>(subexps: [Expression<Ident, Ident>; N]) -> Expression<Ident, Ident> {
        Expression::Tuple(subexps.to_vec())
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
            Symbol::intern_many(["A", "B", "c", "d", "h", "f", "x", "y"]);
        let expr = Parser::from_str(src).case_expr().map(|expr| {
            expr.map_fst(&mut Func::New(Spanned::take_item))
                .map_snd(&mut Func::New(Spanned::take_item))
        });
        println!("{:#?}", &expr);
        let expected = Expression::Case(
            Box::new(Expression::App(
                Box::new(Expression::Ident(Ident::Lower(f))),
                Box::new(Expression::Ident(Ident::Lower(x))),
            )),
            vec![
                Alternative {
                    pat: Pattern::Dat(Ident::Upper(a), vec![Pattern::Var(Ident::Lower(c))]),
                    cond: None,
                    body: Expression::Ident(Ident::Lower(c)),
                    wher: vec![],
                },
                Alternative {
                    pat: Pattern::Dat(Ident::Upper(b), vec![Pattern::Var(Ident::Lower(d))]),
                    cond: Some(Expression::App(
                        Box::new(Expression::Ident(Ident::Lower(c))),
                        Box::new(Expression::Ident(Ident::Lower(d))),
                    )),
                    body: Expression::Ident(Ident::Lower(h)),
                    wher: vec![],
                },
                Alternative {
                    pat: Pattern::Var(Ident::Lower(y)),
                    cond: None,
                    body: Expression::Ident(Ident::Lower(y)),
                    wher: vec![],
                },
            ],
        );
        diff_assert_eq!(expr, Ok(expected))
    }

    #[test]
    fn test_infix_exprs() {
        use Expression::Lit;
        let [op1, op2, plus, times, minus, fun] =
            Symbol::intern_many(["<>", "><", "+", "*", "-", "fun"]);
        let int = |n| Lit(Literal::simple_int(n));

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
            diff_assert_eq!(
                Parser::from_str(src)
                    .expression()
                    .map(|expr| expr
                        .map_fst(&mut Func::New(Spanned::take_item))
                        .map_snd(&mut Func::New(Spanned::take_item)))
                    .unwrap(),
                expected
            );
        }
    }

    #[test]
    fn let_expr() {
        let src = r#"
        let foo | 1 = 2 
                | 3 = 4
        , bar | x y = (x, y) where y = x + 2
        in bar (foo 1) (foo 2)
    "#;
        let [foo, bar, x, y] = Symbol::intern_many_with(["foo", "bar", "x", "y"], Ident::Lower);
        let actual = Parser::from_str(src).expression().map(de_span2).unwrap();
        let expected = Expression::Let(
            vec![
                Binding {
                    name: foo,
                    tsig: Signature::Implicit,
                    arms: vec![
                        Arm {
                            args: vec![Pattern::Lit(Literal::simple_int(1))],
                            cond: None,
                            body: Expression::Lit(Literal::simple_int(2)),
                            wher: vec![],
                        },
                        Arm {
                            args: vec![Pattern::Lit(Literal::simple_int(3))],
                            cond: None,
                            body: Expression::Lit(Literal::simple_int(4)),
                            wher: vec![],
                        },
                    ],
                },
                Binding {
                    name: bar,
                    tsig: Signature::Implicit,
                    arms: vec![Arm {
                        args: vec![Pattern::Var(x), Pattern::Var(y)],
                        cond: None,
                        body: Expression::Tuple(vec![Expression::Ident(x), Expression::Ident(y)]),
                        wher: vec![Binding {
                            name: y,
                            tsig: Signature::Implicit,
                            arms: vec![Arm {
                                args: vec![],
                                cond: None,
                                body: Expression::Infix {
                                    left: Box::new(Expression::Ident(x)),
                                    infix: Ident::Infix(Symbol::intern("+")),
                                    right: Box::new(Expression::Lit(Literal::simple_int(2))),
                                },
                                wher: vec![],
                            }],
                        }],
                    }],
                },
            ],
            Box::new(Expression::App(
                Box::new(Expression::App(
                    Box::new(Expression::Ident(bar)),
                    Box::new(Expression::App(
                        Box::new(Expression::Ident(foo)),
                        Box::new(Expression::Lit(Literal::simple_int(1))),
                    )),
                )),
                Box::new(Expression::App(
                    Box::new(Expression::Ident(foo)),
                    Box::new(Expression::Lit(Literal::simple_int(2))),
                )),
            )),
        );
        diff_assert_eq!(actual, expected);
    }

    #[test]
    fn test_lambda_exprs() {
        let [f, x, y, z] = Symbol::intern_many_with(["f", "x", "y", "z"], Ident::Lower);
        let pairs = [
            (
                r#"\x -> f x"#,
                Expression::Lambda(
                    Pattern::Var(x),
                    Box::new(Expression::App(
                        Box::new(Expression::Ident(f)),
                        Box::new(Expression::Ident(x)),
                    )),
                ),
            ),
            (
                r#"\(x, y) -> (f x, f y, \z -> f z)"#,
                Expression::Lambda(
                    Pattern::Tup(vec![Pattern::Var(x), Pattern::Var(y)]),
                    Box::new(Expression::Tuple(vec![
                        Expression::App(
                            Box::new(Expression::Ident(f)),
                            Box::new(Expression::Ident(x)),
                        ),
                        Expression::App(
                            Box::new(Expression::Ident(f)),
                            Box::new(Expression::Ident(y)),
                        ),
                        Expression::Lambda(
                            Pattern::Var(z),
                            Box::new(Expression::App(
                                Box::new(Expression::Ident(f)),
                                Box::new(Expression::Ident(z)),
                            )),
                        ),
                    ])),
                ),
            ),
            (
                r#"\x y z -> f x y z"#,
                Expression::Lambda(
                    Pattern::Var(x),
                    Box::new(Expression::Lambda(
                        Pattern::Var(y),
                        Box::new(Expression::Lambda(
                            Pattern::Var(z),
                            Box::new(Expression::App(
                                Box::new(Expression::App(
                                    Box::new(Expression::App(
                                        Box::new(Expression::Ident(f)),
                                        Box::new(Expression::Ident(x)),
                                    )),
                                    Box::new(Expression::Ident(y)),
                                )),
                                Box::new(Expression::Ident(z)),
                            )),
                        )),
                    )),
                ),
            ),
        ];
        for (src, expected) in pairs {
            diff_assert_eq!(
                Parser::from_str(src).expression().map(de_span2).unwrap(),
                expected
            );
        }
    }

    #[test]
    fn test_list_comprehensions() {
        let [f, x, y, n] = Symbol::intern_many_with(["f", "x", "y", "n"], Ident::Lower);
        let pairs = [
            (
                "[ f x | x <- [0..n] ]",
                Expression::List(
                    Box::new(Expression::App(
                        Box::new(Expression::Ident(f)),
                        Box::new(Expression::Ident(x)),
                    )),
                    vec![Statement::Generator(
                        Pattern::Var(x),
                        Expression::Range(Box::new(Range::FromTo([
                            Expression::Lit(Literal::DIGIT_ZERO),
                            Expression::Ident(n),
                        ]))),
                    )],
                ),
            ),
            (
                "[f x | x <- [0, 5..10], y <- [0 .. n]]",
                Expression::List(
                    Box::new(Expression::App(
                        Box::new(Expression::Ident(f)),
                        Box::new(Expression::Ident(x)),
                    )),
                    vec![
                        Statement::Generator(
                            Pattern::Var(x),
                            Expression::Range(Box::new(Range::FromThenTo([
                                Expression::Lit(Literal::DIGIT_ZERO),
                                Expression::Lit(Literal::simple_int(5)),
                                Expression::Lit(Literal::simple_int(10)),
                            ]))),
                        ),
                        Statement::Generator(
                            Pattern::Var(y),
                            Expression::Range(Box::new(Range::FromTo([
                                Expression::Lit(Literal::DIGIT_ZERO),
                                Expression::Ident(n),
                            ]))),
                        ),
                    ],
                ),
            ),
        ];
        for (src, expected) in pairs {
            let actual = Parser::from_str(src).expression().map(de_span2).unwrap();
            diff_assert_eq!(actual, expected);
        }
    }

    #[test]
    fn test_section_expr() {
        use wy_syntax::expr::Section::*;
        use Expression as E;
        let src = "map (+5) [1, 2, 3]";
        let [map, plus] = Symbol::intern_many(["map", "+"]);
        let map = Ident::Lower(map);
        let plus = Ident::Infix(plus);
        let expected: Expression<Ident, Ident> = E::App(
            Box::new(E::App(
                Box::new(E::Ident(map)),
                Box::new(E::Section(Prefix {
                    prefix: plus,
                    right: Box::new(E::Lit(Literal::simple_int(5))),
                })),
            )),
            Box::new(E::Array(vec![
                E::Lit(Literal::simple_int(1)),
                E::Lit(Literal::simple_int(2)),
                E::Lit(Literal::simple_int(3)),
            ])),
        );

        diff_assert_eq!(
            Parser::from_str(src).expression().map(de_span2),
            Ok(expected)
        )
    }

    #[test]
    fn test_expr_assoc() {
        for (x, y) in [("f x y", "(f x) y"), ("return x == y", "(return x) == y")] {
            diff_assert_eq!(
                Parser::from_str(x).expression().map(de_span2),
                Parser::from_str(y).expression().map(de_span2)
            );
        }
    }

    fn show<X, E>(res: Result<X, E>)
    where
        X: std::fmt::Debug,
        E: std::fmt::Display,
    {
        match &res {
            Ok(x) => println!("{x:#?}"),
            Err(e) => eprintln!("{e}"),
        };
    }

    #[test]
    fn experiment() {
        let src = "let foo | (Some a) b if a == 1 = (a, b) | a b if True = Blah in Blah";
        show(Parser::from_str(src).expression())
    }
}
