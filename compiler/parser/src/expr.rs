use std::iter;

use wy_lexer::token::{LexKind, Not};
use wy_lexer::*;
use wy_name::ident::Ident;
use wy_span::WithLoc;
use wy_syntax::expr::{RawExpression, Section};
use wy_syntax::pattern::RawPattern;
use wy_syntax::record::{Field, Record};
use wy_syntax::stmt::{RawAlternative, RawBinding, RawMatch, RawStatement};
use wy_syntax::tipo::Signature;

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
    pub fn expression(&mut self) -> Parsed<RawExpression> {
        self.maybe_binary(&mut Self::subexpression)
    }

    /// A subexpression is synonymous to an application not only because a
    /// single terminal may be interpreted as a trivial application, but also
    /// because applications have higher precedence than infix operators do.
    fn subexpression(&mut self) -> Parsed<RawExpression> {
        self.maybe_apply(Self::atom)
    }

    fn maybe_apply<F>(&mut self, mut f: F) -> Parsed<RawExpression>
    where
        F: FnMut(&mut Self) -> Parsed<RawExpression>,
    {
        let head = f(self)?;
        Ok(self
            .many_while_on(Lexeme::begins_expr, f)?
            .into_iter()
            .fold(head, RawExpression::mk_app))
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
    fn maybe_binary<F>(&mut self, f: &mut F) -> Parsed<RawExpression>
    where
        F: FnMut(&mut Self) -> Parsed<RawExpression>,
    {
        let mut left = f(self)?;
        while self.peek_on(Lexeme::is_infix) {
            let infix = self.expect_infix()?;
            left = RawExpression::Infix {
                left: Box::new(left),
                infix,
                right: self.maybe_binary(f).map(Box::new)?,
            };
        }

        if self.bump_on(Lexeme::Colon2) {
            self.ty_node()
                .map(|tipo| RawExpression::Cast(Box::new(left), tipo))
        } else {
            Ok(left)
        }
    }

    fn negation(&mut self) -> Parsed<RawExpression> {
        if self.bump_on(Lexeme::is_minus_sign) {
            self.negation().map(Box::new).map(RawExpression::Neg)
        } else {
            self.atom()
        }
    }

    fn atom(&mut self) -> Parsed<RawExpression> {
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
            _ => self
                .custom_error("does not correspond to a lexeme that begins an expression")
                .err(),
        }
    }

    fn literal(&mut self) -> Parsed<RawExpression> {
        self.expect_literal().map(RawExpression::Lit)
    }

    fn identifier(&mut self) -> Parsed<RawExpression> {
        let ident = match self.peek() {
            lexpat!(~[var]) => self.expect_lower(),
            lexpat!(~[Var]) => self.expect_upper(),
            _ => self.expected(LexKind::Identifier).err(),
        }?;
        match self.peek() {
            lexpat!(~[.]) => {
                let tail = self.id_path_tail()?;
                Ok(RawExpression::Path(ident, tail))
            }
            lexpat!(~[curlyL]) => Ok(RawExpression::Dict(Record::Data(ident, self.curly_expr()?))),
            _ => Ok(RawExpression::Ident(ident)),
        }
    }

    fn id_path_tail(&mut self) -> Parsed<Vec<Ident>> {
        self.many_while(
            |p| p.bump_on(Lexeme::Dot) && p.peek_on(Lexeme::is_ident),
            |p| match p.peek() {
                Some(t) if t.is_lower() => p.expect_lower(),
                Some(t) if t.is_upper() => p.expect_upper(),
                Some(t) if t.is_infix() => p.expect_infix(),
                _ => p.expected(LexKind::Identifier).err(),
            },
        )
    }

    fn comma_section(&mut self) -> Parsed<RawExpression> {
        use Lexeme::{Comma, ParenR};
        let mut commas = 0;
        while self.bump_on(Comma) {
            commas += 1;
        }
        let prefix = Ident::mk_tuple_commas(commas);

        Ok(if self.bump_on(ParenR) {
            RawExpression::Ident(prefix)
        } else {
            let section = self
                .expression()
                .map(Section::with_prefix(prefix))?
                .into_expression();
            self.eat(ParenR)?;
            section
        })
    }

    fn maybe_prefix_section(&mut self) -> Parsed<RawExpression> {
        let prefix = self.expect_infix()?;
        if !self.peek_on(Lexeme::ParenR) {
            let right = self.subexpression().map(Box::new)?;
            self.eat(Lexeme::ParenR)?;
            return Ok(RawExpression::Section(Section::Prefix { prefix, right }));
        }
        self.eat(Lexeme::ParenR)?;
        Ok(RawExpression::mk_group(RawExpression::Ident(prefix)))
    }

    fn suffix_section(&mut self, left: RawExpression) -> Parsed<RawExpression> {
        let suffix = self.expect_infix()?;
        self.eat(Lexeme::ParenR)?;
        return Ok(RawExpression::Section(Section::Suffix {
            suffix,
            left: Box::new(left),
        }));
    }

    fn paren_expr(&mut self) -> Parsed<RawExpression> {
        use Lexeme::{Comma, ParenL, ParenR};
        self.eat(ParenL)?;
        if self.peek_on(ParenR) {
            self.bump();
            return Ok(RawExpression::UNIT);
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
                .map(RawExpression::Tuple);
        }

        while !self.peek_on(ParenR) {
            first = RawExpression::mk_app(first, self.subexpression()?)
        }

        self.eat(ParenR)?;
        // only represent as grouped if containing an infix expression to
        // preserve explicit groupings during fixity resolution and retraversal
        if let RawExpression::Infix { .. } = &first {
            Ok(RawExpression::Group(Box::new(first)))
        } else {
            Ok(first)
        }
    }

    fn brack_expr(&mut self) -> Parsed<RawExpression> {
        use Lexeme::{BrackL, BrackR, Comma, Dot2};
        self.eat(BrackL)?;
        if self.bump_on(BrackR) {
            return Ok(RawExpression::NULL);
        }

        let first = self.expression()?;

        if self.bump_on(Dot2) {
            return Ok(RawExpression::Range(
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
                Ok(RawExpression::Array(vec![first]))
            }
            lexpat!(~[|]) => self.list_comprehension(first),

            lexpat!(~[,]) => self
                .delimited([Comma, Comma, BrackR], Self::expression)
                .map(|xs| std::iter::once(first).chain(xs).collect::<Vec<_>>())
                .map(RawExpression::Array),

            _ => self.unbalanced_brack().err(),
        }
    }

    fn curly_expr(&mut self) -> Parsed<Vec<Field<Ident, RawExpression>>> {
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
    fn list_comprehension(&mut self, head: RawExpression) -> Parsed<RawExpression> {
        use Lexeme::{BrackR, Comma, Pipe};
        self.eat(Pipe)?;

        let mut stmts = vec![];
        loop {
            if self.bump_on(BrackR) {
                break Ok(RawExpression::List(Box::new(head), stmts));
            }

            stmts.push(self.statement()?);
            self.ignore(Comma);
            if self.is_done() {
                break self.unbalanced_brack().err();
            }
        }
    }

    fn lambda(&mut self) -> Parsed<RawExpression> {
        use Lexeme::{ArrowR, Lambda};
        self.eat(Lambda)?;
        let pats = self.many_while_on(Lexeme::begins_pat, Self::pattern)?;
        self.eat(ArrowR)?;
        self.expression().map(|expr| {
            pats.into_iter()
                .rev()
                .fold(expr, |body, arg| RawExpression::Lambda(arg, Box::new(body)))
        })
    }

    pub(crate) fn binder_name(&mut self) -> Parsed<Ident> {
        use Lexeme::{ParenL, ParenR};
        if self.bump_on(ParenL) {
            let infix = self.expect_infix()?;
            self.eat(ParenR)?;
            Ok(infix)
        } else if lexpat!(self on [var]) {
            self.expect_lower()
        } else {
            self.invalid_fn_ident().err()
        }
    }

    fn binding_lhs(&mut self) -> Parsed<(Vec<RawPattern>, Option<RawExpression>)> {
        use Keyword::If;
        use Lexeme::Pipe;
        self.ignore(Pipe);
        let args = self.many_while_on(Lexeme::begins_pat, Self::pattern)?;
        if lexpat!(self on [|]|[;]|[=]) {
            return Ok((args, None));
        } else if self.bump_on(If) {
            Ok((args, Some(self.expression()?)))
        } else {
            self.invalid_pattern().err()
        }
    }

    fn binding_rhs(&mut self) -> Parsed<(RawExpression, Vec<RawBinding>)> {
        let body = self.expression()?;
        let wher = self.where_clause()?;
        Ok((body, wher))
    }

    fn caf_binding(&mut self, name: Ident, tipo: Option<Signature>) -> Parsed<RawBinding> {
        self.binding_rhs().map(|(body, wher)| RawBinding {
            name,
            tipo,
            arms: vec![RawMatch::caf(body, wher)],
        })
    }

    pub(crate) fn binding(&mut self) -> Parsed<RawBinding> {
        let name = self.binder_name()?;

        match self.peek() {
            Some(t) if t.begins_pat() || t.is_pipe() => Ok(RawBinding {
                name,
                tipo: None,
                arms: self.match_arms()?,
            }),
            lexpat!(~[::]) => {
                self.bump();
                let tipo = self.total_signature().map(Some)?;
                self.ignore(Lexeme::Comma);
                if self.bump_on([Lexeme::Equal, Lexeme::FatArrow]) {
                    self.caf_binding(name, tipo)
                } else {
                    self.match_arms()
                        .map(|arms| RawBinding { name, arms, tipo })
                }
            }
            lexpat!(~[=>]) => {
                self.bump();
                self.caf_binding(name, None)
            }
            lexpat!(~[=]) => {
                self.bump();
                let (body, wher) = self.binding_rhs()?;
                let arms = iter::once(RawMatch::caf(body, wher))
                    .chain(self.match_arms()?)
                    .collect();
                Ok(RawBinding {
                    name,
                    tipo: None,
                    arms,
                })
            }
            _ => self.custom_error("after binder name").err(),
        }
    }

    fn match_arms(&mut self) -> Parsed<Vec<RawMatch>> {
        use Lexeme::Pipe;
        self.many_while(
            |this| {
                this.ignore(Pipe);
                this.peek_on(Lexeme::begins_pat)
            },
            Self::match_arm,
        )
    }

    pub(crate) fn match_arm(&mut self) -> Parsed<RawMatch> {
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

        Ok(RawMatch {
            args,
            pred,
            body,
            wher,
        })
    }

    fn where_clause(&mut self) -> Parsed<Vec<RawBinding>> {
        use Keyword::Where;
        use Lexeme::Comma;
        let mut binds = vec![];
        if self.bump_on(Where) {
            binds.push(self.binding()?);
            binds.extend(self.many_while(|p| p.bump_on(Comma), Self::binding)?);
        };
        Ok(binds)
    }

    fn let_expr(&mut self) -> Parsed<RawExpression> {
        use Keyword::{In, Let};
        use Lexeme::{Comma, Kw};
        Ok(RawExpression::Let(
            self.delimited([Kw(Let), Comma, Kw(In)], Self::binding)?,
            Box::new(self.expression()?),
        ))
    }

    fn case_expr(&mut self) -> Parsed<RawExpression> {
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

        Ok(RawExpression::Case(Box::new(scrut), alts))
    }

    fn case_alt(&mut self) -> Parsed<RawAlternative> {
        Ok(RawAlternative {
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

    fn cond_expr(&mut self) -> Parsed<RawExpression> {
        self.eat(Keyword::If)?;
        let cond = self.expression()?;
        self.eat(Keyword::Then)?;
        let pass = self.expression()?;
        self.eat(Keyword::Else)?;
        let fail = self.expression()?;

        Ok(RawExpression::Cond(Box::new([cond, pass, fail])))
    }

    pub(crate) fn do_expr(&mut self) -> Parsed<RawExpression> {
        self.eat(Keyword::Do)?;
        self.eat(Lexeme::CurlyL)?;

        let mut statements = self.many_while_on(Not(Lexeme::is_curly_r), |p| {
            p.trailing(Lexeme::Semi, Self::statement)
        })?;

        self.eat(Lexeme::CurlyR)?;

        let msg = "do expression must end in an expression";
        statements
            .pop()
            .ok_or_else(|| self.custom_error(msg))
            .and_then(|s| {
                if let RawStatement::Predicate(g) = s {
                    Ok(Box::new(g))
                } else {
                    Err(self.custom_error(msg))
                }
            })
            .map(|tail| RawExpression::Do(statements, tail))
    }

    fn statement(&mut self) -> Parsed<RawStatement> {
        fn bump_comma(parser: &mut Parser) -> bool {
            parser.bump_on(Lexeme::Comma)
        }
        match self.peek() {
            lexpat!(~[do]) => self.do_expr().map(RawStatement::Predicate),
            lexpat!(~[let]) => {
                self.eat(Keyword::Let)?;
                let mut bindings = vec![self.binding()?];
                self.many_while(bump_comma, Self::binding)
                    .map(|binds| bindings.extend(binds))?;
                if self.bump_on(Keyword::In) {
                    Ok(RawStatement::Predicate(RawExpression::Let(
                        bindings,
                        Box::new(self.expression()?),
                    )))
                } else {
                    Ok(RawStatement::JustLet(bindings))
                }
            }
            lexpat!(~[var]) => {
                let lower = self.expect_ident()?;
                if self.bump_on(Lexeme::ArrowL) {
                    self.expression()
                        .map(|ex| RawStatement::Generator(RawPattern::Var(lower), ex))
                } else {
                    Ok(RawStatement::Predicate(
                        self.many_while_on(Lexeme::begins_expr, Self::expression)?
                            .into_iter()
                            .fold(RawExpression::Ident(lower), RawExpression::mk_app),
                    ))
                }
            }
            lexpat!(~[Var]) => {
                let pat = self.pattern()?;
                self.eat(Lexeme::ArrowL)?;
                Ok(RawStatement::Generator(pat, self.expression()?))
            }
            lexpat!(~[_]) => {
                self.bump();
                self.eat(Lexeme::ArrowL)?;
                let expr = self.expression()?;
                Ok(RawStatement::Generator(RawPattern::Wild, expr))
            }
            Some(t) if t.begins_pat() => {
                let lexer = self.lexer.clone();
                let queue = self.queue.clone();
                let pat = self.pattern()?;
                if self.bump_on(Lexeme::ArrowL) {
                    Ok(RawStatement::Generator(pat, self.expression()?))
                } else {
                    self.lexer = lexer;
                    self.queue = queue;
                    Ok(RawStatement::Predicate(self.expression()?))
                }
            }
            Some(t) if t.begins_expr() => self.expression().map(RawStatement::Predicate),
            _ => Err(self.custom_error("is not supported in `do` expressions")),
        }
    }
}

#[cfg(test)]
mod test {
    use wy_syntax::{expr::Expression, pattern::Pattern, stmt::Alternative};

    use super::*;

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
}
