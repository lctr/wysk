use wy_common::Deque;
use wy_lexer::lexpat;
use wy_lexer::{Lexeme, Token};
use wy_name::ident::Ident;
use wy_syntax::pattern::RawPattern;
use wy_syntax::record::{Field, Record};

use crate::error::*;
use crate::stream::*;

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

    pub(crate) fn maybe_at_pattern(&mut self) -> Parsed<RawPattern> {
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

#[cfg(test)]
mod test {
    use wy_lexer::Literal;
    use wy_syntax::pattern::Pattern;

    use super::*;

    #[test]
    fn test_pattern() {
        let int = |n| Pattern::Lit(Literal::Int(n));
        let [a, b, c, d] = wy_intern::intern_many(["a", "b", "c", "d"]);
        let id = |s| Pattern::Var(Ident::Lower(s));
        let lnk = |px, py| Pattern::Lnk(Box::new(px), Box::new(py));
        let pairs = [
            ("(a, b)", Pattern::Tup(vec![id(a), id(b)])),
            ("(a:b:(c:d))", lnk(id(a), lnk(id(b), lnk(id(c), id(d))))),
            (
                "a @ [1, 2, 3]",
                Pattern::At(
                    Ident::Lower(a),
                    Box::new(Pattern::Vec(vec![int(1), int(2), int(3)])),
                ),
            ),
            (
                "(a:b:[c, d])",
                lnk(id(a), lnk(id(b), Pattern::Vec(vec![id(c), id(d)]))),
            ),
            ("(a:[])", lnk(id(a), Pattern::Vec(vec![]))),
        ];

        for (s, x) in pairs {
            assert_eq!(Parser::from_str(s).pattern(), Ok(x))
        }
    }

    #[test]
    fn test_cons_pat() {
        let var = |s| Pattern::Var(Ident::Lower(s));
        let [a, b, c] = wy_intern::intern_many(["a", "b", "c"]);
        let link = Pattern::Lnk(
            Box::new(var(a)),
            Box::new(Pattern::Lnk(Box::new(var(b)), Box::new(var(c)))),
        );
        assert_eq!(Ok(link), Parser::from_str("(a:b:c)").pattern())
    }
}
