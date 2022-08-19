use std::path::Path;

use wy_common::Deque;
use wy_lexer::{token::Lexlike, Lexeme, Lexer, Token};
use wy_name::ident::Ident;

use wy_span::{ranges::CoordSpan, BytePos, Coord, Dummy, Span, WithLoc, WithSpan};
use wy_syntax::fixity::FixityTable;

use crate::error::{Expects, ParseError, Parsed, ParserErrors, Report, SrcLoc, SrcPath};

#[derive(Debug)]
pub struct Parser<'t> {
    pub(crate) lexer: Lexer<'t>,
    pub(crate) queue: Deque<Token>,
    pub fixities: FixityTable,
    pub path: SrcPath,
    pub errors: ParserErrors,
}

impl<'t> WithSpan for Parser<'t> {
    fn get_pos(&self) -> BytePos {
        if let Some(t) = self.queue.front() {
            t.span.start()
        } else {
            self.lexer.get_pos()
        }
    }
}

impl<'t> WithLoc for Parser<'t> {
    fn get_coord(&self) -> Coord {
        self.lexer.get_coord()
    }
}

impl<'t> Report for Parser<'t> {
    fn next_token(&mut self) -> Token {
        self.peek_ahead()
            .copied()
            .unwrap_or_else(|| self.lexer.eof_token())
    }

    fn next_coord_span(&mut self) -> CoordSpan {
        CoordSpan {
            coord: self.get_coord(),
            span: self.next_token().span,
        }
    }

    fn store_error(&mut self, error: ParseError) {
        self.errors.push(error)
    }
}

impl<'t> Parser<'t> {
    pub fn new(src: &'t str, path: impl AsRef<Path>) -> Self {
        Self {
            lexer: Lexer::new(src),
            path: SrcPath::File(path.as_ref().to_path_buf()),
            queue: Deque::new(),
            fixities: FixityTable::new(Ident::Infix),
            errors: ParserErrors::default(),
        }
    }

    pub fn from_str(src: &'t str) -> Self {
        Self {
            lexer: Lexer::new(src),
            path: SrcPath::Direct,
            queue: Deque::new(),
            fixities: FixityTable::new(Ident::Infix),
            errors: ParserErrors::default(),
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

    pub fn then_bump<T>(t: T) -> impl FnOnce(&mut Parser) -> T {
        move |this: &mut Parser| {
            this.bump();
            t
        }
    }

    pub fn srcloc(&mut self) -> SrcLoc {
        let pathstr = self.path.clone();
        let coord = self.lexer.get_coord();
        SrcLoc { pathstr, coord }
    }

    pub fn eat<T>(&mut self, expected: T) -> Parsed<Token>
    where
        T: AsRef<Lexeme>,
    {
        let lexeme: &Lexeme = expected.as_ref();
        match self.peek() {
            None
            | Some(Token {
                lexeme: Lexeme::Eof,
                ..
            }) => Err(self.unexpected_eof()),

            t if t.cmp_lex(lexeme) => Ok(self.bump()),

            Some(_t) => match *lexeme {
                delim if delim.is_right_delim() => self.unbalanced_delim(delim).err(),
                expected => self.expected_token(expected).err(),
            },
        }
    }

    pub fn text(&self) -> String {
        let mut buf = String::new();
        self.lexer.write_to_string(&mut buf);
        buf
    }

    /// Bumps the lexer twice, storing the two tokens returns, and
    /// then returns a reference to the second token bumped.
    pub fn peek_ahead(&mut self) -> Option<&Token> {
        match self.queue.len() {
            0 => {
                self.lookahead::<2>();
            }
            1 => {
                self.lookahead::<1>();
            }
            _ => (),
        };
        self.queue.get(1)
    }

    pub fn lookahead<const N: usize>(&mut self) -> [Token; N] {
        let mut array = [Token {
            lexeme: Lexeme::Eof,
            span: Span::DUMMY,
        }; N];
        for i in 0..N {
            if let Some(tok) = self.lexer.next() {
                array[i] = tok;
                if !tok.is_eof() {
                    self.queue.push_back(tok)
                } else {
                    break;
                }
            }
        }
        array
    }

    /// Consumes an initial lexeme `start` and repeatedly alternates applying
    /// the given closure `f` and consuming the separator lexeme `mid`,
    /// terminating upon encountering (and consuming) the ending lexeme `end`.
    ///
    /// This method is ideal for parsing collections of delimited nodes, as in
    /// tuples and arrays.
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
}

pub trait Streaming {
    type Peeked: Lexlike;
    type Lexeme: Lexlike;
    type Err;

    /// Returns whether the underlying token stream is complete. A token stream
    /// is considered 'done' if the current token is the `EOF` lexeme. Note that
    /// there may be subtle differences between calling the token stream's
    /// `is_done` method and matching the peeked current token with `Eof`, as
    /// the underlying token stream may have non-EOF tokens queued.
    fn is_done(&mut self) -> bool;

    fn peek(&mut self) -> Option<&Self::Peeked>;

    /// Peeks at the current `Peeked` item and calls the `Lexlike::cmp_tok`
    /// method on the provided input, returning whether a match was found.
    #[inline]
    fn peek_on<T>(&mut self, item: T) -> bool
    where
        T: Lexlike<Self::Peeked, Self::Lexeme>,
    {
        match self.peek() {
            Some(t) => item.cmp_tok(t),
            None => false, // item.cmp_lex(&Lexeme::Eof),
        }
    }

    fn eat<T>(&mut self, item: T) -> Parsed<Self::Peeked>
    where
        T: AsRef<Self::Lexeme>;

    /// Advance the underlying stream of tokens. If the stream
    /// is not over, then the *current* token is returned; otherwise the token
    /// corresponding to the `EOF` lexeme is returned.
    ///
    /// Note that this method first checks the internal lexeme queue before
    /// calling the lexer. If the buffer is non-empty, it simply pops the next
    /// element from the front of the qeueue.
    fn bump(&mut self) -> Self::Peeked;

    /// Calls `bump` and ignores its return value, instead returning the given
    /// item `t`.
    #[inline]
    fn bumped<T>(&mut self, t: T) -> T {
        self.bump();
        t
    }

    /// Conditionally advances the token stream based on the given argument
    /// matching -- via the `Lexlike::cmp_tok` method -- the inner token
    /// referenced by the result of calling `Stream::peek`. Returns the same
    /// boolean value used to decide whether to advance or not.
    ///
    ///
    /// This method is useful as a shortcut to the pattern involved in
    /// conditionally advancing the inner stream of tokens as the side effect of
    /// a predicate (as in the following code snippet):
    /// ```rust,ignore
    /// if self.peek_on(...) {
    ///     self.bump();
    ///     /* do something */
    /// } /* do something else */
    /// ```
    #[inline]
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

    /// Shortcut equivalent to calling `bump_on(bump_if) || peek_on(peek_on)`,
    /// but optimized such that only a single call to the underlying token
    /// stream is made.
    #[inline]
    fn bump_or_peek_on(
        &mut self,
        bump_if: impl Lexlike<Self::Peeked, Self::Lexeme>,
        peek_if: impl Lexlike<Self::Peeked, Self::Lexeme>,
    ) -> bool {
        match self.peek() {
            Some(t) if bump_if.cmp_tok(t) => {
                self.bump();
                true
            }
            Some(t) => peek_if.cmp_tok(t),
            _ => false,
        }
    }

    /// Conditionally advances the underlying token stream if the current lexeme
    /// matches the given `item`.
    #[inline]
    fn ignore<T>(&mut self, item: T)
    where
        T: Lexlike<Self::Peeked, Self::Lexeme>,
    {
        self.bump_on(item);
    }

    /// Ignores the lexeme `item` after applying the given closure `f`,
    /// returning the results. This method is non-strict with regards to the
    /// lexeme in that it won't fail if the next lexeme in the stream, after
    /// appplying `f`, doesn't match `item`.
    ///
    /// This method can be used to parse a node optionally followed by a
    /// trailing separator.
    #[inline]
    fn trailing<X>(
        &mut self,
        end: impl Lexlike<Self::Peeked, Self::Lexeme>,
        mut f: impl FnMut(&mut Self) -> Result<X, Self::Err>,
    ) -> Result<X, Self::Err> {
        let it = f(self)?;
        self.ignore(end);
        Ok(it)
    }

    /// Consumes a starting token, applies a closure consumes and ending token,
    /// then returns the result from the applied closure. Returns an error if
    /// neither starting nor ending token could be consumed in order, or if the
    /// closure returns an error.
    #[inline]
    fn wrapped<A: AsRef<Self::Lexeme>, X, B: AsRef<Self::Lexeme>>(
        &mut self,
        (start, end): (A, B),
        mut f: impl FnMut(&mut Self) -> Parsed<X>,
    ) -> Parsed<X> {
        self.eat(start)?;
        let x = f(self)?;
        self.eat(end)?;
        Ok(x)
    }

    /// Given a predicate `pred` and a parser, applies the given parser `parse`
    /// repeatedly as long as the predicate returns `true` and returning the
    /// results in a vector.
    ///
    /// This method will always check the predicate prior to running
    /// the given parser.
    ///
    /// **Note:** the given predicate *must* be coercible to
    /// `fn` pointer, and hence **must not** capture any variables.
    #[inline]
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

    #[inline]
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

    fn eat<T>(&mut self, item: T) -> Parsed<Self::Peeked>
    where
        T: AsRef<Self::Lexeme>,
    {
        Parser::eat(self, item)
    }

    /// Advance the underlying stream of tokens, retuning the unwrapped result
    /// of `Lexer::next`. If `Lexer::next` returns `None`, then the token
    /// corresponding to the `EOF` lexeme is returned.
    ///
    /// Note that this method first checks the internal token queue before
    /// calling the lexer. If the buffer is non-empty, it simply pops the next
    /// element from the front of the qeueue.
    fn bump(&mut self) -> Token {
        Parser::bump(self)
    }

    fn is_done(&mut self) -> bool {
        match self.peek() {
            Some(t) if t.is_eof() => true,
            None => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod test {
    use wy_intern::Symbol;
    use wy_lexer::Literal;

    use super::*;

    #[test]
    fn test_lookahead() {
        let src = "foo bar [1, { bar, baz }]";
        let [foo, bar, _baz] = Symbol::intern_many(["foo", "bar", "baz"]);
        let mut parser = Parser::from_str(src);
        assert_eq!(
            parser.peek().map(|t| t.lexeme),
            Some(Lexeme::Lower(Symbol::intern("foo")))
        );
        assert_eq!(
            parser.lookahead::<3>(),
            [
                Token {
                    lexeme: Lexeme::Lower(foo),
                    span: Span(BytePos::new(0), BytePos::strlen("foo"))
                },
                Token {
                    lexeme: Lexeme::Lower(bar),
                    span: Span(BytePos::strlen("foo "), BytePos::strlen("foo bar"))
                },
                Token {
                    lexeme: Lexeme::BrackL,
                    span: Span(BytePos::strlen("foo bar "), BytePos::strlen("foo bar ["))
                },
            ]
        );
        assert_eq!(
            parser.peek_ahead(),
            Some(&Token {
                lexeme: Lexeme::Lower(bar),
                span: Span(BytePos::strlen("foo "), BytePos::strlen("foo bar"))
            },)
        );
        assert_eq!(
            parser.bump(),
            Token {
                lexeme: Lexeme::Lower(foo),
                span: Span(BytePos::new(0), BytePos::strlen("foo"))
            }
        );
        assert_eq!(
            parser.bump(),
            Token {
                lexeme: Lexeme::Lower(bar),
                span: Span(BytePos::strlen("foo "), BytePos::strlen("foo bar"))
            },
        );
        assert_eq!(
            parser.peek(),
            Some(&Token {
                lexeme: Lexeme::BrackL,
                span: Span(BytePos::strlen("foo bar "), BytePos::strlen("foo bar ["))
            },)
        );
        assert_eq!(
            parser.peek_ahead(),
            Some(&Token {
                lexeme: Lexeme::Lit(Literal::simple_int(1)),
                span: Span(BytePos::strlen("foo bar ["), BytePos::strlen("foo bar [1"))
            })
        )
    }
}
