use wy_lexer::token::Lexlike;

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

    fn ignore<T>(&mut self, item: T)
    where
        T: Lexlike<Self::Peeked, Self::Lexeme>,
    {
        self.bump_on(item);
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
