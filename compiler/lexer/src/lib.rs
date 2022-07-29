use meta::{Associativity, Attr, Digit, Placement, Pragma};
// use stream::Mode;
use wy_intern as intern;
use wy_span as span;

use intern::symbol;

use comment::{Comment, CommentId, LineKind};
use literal::Base;

use span::{BytePos, Span, Spanned, WithSpan};

pub use literal::Literal;
pub use stream::{Lexer, Source};
pub use token::{Keyword, LexError, Lexeme, Token};

pub mod comment;
pub mod literal;
pub mod meta;
pub mod stream;
pub mod token;

#[inline]
fn lex_eof(lexer: &mut Lexer) -> Token {
    lexer.source.spanned(|_| Lexeme::Eof).into()
}

impl From<Spanned<Lexeme>> for Token {
    fn from(Spanned(lexeme, span): Spanned<Lexeme>) -> Self {
        Token { lexeme, span }
    }
}

impl<'t> Lexer<'t> {
    pub fn token(&mut self) -> Token {
        if let Some(t) = self.stack.pop() {
            t
        } else {
            self.source.eat_whitespace();
            if let Some(c) = self.source.peek().copied() {
                self.tokenize(c)
            } else {
                lex_eof(self)
            }
        }
    }

    fn lexed_with(&mut self, lexeme: Lexeme) -> Token {
        self.source
            .spanned(|s| {
                s.next();
                lexeme
            })
            .into()
    }

    fn tokenize(&mut self, c: char) -> Token {
        match c {
            '~' => self.tilde(),
            ';' => self.lexed_with(Lexeme::Semi),
            '\'' => self.character(),
            '"' => self.string(),
            '`' => self.backtick(),
            c if c.is_digit(10) => self.number(c),
            c if is_ident_start(c) => self.identifier(c),
            '(' => self.lexed_with(Lexeme::ParenL),
            ')' => self.lexed_with(Lexeme::ParenR),
            '[' => self.lexed_with(Lexeme::BrackL),
            ']' => self.lexed_with(Lexeme::BrackR),
            '{' => self.lexed_with(Lexeme::CurlyL),
            '}' => self.lexed_with(Lexeme::CurlyR),
            ',' => self.lexed_with(Lexeme::Comma),
            c if is_infix_char(c) => self.infix(),
            _ => self.unknown(),
        }
    }

    fn character(&mut self) -> Token {
        use Lexeme::Lit;
        use Literal::Char;
        let start = self.source.get_pos();
        // skip the first apostrophe
        self.source.next();
        match self.source.peek().copied() {
            Some(c) if c != '\\' => {
                self.source.next();
                let lexeme = if self.source.on_char('\'') {
                    self.source.next();
                    Lit(Char(c))
                } else if c == '_' && self.on_char(char::is_whitespace) {
                    Lexeme::Unlabel
                } else if is_ident_start(c) {
                    let posn = self.source.eat_while(is_ident_char);
                    let symbol = wy_intern::intern_once(&self.source[posn.span()]);
                    Lexeme::Label(symbol)
                } else {
                    Lexeme::Unknown(LexError::UnterminatedChar)
                };
                Token {
                    lexeme,
                    span: self.source.span_from(start),
                }
            }
            Some(c) if c == '\\' => {
                self.source.next();
                let lexeme = if matches!(self.source.peek(), Some(c) if is_escapable(*c)) {
                    self.source.next();
                    if self.source.on_char('\'') {
                        self.source.next();
                        Lit(Char(get_escaped(c)))
                    } else {
                        Lexeme::Unknown(LexError::UnterminatedChar)
                    }
                } else {
                    Lexeme::Unknown(LexError::InvalidEscape)
                };
                Token {
                    lexeme,
                    span: self.span_from(start),
                }
            }
            // unreachable?? since every char is either equal to a given
            // character or not (in this case, the escape, but regardless, c !=
            // d => !(c == d), and !(c == d) => c != d, so the only case left is
            // no character... hence this is unreachable)
            Some(_invalid) => {
                unreachable!()
            }
            None => {
                // TODO: report on unexpected EOF (or non-terminated character?)
                Token {
                    lexeme: Lexeme::Unknown(LexError::UnterminatedChar),
                    span: self.source.span_from(start),
                }
            }
        }
    }

    fn infix(&mut self) -> Token {
        let span = self.source.eat_while(is_infix_char).span();
        let lexeme = match &self.source[span] {
            "->" => Lexeme::ArrowR,
            "<-" => Lexeme::ArrowL,
            "=>" => Lexeme::FatArrow,
            ":" => Lexeme::Colon,
            "::" => Lexeme::Colon2,
            "|" => Lexeme::Pipe,
            "=" => Lexeme::Equal,
            "\\" => Lexeme::Lambda,
            "@" => Lexeme::At,
            "!" => Lexeme::Bang,
            "#" => {
                let hash = Lexeme::Pound;
                let bang = self
                    .source
                    .spanned(|s| {
                        if s.bump_on('!') {
                            Some(Lexeme::Bang)
                        } else {
                            None
                        }
                    })
                    .transpose();
                if self.source.on_char('[') {
                    let placement = if let Some(b) = bang {
                        self.stack.push(Token::from(b));
                        Placement::After
                    } else {
                        Placement::Before
                    };
                    self.set_meta_mode(placement);
                };
                hash
            }
            "." => Lexeme::Dot,
            ".." => Lexeme::Dot2,
            // this shouldn't be possible at this point!!
            "~" => Lexeme::Tilde,
            "-" => Lexeme::Infix(*symbol::reserved::MINUS),
            s => Lexeme::Infix(symbol::intern_once(s)),
        };
        Token { lexeme, span }
    }

    fn _hash(&mut self) -> Lexeme {
        let hash = Lexeme::Pound;
        let bang = self
            .source
            .spanned(|s| {
                if s.bump_on('!') {
                    Some(Lexeme::Bang)
                } else {
                    None
                }
            })
            .transpose();
        if self.source.on_char('[') {
            let placement = if let Some(b) = bang {
                self.stack.push(Token::from(b));
                Placement::After
            } else {
                Placement::Before
            };
            self.set_meta_mode(placement);
        };
        hash
    }

    fn shebang(&mut self) {
        #![allow(unused)]
        todo!()
    }

    fn backtick(&mut self) -> Token {
        use LexError::{EmptyInfix, InvalidInfix, UnterminatedInfix};
        use Lexeme::{Eof, Infix, Lower, Unknown};
        fn not_tick(c: char) -> bool {
            c != '`'
        }
        let start = self.source.get_pos();
        self.source.next();
        match self.source.peek().copied() {
            Some(c) if is_ident_start(c) => {
                let start = self.get_pos();
                match self.identifier(c) {
                    Token {
                        lexeme: Lower(sym),
                        span,
                    } => {
                        if self.source.on_char('`') {
                            self.source.next();
                            Token {
                                lexeme: Infix(sym),
                                span,
                            }
                        } else {
                            match self.source.peek() {
                                Some(_) => {
                                    let sp = self.source.eat_while(not_tick).span();
                                    Token {
                                        lexeme: Unknown(InvalidInfix),
                                        span: Span(start, sp.end()),
                                    }
                                }
                                None => {
                                    let span = self.source.span_from(start);
                                    self.stack.push(Token { lexeme: Eof, span });
                                    Token {
                                        lexeme: Unknown(UnterminatedInfix),
                                        span,
                                    }
                                }
                            }
                        }
                    }
                    _token => {
                        let (sp, _loc) = self.source.eat_while(not_tick).parts();
                        Token {
                            lexeme: if self.source.on_char('`') {
                                self.source.next();
                                Unknown(InvalidInfix)
                            } else {
                                Lexeme::Eof
                            },
                            span: Span(start, sp.end()),
                        }
                    }
                }
            }
            Some('`') => {
                self.source.next();
                Token {
                    lexeme: Unknown(EmptyInfix),
                    span: self.span_from(start),
                }
            }
            Some(_) => {
                let (sp, _loc) = self.source.eat_while(not_tick).parts();
                Token {
                    span: Span(start, sp.end()),
                    lexeme: if self.source.on_char('`') {
                        self.source.next();
                        Unknown(InvalidInfix)
                    } else {
                        Eof
                    },
                }
            }
            None => Token {
                lexeme: Unknown(UnterminatedInfix),
                span: self.source.span_from(start),
            },
        }
    }
    fn mid_string(
        &mut self,
        escaped: &mut bool,
        terminated: &mut bool,
        buf: &mut String,
    ) -> BytePos {
        while let Some(c) = self.source.next() {
            if *escaped {
                *escaped = false;
                match c {
                    esc if is_escapable(esc) => buf.push(get_escaped(esc)),
                    // preserve indentation/ignore whitespace on new line
                    // e.g. `"a b c\
                    //        d e"` lexes as "a b cd e"
                    '\n' => {
                        self.source.eat_whitespace();
                    }
                    _ => {
                        buf.push(c);
                    }
                };
            } else if c == '"' {
                *terminated = true;
                break;
            } else if c == '\\' {
                *escaped = true;
            } else {
                buf.push(c);
            }
        }
        self.source.get_pos()
    }

    fn string(&mut self) -> Token {
        let start = self.source.get_pos();
        let mut buf = String::new();
        self.source.next();
        let mut escaped = false;
        let mut terminated = false;
        let end = self.mid_string(&mut escaped, &mut terminated, &mut buf);
        let span = Span(start, end);
        let lexeme = if !terminated {
            Lexeme::Unknown(LexError::UnterminatedString)
        } else {
            Lexeme::Lit(Literal::Str(symbol::intern_once(buf.as_str())))
        };
        Token { lexeme, span }
    }

    fn identifier(&mut self, first: char) -> Token {
        if first == 'w' && self.source.bump_on('#') {
            let (span, _) = self.source.eat_until_whitespace().parts();
            let sym = symbol::intern_once(&self.source[span]);
            // lex all raw idents as lower
            return Token {
                lexeme: Lexeme::Lower(sym),
                span: span.grow_left(b"w#"),
            };
        }

        debug_assert!(self.source.on_char(is_ident_start));

        let (span, _) = self.source.eat_while(is_ident_char).parts();

        let text = &self.source[span];
        let token = |lexeme: Lexeme| Token { lexeme, span };

        if text == "_" {
            token(Lexeme::Underline)
        } else if let Some(kw) = Keyword::from_str(text) {
            token(Lexeme::Kw(kw))
        } else {
            token(if first.is_uppercase() {
                Lexeme::Upper
            } else {
                Lexeme::Lower
            }(symbol::intern_once(text)))
        }
    }

    pub fn pragma(&mut self, span: Span) -> Option<Token> {
        use Associativity as A;
        if self.mode.is_meta() {
            match Attr::scan(&mut self.source) {
                Some(Spanned(atr, sp_at)) => match atr {
                    Attr::Fixity => {
                        if self.source.on_char(Digit::digit_char) {
                            Digit::scan(&mut self.source).map(|Spanned(digit, sp_d)| match A::scan(
                                &mut self.source,
                            ) {
                                Some(Spanned(assoc, sp_a)) => Token {
                                    lexeme: Lexeme::Meta(Pragma::Fixity(assoc, digit)),
                                    span: sp_d.union(&sp_a.union(&sp_at)),
                                },
                                None => Token {
                                    lexeme: Lexeme::Meta(Pragma::Fixity(A::None, digit)),
                                    span: sp_at.union(&sp_d),
                                },
                            })
                        } else {
                            A::scan(&mut self.source).map(|Spanned(aso, sp_a)| {
                                match Digit::scan(&mut self.source) {
                                    Some(Spanned(digit, sp_d)) => Token {
                                        lexeme: Lexeme::Meta(Pragma::Fixity(aso, digit)),
                                        span: sp_a.union(&sp_d),
                                    },
                                    None => Token {
                                        lexeme: Lexeme::Meta(Pragma::Fixity(aso, Digit::Nine)),
                                        span: sp_a.union(&sp_at),
                                    },
                                }
                            })
                        }
                    }
                    attr => Some(Token {
                        lexeme: Lexeme::Meta(Pragma::Attr(attr)),
                        span,
                    }),
                },
                None => {
                    let pos = self.get_pos();
                    if let Some(&'|') = self.source.peek() {
                        self.reset_mode();
                        return Some(Token {
                            lexeme: Lexeme::Pipe,
                            span: self.span_from(pos),
                        });
                    };
                    None
                }
            }
        } else {
            None
        }
    }

    /// Utility method called only by `number` method when encountering 0 as the
    /// first digit. This is a separate method as prefixed integers follow a
    /// different set of lexical rules than general numeric literals.
    fn zero_first_int(
        &mut self,
        start: BytePos,
        has_exp: &mut bool,
        empty_exp: &mut Option<bool>,
        sign_positive: &mut Option<bool>,
    ) -> Option<Token> {
        self.source.next();
        if self.source.test_char(|c| c.is_whitespace()) {
            return Some(Token {
                lexeme: Lexeme::Lit(Literal::Int(0)),
                span: self.source.span_from(start),
            });
        };

        let base = match self.source.peek() {
            Some(&('b' | 'B')) => Some(Base::Bin),
            Some(&('o' | 'O')) => Some(Base::Oct),
            Some(&('x' | 'X')) => Some(Base::Hex),
            Some(&('e' | 'E')) => {
                *has_exp = true;
                *empty_exp = Some(false);
                None
            }
            _ => None,
        };
        if let Some(base) = base {
            self.source.next();
            let mut tok = self.integer(base);
            tok.span.0 = start;
            return Some(tok);
        }
        if *has_exp || matches!(empty_exp, Some(false)) {
            self.source.next();
            if self.source.on_char('-') {
                self.source.next();
                *sign_positive = Some(false);
            } else if self.source.on_char('+') {
                self.source.next();
                *sign_positive = Some(true);
            };
        };

        None
    }

    fn number(&mut self, c: char) -> Token {
        // we accept only 1 `.` for floats; if we see `..`, then we stop,
        // return the currently lexed number, and push the `..` token on the
        // stack to be returned next;
        let mut has_dot = false;
        // have we seen an `e` between numbers?
        let mut has_exp = false;
        // have we seen at least 1 integer after having seen `e`, `e+` or `e-`?
        let mut empty_exp = None;
        // have we seen a `+` or `-` after an `e`? Note that by default we set
        // this to `None` to enforce three possible cases:
        // 1. None => we have not seen any reason to accept `+` or `-`
        // 2. Some(true) => we have either seen `e+` or `eN` where N is a digit
        // 3. Some(false) => we have seen `e-`
        let mut sign_positive = None;
        let start = self.source.get_pos();
        if c == '0' {
            if let Some(token) =
                self.zero_first_int(start, &mut has_exp, &mut empty_exp, &mut sign_positive)
            {
                return token;
            }
        };

        if self.source.on_char('.') {
            let a = self.get_pos();
            self.source.next();
            if self.source.on_char('.') {
                self.source.next();
                self.stack.push(Token {
                    lexeme: Lexeme::Dot2,
                    span: self.span_from(a),
                });
                return Token {
                    lexeme: Lexeme::Lit(Literal::Int(0)),
                    span: Span(start, a),
                };
            } else {
                has_dot = true;
            }
        }

        while let Some(&c) = self.source.peek() {
            match c {
                '_' | '0'..='9' => {
                    self.source.next();
                }
                'e' | 'E' if !has_exp => {
                    has_exp = true;
                    self.source.next();
                    empty_exp = Some(true);
                }
                '+' | '-' if matches!(empty_exp, Some(true)) => {
                    self.source.next();
                    if self.source.test_char(|c| c.is_digit(10)) {
                        continue;
                    } else {
                        let span = Span(start, self.source.get_pos());
                        eprintln!(
                            "Invalid (unterminated) exponential number `{}`",
                            &self.source[span]
                        );
                        return Token {
                            lexeme: Lexeme::Unknown(LexError::MissingExponent),
                            span,
                        };
                    }
                }
                '.' if !has_dot && !has_exp => {
                    let end = self.source.get_pos();
                    has_dot = true;
                    self.source.next();
                    if self.source.bump_on('.') {
                        self.stack.push(Token {
                            lexeme: Lexeme::Dot2,
                            span: self.span_from(start),
                        });
                        let span = Span(start, end);
                        return Token {
                            lexeme: Literal::parse_int(&self.source[span], Base::Dec)
                                .ok()
                                .map(Literal::Int)
                                .map(Lexeme::Lit)
                                .unwrap_or_else(|| {
                                    let span = self.span_from(start);
                                    eprintln!("Invalid number `{}`", &self.source[span]);
                                    Lexeme::Unknown(LexError::MalformedNumber)
                                }),
                            span,
                        };
                    };
                }
                _ => break,
            }
        }
        let span = Span(start, self.source.get_pos());
        let src = &self.source[span];

        let lexeme = if !has_dot && !has_exp && sign_positive.is_none() {
            if src.len() < 15 {
                Literal::parse_int(src, Base::Dec).ok().map(Literal::Int)
            } else {
                Literal::parse_nat(src, Base::Dec).ok().map(Literal::Nat)
            }
        } else if has_dot && src.len() < 15 {
            Literal::parse_float(src).ok().map(Literal::Float)
        } else {
            Literal::parse_double(src).ok().map(Literal::Double)
        }
        .map(Lexeme::Lit)
        .unwrap_or_else(|| Lexeme::Unknown(LexError::MalformedNumber));
        Token { lexeme, span }
    }

    fn integer(&mut self, base: Base) -> Token {
        let radix = base.radix();
        let (span, _) = self.source.eat_while(|c| c.is_digit(radix)).parts();
        let src = &self.source[span];
        let lexeme = Literal::parse_int(src, base)
            .ok()
            .map(Literal::Int)
            .map(Lexeme::Lit)
            .unwrap_or_else(|| Lexeme::Unknown(LexError::MalformedNumber));
        Token { lexeme, span }
    }

    /// A tilde `~` may either lex as:
    /// - a single *tilde* lexeme `~`
    /// - a block comment start `~{`, with everything up until `}~` as a comment
    /// - a doc comment (multiple tildes followed by a `|`,`>`, `:`, or `<`)
    /// - a line comment (multiple tildes followed by any other character)
    fn tilde(&mut self) -> Token {
        use Lexeme::{Infix, Tilde};
        let start = self.source.get_pos();
        assert!(self.source.on_char('~'));
        self.source.next();
        let span = self.source.span_from(start);
        let tilde = Token {
            lexeme: Tilde,
            span,
        };
        if let Some(c) = self.source.peek() {
            if c == &'~' {
                // if we strictly need TWO tildes for doc comments
                // or do we not care how many tildes there are aslong
                // there is more than 1?
                // => ANY >= 2
                self.source.eat_while_on('~');
                self.maybe_doc_comment();
                self.token()
            } else if c == &'{' {
                self.source.next();
                self.block_comment();
                self.token()
            } else if is_infix_char(*c) {
                // note that we know c is not a tilde, so
                // we have something like TILDE INFIX where INFIX does NOT
                // start with a tilde (otherwise it would be a comment!)
                let span = span.union(&self.source.eat_while(is_infix_char).span());
                let lexeme = Infix(self.span_symbol(span));
                Token { lexeme, span }
            } else {
                let tok = self.token();
                self.stack.push(tok);
                tilde
            }
        } else {
            tilde
        }
    }

    // rewrite for handling nested block comments correctly
    // method starts after having passed the first `~{`
    fn block_comment(&mut self) {
        let mut depth = 1;

        // let mut close = true;
        let mut interrupted = false;
        let start = self.get_pos();
        loop {
            if depth == 0 {
                break;
            }
            if self.source.is_done() {
                interrupted = true;
                break;
            }

            match self.source.peek() {
                Some('~') => {
                    self.source.next();
                    if self.on_char('{') {
                        depth += 1;
                    }
                }
                Some('}') => {
                    self.source.next();
                    if self.on_char('~') {
                        depth -= 1;
                        self.source.next();
                    }
                }
                _ => {
                    self.source.next();
                    continue;
                }
            };
        }
        // since the span we got included the terminating `}` from `}~`,
        // we shave it off
        let span = self.span_from(start).shrink_right('}');
        if interrupted {
            self.stack.push(Token {
                lexeme: Lexeme::Unknown(LexError::UnterminatedComment),
                span,
            })
        } else {
            // since we stopped at the last `~`, we eat it
            self.source.next();
            self.comments.push(Comment::Block(span));
        }
    }

    /// Doc comments may be specialized in a layout-specific fashion based
    /// on the character found following the initial `~~`:
    /// - `~~>` marks the *beginning* of a paragraph, and hence will render
    ///   a line break before the commented text, and should be found
    ///   *above* the entity being commented.
    /// - `~~|` marks the *middle* of a paragraph, and will *not* render any
    ///   new lines before or after its contents, instead inheriting the
    ///   style followed by the immediately preceding documentation lines.
    /// - `~~:` marks documentation that has been added *after* (or *below*)
    ///   the source code entity being documented.
    ///
    /// Additionally, if we encounter `~~<X>` for some identifier `X`,
    /// then the line's doc style will be preserved until reaching a `~~;`,
    /// which is idiomatically expected to be found on the next line
    ///
    /// Below we see an example of all the doc flags listed above in use:
    /// ```wysk
    /// ~~> This would be the beginning of a paragraph descibing the entity
    /// ~~| described by the source code following this doc comment block.
    /// ~~| Notice how `~~|` is used as a *line continuation*, and hence
    /// ~~| will *only* render a single whitespace character ` ` *before*
    /// ~~| and *after* its contents. Notice that this block documents the
    /// ~~| function `foo` below.
    /// fn foo :: a -> (a, a)
    /// | x = (x, x)
    /// ~~: This doc comment here would be grouped with the above doc
    /// ~~| comments for the item `foo`.
    /// ~~| To show embedded code within doc comments, we will show below
    /// ~~| the equivalent code in Rust using the embedded doc code syntax,
    /// ~~| where we specify that the following block of code is *Rust*
    /// ~~| code. Note that the language identifier is read in a
    /// ~~| case-insensitive manner, with the text between `<` and `>`
    /// ~~| trimmed for whitespace on both ends so that the flags
    /// ~~| `~~<Rust>`, `~~<RUST>`, `~~< RUST>`,
    /// ~~| `~~< rusT >`, etc., are all equivalent!
    /// ~~<rust>
    /// ~~| fn foo<A>(a: A) -> (A, A) {
    /// ~~|     (a, a)
    /// ~~| }
    /// ~~;
    /// ```
    fn maybe_doc_comment(&mut self) {
        // let's get the rest of the non-whitespace chars into a str
        // then we can use this to get the line kind
        // examples:
        // 1.) `~~> abcd efgh`
        //        ^           <- consume `>`, giving us `DocHead`
        // 2.) `~~this is a regular line to be ignored`
        //        ^^^^        <- consume `this`, giving us `Ignored`
        // 3.) `~~ | this is also ignored!`
        //        *because of the space here, this line is `Ignored`*
        // 4.) `~~<abc> ...`  <- consume `<abc>`, giving us `Embedded`
        //        ^^^^^
        let (first, _) = self.source.eat_until_whitespace().parts();
        let linekind = LineKind::from_str(&self.source[first]);
        // now we consume the rest of the line, ensuring to join the
        let (rest, _) = self.source.eat_while(|c| c != '\n').parts();
        // ignore newlines
        self.source.next();
        let span = first.union(&rest);
        let id = CommentId::new(self.comments.len());
        self.comments.push(Comment::Doc { id, span, linekind });
    }

    fn unknown(&mut self) -> Token {
        self.spanned(|_| Lexeme::Unknown(LexError::Unsupported))
            .into()
    }

    pub fn get_source(&'t self) -> &Source {
        &self.source
    }

    pub fn get_source_mut(&'t mut self) -> &'t mut Source {
        &mut self.source
    }

    pub fn write_to_string(&self, buf: &mut String) {
        buf.push_str(self.source.src);
    }
}

impl<'t> Iterator for Lexer<'t> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        match self.current.take() {
            Some(t) => Some(t),
            None => match self.token() {
                t if t.lexeme.is_eof() => None,
                t => Some(t),
            },
        }
    }
}

pub fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || matches!(c, '_')
}
pub fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || matches!(c, '_' | '\'')
}

pub fn get_escaped(c: char) -> char {
    match c {
        't' => '\t',
        'n' => '\n',
        'r' => '\r',
        '"' => '\"',
        '\'' => '\'',
        '\\' => '\\',
        'b' => '\x08',
        'f' => '\x0C',
        _ => c,
    }
}

pub fn is_escapable(c: char) -> bool {
    matches!(c, 't' | 'n' | 'r' | '"' | '\'' | '\\' | 'b' | 'f')
}

pub fn unescape_string(mut s: &str) -> String {
    let mut buf = String::new();
    while let Some(i) = s.bytes().position(|byte| byte == b'\\') {
        let c = match s.as_bytes()[i + 1] {
            b'\'' => '\'',
            b'"' => '"',
            b'\\' => '\\',
            b'/' => '/',
            b'n' => '\n',
            b'r' => '\r',
            b't' => '\t',
            _ => {
                panic!("Invalid escape found at byte {} for string `{}`", i, s)
            }
        };
        buf.push_str(&s[..i]);
        buf.push(c);
        s = &s[i + 2..];
    }
    buf.push_str(s);
    buf
}

pub fn is_infix_char(c: char) -> bool {
    matches!(
        c,
        '~' | '!'
            | '@'
            | '#'
            | '$'
            | '%'
            | '^'
            | '&'
            | '*'
            | '-'
            | '+'
            | '/'
            | '\\'
            | ':'
            | '?'
            | '<'
            | '='
            | '>'
            | '.'
            | '|'
    )
}

#[cfg(test)]
mod test {
    use wy_intern::{intern_many, symbol};

    use super::*;

    #[test]
    fn test_peeking() {
        let src = r#"fn 4..5 foo :: a -> b;"#;
        let mut lexer = Lexer::new(src);
        println!("first peek: {:?}", lexer.peek());
        let mut i = 1;
        while !lexer.is_done() {
            i += 1;
            println!("peek #{}: {:?}", i, lexer.peek());
            println!("bump #{}: {}", i - 1, lexer.bump());
            println!("post-bump peek #{}: {:?}", i - 1, lexer.peek());
        }
    }

    #[test]
    fn test_lex_number() {
        let src = "123 0b11";
        let mut lexer = Lexer::new(src);
        let n1 = lexer.number('1');
        println!("{:?}", &n1);
        lexer.source.eat_whitespace();
        let n2 = lexer.number('0');
        println!("{:?}", n2);
        assert_eq!("123", &lexer.source[n1.span]);
        assert_eq!("0b11", &lexer.source[n2.span]);
    }

    #[test]
    fn test_tokens() {
        let src = "a + b )*( 'x' .. '\n' 3.56 4e12";
        let mut lexer = Lexer::new(src);
        let a = lexer.token();
        assert_eq!(a.lexeme, Lexeme::Lower(symbol::intern_once("a")));
        let plus = lexer.token();
        assert_eq!(plus.lexeme, Lexeme::Infix(symbol::intern_once("+")));
        let b = lexer.token();
        assert_eq!(b.lexeme, Lexeme::Lower(symbol::intern_once("b")));
        let parenr = lexer.token();
        assert_eq!(parenr.lexeme, Lexeme::ParenR);
        let times = lexer.token();
        assert_eq!(times.lexeme, Lexeme::Infix(symbol::intern_once("*")));
        let parenl = lexer.token();
        assert_eq!(parenl.lexeme, Lexeme::ParenL);
        let charx = lexer.token();
        assert_eq!(charx.lexeme, Lexeme::Lit(Literal::Char('x')));
        let dot2 = lexer.token();
        assert_eq!(dot2.lexeme, Lexeme::Dot2);
        let nl = lexer.token();
        assert_eq!(nl.lexeme, Lexeme::Lit(Literal::Char('\n')));
        let _356 = lexer.token();
        assert_eq!(_356.lexeme, Lexeme::Lit(Literal::Float(3.56)));
        let _4e12 = lexer.token();
        assert_eq!(_4e12.lexeme, Lexeme::Lit(Literal::Double(4e12_f64)));

        println!("{:?}", lexer);

        println!("{:#?}", Lexer::new(src).into_iter().collect::<Vec<_>>())
    }

    #[test]
    fn test_dots() {
        let mut lexer = Lexer::new("4..5 4.5 a.b a..b [1..2]");
        let [a, b] = symbol::intern_many(["a", "b"]);
        assert_eq!(lexer.token().lexeme, Lexeme::Lit(Literal::Int(4)));
        assert_eq!(lexer.token().lexeme, Lexeme::Dot2);
        assert_eq!(lexer.token().lexeme, Lexeme::Lit(Literal::Int(5)));
        assert_eq!(
            lexer.token().lexeme,
            Lexeme::Lit(Literal::Float(4.5_f32))
        );
        assert_eq!(lexer.token().lexeme, Lexeme::Lower(a));
        assert_eq!(lexer.token().lexeme, Lexeme::Dot);
        assert_eq!(lexer.token().lexeme, Lexeme::Lower(b));
        assert_eq!(lexer.token().lexeme, Lexeme::Lower(a));
        assert_eq!(lexer.token().lexeme, Lexeme::Dot2);
        assert_eq!(lexer.token().lexeme, Lexeme::Lower(b));
        assert_eq!(lexer.token().lexeme, Lexeme::BrackL);
        assert_eq!(lexer.token().lexeme, Lexeme::Lit(Literal::Int(1)));
        assert_eq!(lexer.token().lexeme, Lexeme::Dot2);
        assert_eq!(lexer.token().lexeme, Lexeme::Lit(Literal::Int(2)));
        assert_eq!(lexer.token().lexeme, Lexeme::BrackR);
        assert_eq!(lexer.token().lexeme, Lexeme::Eof);

        println!(
            "{:#?}",
            Lexer::new("[ x | _ <- [0..n] ]").collect::<Vec<_>>()
        )
    }

    #[test]
    fn test_infixes() {
        use Lexeme::*;
        // also testing for tilde-related lexemes, since a tilde can be
        // found in either the single tilde lexeme, as comment markers, OR
        // as *ONE OF* the characters in an infix
        let source = r#"\ \\ \> = == : ~{ im ignored!!! }~ :: ~ . .. ~> ~| `boop`"#;
        let mut lexer = Lexer::new(source);
        println!("collected: {:#?}", lexer.clone().collect::<Vec<_>>());
        let [lamr, lam2, eq2, tarrow, tpipe, boop] =
            intern_many([r#"\>"#, r#"\\"#, "==", "~>", "~|", "boop"]);
        let expected = [
            (Lambda, "\\"),
            (Infix(lam2), "\\\\"),
            (Infix(lamr), "\\>"),
            (Equal, "="),
            (Infix(eq2), "=="),
            (Colon, ":"),
            (Colon2, "::"),
            (Tilde, "~"),
            (Dot, "."),
            (Dot2, ".."),
            (Infix(tarrow), "~>"),
            (Infix(tpipe), "~|"),
            (Infix(boop), "boop"),
            (Eof, ""),
        ];
        lexer
            .by_ref()
            .zip(expected)
            .for_each(|(token, (lexeme, txt))| {
                assert_eq!(token.lexeme, lexeme);
                assert_eq!(&source[token.span.range()], txt);
            });
        let comment = lexer.comments[0];
        assert!(matches!(comment, Comment::Block(..)));
        println!("{}", &source[comment.span().range()]);
        println!("{:#?}", lexer)
    }

    #[test]
    fn test_nested_comments() {
        use wy_intern::Symbol;
        let src =
            r#" fn foo ~{ fee fi ~{ fo... }~ fum }~ bar ~{ comment }~ ~{ ~~{ {} ~} }~ }~ baz;"#;
        let lexer = Lexer::new(src);
        let expected = [
            Lexeme::Kw(Keyword::Fn),
            Lexeme::Lower(Symbol::intern("foo")),
            Lexeme::Lower(Symbol::intern("bar")),
            Lexeme::Lower(Symbol::intern("baz")),
            Lexeme::Semi,
        ];

        lexer
            .zip(expected)
            .for_each(|(tok, lex)| assert_eq!(tok.lexeme, lex))
    }
}
