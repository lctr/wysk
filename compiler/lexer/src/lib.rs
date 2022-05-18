use wy_intern as intern;
use wy_span as span;

use intern::symbol;

use span::{Span, Spanned, WithSpan};
use token::Base;
pub use token::{LexError, Keyword, Lexeme, Literal, Token};
pub use stream::{Lexer, Source};

use comment::{LineKind, Comment, CommentId};

pub mod token;
pub mod comment;
pub mod stream;


impl<'t> Lexer<'t> {
    pub fn token(&mut self) -> Token {
        #[inline]
        fn lex_eof(this: &mut Lexer) -> Token {
            let Spanned(lexeme, span) = this.source.spanned(|_| Lexeme::Eof);
            Token { lexeme, span }
        }

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

    fn tokenize(&mut self, c: char) -> Token {
        let lex = |this: &mut Self, lexeme| {
            let Spanned(lexeme, span) = this.source.spanned(|s| {
                s.next();
                lexeme
            });
            Token { lexeme, span }
        };
        match c {
            '~' => self.tilde(),
            ';' => lex(self, Lexeme::Semi),
            '\'' => self.character(),
            '"' => self.string(),
            '`' => self.backtick(),
            c if c.is_digit(10) => self.number(c),
            c if is_ident_start(c) => self.identifier(c),
            '(' => lex(self, Lexeme::ParenL),
            ')' => lex(self, Lexeme::ParenR),
            '[' => lex(self, Lexeme::BrackL),
            ']' => lex(self, Lexeme::BrackR),
            '{' => lex(self, Lexeme::CurlyL),
            '}' => lex(self, Lexeme::CurlyR),
            ',' => lex(self, Lexeme::Comma),
            c if is_infix_char(c) => self.infix(),
            _ => self.unknown(),
        }
    }

    fn character(&mut self) -> Token {
        let start = self.source.get_pos();
        self.source.next();
        match self.source.peek().copied() {
            Some(c) if c != '\\' => {
                self.source.next();
                if self.source.on_char('\'') {
                    self.source.next();
                    Token {
                        lexeme: Lexeme::Lit(Literal::Char(c)),
                        span: Span(start, self.source.get_pos()),
                    }
                } else {
                    // TODO: report on unterminated character
                    eprintln!("Character lexeme not terminated at {}! Expected `'`, but found `{}` while reading `'{}`", 
                    start, 
                    self.source.peek().unwrap_or_else(|| &'\0'),
                    c
                );
                todo!()
                }
            }
            Some(c) if c == '\\' => {
                self.source.next();
                let _pos2 = self.source.get_pos();
                if matches!(self.source.peek(), Some(c) if is_escapable(*c)) {
                    self.source.next();
                    let _pos3 = self.source.get_pos();
                    if self.source.on_char('\'') {
                        self.source.next();
                        Token {
                            lexeme: Lexeme::Lit(Literal::Char(get_escaped(c))),
                            span: Span(start, self.source.get_pos()),
                        }
                    } else {
                        // TODO: report on unterminated character
                        eprintln!("Character lexeme not terminated at {}! Expected `'`, but found `{}` ", 
                            _pos3, 
                            self.source.peek().unwrap_or_else(|| &'\0')
                        );
                        todo!()
                    }
                } else {
                    // TODO: report on invalid escape!
                    eprintln!("Invalid escape found at {}! `\\{}` is not a valid escape!", _pos2, c);
                    todo!()
                }
            }
            // unreachable??
            Some(_invalid) => {
                self.source.next();
                // TODO: report on invalid character
                todo!()
            }
            None => {
                // TODO: report on unexpected EOF (or non-terminated character?)
                todo!()
            }
        }
    }

    fn infix(&mut self) -> Token {
        let (span, _) = self.source.eat_while(is_infix_char);
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
            "#" => Lexeme::Pound,
            "." => Lexeme::Dot,
            ".." => Lexeme::Dot2,
            // these shouldn't be possible at this point!!
            "~" => Lexeme::Tilde,
            s => Lexeme::Infix(symbol::intern_once(s)),
        };
        Token { lexeme, span }
    }

    fn backtick(&mut self) -> Token {
        let start = self.source.get_pos();
        self.source.next();
        match self.source.peek().copied() {
            Some(c) if is_ident_start(c) => {
                let start = self.get_pos();
                match self.identifier(c) {
                    Token { lexeme: Lexeme::Lower(sym), span } => {
                        if self.source.on_char('`') {
                            self.source.next();
                            Token { 
                                lexeme: Lexeme::Infix(sym), 
                                span
                            }
                        } else {
                            match self.source.peek() {
                                Some(_) => {
                                    let (sp, _) = self.source.eat_while(|c| c != '`');
                                    Token { lexeme: Lexeme::Unknown(LexError::InvalidInfix), span: Span(start, sp.end())}
                                }
                                None => {
                                    let span = self.source.span_from(start);
                                    self.stack.push(Token { 
                                        lexeme: Lexeme::Eof,
                                        span
                                    });
                                    Token { lexeme: Lexeme::Unknown(LexError::UnterminatedInfix), span }
                                }
                            }
                        }
                    }
                    _token => {
                        let (sp, _loc) = self.source.eat_while(|c| c != '`');
                        let span = Span(start, sp.end());
                        
                        Token { lexeme: if self.source.on_char('`') {
                            self.source.next();
                            Lexeme::Unknown(LexError::InvalidInfix)
                        } else { Lexeme::Eof 
                        }, span }
                    }
                }
            }
            Some('`') => {
                self.source.next();
                Token { lexeme: Lexeme::Unknown(LexError::EmptyInfix), span: Span(start, self.source.get_pos())}
            } 
            Some(_) => {
                let (sp, _loc) = self.source.eat_while(|c| c != '`');
                let span = Span(start, sp.end());
                
                Token { 
                    span,
                    lexeme: if self.source.on_char('`') {
                        self.source.next();
                        Lexeme::Unknown(LexError::InvalidInfix)
                    } else { 
                        Lexeme::Eof 
                    }, 
                }
            }
            None => Token { 
                lexeme: Lexeme::Unknown(LexError::UnterminatedInfix), 
                span: self.source.span_from(start)
            }
        }
    }

    fn string(&mut self) -> Token {
        let start = self.source.get_pos();
        let mut buf = String::new();
        self.source.next();
        let mut escaped = false;
        let mut terminated = false;
        while let Some(c) = self.source.next() {
            if escaped {
                escaped = false;
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
                terminated = true;
                break;
            } else if c == '\\' {
                escaped = true;
            } else {
                buf.push(c);
            }
        }
        let span = Span(start, self.source.get_pos());
        if !terminated {
            Token { 
                lexeme: Lexeme::Unknown(LexError::UnterminatedString), 
                span 
            }
        } else {
            let sym = symbol::intern_once(buf.as_str());
            Token {
                lexeme: Lexeme::Lit(Literal::Str(sym)),
                span,
            }
        }
    }

    fn identifier(&mut self, first: char) -> Token {
        debug_assert!(
            matches!(self.source.peek(), Some(c) if is_ident_start(*c))
        );
        let name = if first.is_uppercase() {
            Lexeme::Upper
        } else {
            Lexeme::Lower
        };
        let (span, _) = self.source.eat_while(is_ident_char);
        let text = &self.source[span];
        let token = |lexeme: Lexeme| Token { lexeme, span };

        if text == "_" {
            token(Lexeme::Underline)
        } else if let Some(kw) = Keyword::from_str(text) {
            token(Lexeme::Kw(kw))
        } else {
            token(name(symbol::intern_once(text)))
        }
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
            self.source.next();
            if self.source.test_char(|c| c.is_whitespace()) {
                return Token {
                    lexeme: Lexeme::Lit(Literal::Int(0)),
                    span: self.source.span_from(start),
                };
            };

            let base = match self.source.peek() {
                Some(&('b' | 'B')) => Some(Base::Bin),
                Some(&('o' | 'O')) => Some(Base::Oct),
                Some(&('x' | 'X')) => Some(Base::Hex),
                Some(&('e' | 'E')) => {
                    has_exp = true;
                    empty_exp = Some(false);
                    None
                }
                Some(&'.') => {
                    has_dot = true;
                    None
                }
                _ => None,
            };
            if let Some(base) = base {
                self.source.next();
                let mut tok = self.integer(base);
                tok.span.0 = start;
                return tok;
            }
            if has_dot || has_exp || matches!(empty_exp, Some(false)) {
                self.source.next();
                if self.source.on_char('-') {
                    self.source.next();
                    sign_positive = Some(false);
                } else if self.source.on_char('+') {
                    self.source.next();
                    sign_positive = Some(true);
                };
            };
        };

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
                '.' if has_dot || has_exp => {
                    let span = Span(start, self.source.get_pos());
                    let (Span(_, end), _) =
                        self.source.eat_while(|c| !c.is_whitespace());
                    eprintln!("Invalid number! A number may only have a single decimal (dot), but a second one was found at {}: `{}`",
                    self.source.get_loc(),
                    &self.source[Span(span.0, end)]);
                    return Token {
                        lexeme: Lexeme::Unknown(LexError::MissingIntegral),
                        span,
                    };
                }
                '.' if !has_dot && !has_exp => {
                    let end = self.source.get_pos();
                    has_dot = true;
                    self.source.next();
                    if self.source.on_char('.') {
                        self.source.next();
                        self.stack.push(Token {
                            lexeme: Lexeme::Dot2,
                            span: Span(start, self.source.get_pos()),
                        });
                        let span = Span(start, end);
                        return Token {
                            lexeme: Literal::parse_int(
                                &self.source[span],
                                Base::Dec,
                            )
                            .ok()
                            .map(Literal::Int)
                            .map(Lexeme::Lit)
                            .unwrap_or_else(|| {
                                let span = Span(start, self.source.get_pos());
                                eprintln!(
                                    "Invalid number `{}`",
                                    &self.source[span]
                                );
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
        } else {
            if has_dot && src.len() < 15 {
                Literal::parse_float(src).ok().map(Literal::Float)
            } else {
                Literal::parse_double(src).ok().map(Literal::Double)
            }
        }
        .map(Lexeme::Lit)
        .unwrap_or_else(|| Lexeme::Unknown(LexError::MalformedNumber));
        Token { lexeme, span }
    }

    fn integer(&mut self, base: Base) -> Token {
        let radix = base.radix();
        let (span, _) = self.source.eat_while(|c| c.is_digit(radix));
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
        let start = self.source.get_pos();
        assert!(self.source.on_char('~'));
        self.source.next();
        let span = self.source.span_from(start);
        if let Some(c) = self.source.peek() {
            if c == &'~' {
                // if we strictly need TWO tildes for doc comments
                    // self.source.next();
                // or do we not care how many tildes there are aslong
                // there is more than 1?
                self.source.eat_while(|c| c == '~');
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
                let span = span.union(self.source.eat_while(is_infix_char).0);
                let lexeme = Lexeme::Infix(symbol::intern_once(&self.source[span]));
                Token { lexeme , span }
            } 
            else {
                let tok = self.token();
                self.stack.push(tok);
                Token {
                    lexeme: Lexeme::Tilde,
                    span,
                }
            }
        } else {
            Token {
                lexeme: Lexeme::Tilde,
                span,
            }
        }
    }

    fn block_comment(&mut self) {
        // when we see `~`, was it immediately after a `}`? 
        let mut penult = false;
        // consume characters until reaching the sequence `}~`, stopping on `~`
        let (block_span, _) = self.source.eat_while(|c| match (penult, c) {
            // we saw `}` before this `~`
            (true, '~') => false,
            // we saw `}` before this `}`, so no state change necessary
            (true, '}') 
            // or we saw a non `}` before this `~`
            | (false, '~') => true,
            // we're seeing our first `}` and continue; if the next char is 
            // `~`, we're done
            (false, '}') => { penult = true; true }
            // we saw `}` before this, but since we're not on `}` or `~`, we 
            // reset and now go back to first looking for `}`
            (true, _) => {
                penult = false;
                true
            }
            // we haven't seen a `}`
            (false, _) => true
        });
        // since the span we got included the terminating `}` from `}~`,
        // we shave it off
        let span = block_span.shrink_right('}');
        // since we stopped at the last `~`, we eat it
        self.source.next();
        self.comments.push(Comment::Block(span));
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
        let (first, _) = self.source.eat_until_whitespace();
        let linekind = LineKind::from_str(&self.source[first]);
        // now we consume the rest of the line, ensuring to join the 
        let (rest, _) = self.source.eat_while(|c| c != '\n');
        // ignore newlines
        self.source.next();
        let span = first.union(rest);
        let id = CommentId::new(self.comments.len());
        self.comments.push(Comment::Doc { id, span, linekind });
    }

    fn unknown(&mut self) -> Token {
        todo!()
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

            }
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
    use wy_intern::{symbol, intern_many};

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
        };
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
        assert_eq!(_4e12.lexeme, Lexeme::Lit(Literal::Double(4e12 as f64)));

        println!("{:?}", lexer);

        println!("{:#?}", Lexer::new(src).into_iter().collect::<Vec<_>>())
    }

    #[test]
    fn test_dots() {
        let mut lexer = Lexer::new("4..5 4.5 a.b a..b 1.1.1");
        let [a, b] = symbol::intern_many(["a", "b"]);
        assert_eq!(lexer.token().lexeme, Lexeme::Lit(Literal::Int(4)));
        assert_eq!(lexer.token().lexeme, Lexeme::Dot2);
        assert_eq!(lexer.token().lexeme, Lexeme::Lit(Literal::Int(5)));
        assert_eq!(
            lexer.token().lexeme,
            Lexeme::Lit(Literal::Float(4.5 as f32))
        );
        assert_eq!(lexer.token().lexeme, Lexeme::Lower(a));
        assert_eq!(lexer.token().lexeme, Lexeme::Dot);
        assert_eq!(lexer.token().lexeme, Lexeme::Lower(b));
        assert_eq!(lexer.token().lexeme, Lexeme::Lower(a));
        assert_eq!(lexer.token().lexeme, Lexeme::Dot2);
        assert_eq!(lexer.token().lexeme, Lexeme::Lower(b));
        assert_eq!(lexer.token().lexeme, Lexeme::Unknown(LexError::MissingIntegral));
        assert_eq!(lexer.token().lexeme, Lexeme::Eof);
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
        let [lamr, lam2, eq2, tarrow, tpipe, boop] = intern_many([r#"\>"#, r#"\\"#, "==", "~>", "~|", "boop"]);
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
            (Eof, "")];
        lexer.by_ref().zip(expected).for_each(|(token, (lexeme, txt))| {
            assert_eq!(token.lexeme, lexeme);
            assert_eq!(&source[token.span.range()], txt);
        });
        let comment = lexer.comments[0];
        assert!(matches!(comment, Comment::Block(..)));
        println!("{}", &source[comment.span().range()]);
        println!("{:#?}", lexer)
    }
}
