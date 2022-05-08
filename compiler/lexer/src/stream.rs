use std::{iter::Peekable, str::Chars};

use wy_span::{BytePos, Coord, Location, Span, WithLoc, WithSpan};

use crate::comment::Comment;
use crate::token::{Lexeme, Token};

/// A character iterator that tracks byte position as well as row (=line) and
/// column locations.
#[derive(Clone, Debug)]
pub struct Source<'t> {
    pub(crate) src: &'t str,
    pub(crate) pos: BytePos,
    pub(crate) loc: Coord,
    chars: Peekable<Chars<'t>>,
}

impl<'t> WithLoc for Source<'t> {
    fn get_loc(&self) -> Coord {
        self.loc
    }
}

impl<'t> WithSpan for Source<'t> {
    fn get_pos(&self) -> BytePos {
        self.pos
    }
}

impl<'t> AsRef<str> for Source<'t> {
    fn as_ref(&self) -> &str {
        self.src
    }
}

impl<'t> Source<'t> {
    pub fn new(src: &'t str) -> Self {
        Self {
            src,
            chars: src.chars().peekable(),
            pos: BytePos::ZERO,
            loc: Coord::new(),
        }
    }

    pub fn string(&self) -> String {
        self.src.to_string()
    }

    /// Returns the last byte position possible. Equivalent to taking the length
    /// of the inner string slice and (casting to u32 +) wrapping the result
    /// within a `BytePos`.
    pub fn end_pos(&self) -> BytePos {
        BytePos::strlen(self.src)
    }

    pub fn get_pos(&self) -> BytePos {
        self.pos
    }

    pub fn get_loc(&self) -> Coord {
        self.loc
    }

    pub fn peek(&mut self) -> Option<&char> {
        self.chars.peek()
    }

    /// Takes the character returned -- if any -- from calling the `peek`
    /// method on the underlying character stream and updates the current byte
    /// position in the `pos` field according to the number of bytes in said
    /// character. Additionally updates the layout location, incremeenting the
    /// `row` by 1 if encountering a line-feed `\n`, and otherwise incrementing
    /// the `column` by 1. If there are no characters left, no side effects are
    /// performed and `None` is returned.
    pub fn next(&mut self) -> Option<char> {
        if let Some(c) = self.chars.peek() {
            self.pos += if c == &'\n' {
                self.loc.incr_row()
            } else {
                self.loc.incr_column(*c)
            };
            self.chars.next()
        } else {
            None
        }
    }

    /// Given a predicate, advances the iterator. Returns a boolean indicating
    /// whether the predicate passed (and hence advanced the iterator).
    pub fn next_if<F>(&mut self, f: F) -> bool
    where
        F: Fn(&char) -> bool,
    {
        if self.test_char(f) {
            self.next();
            true
        } else {
            false
        }
    }

    pub fn is_done(&mut self) -> bool {
        self.chars.peek().is_none()
    }

    /// Given an initial `Pos` *start*, returns the span generated from the
    /// *start* to the current `Pos`.
    pub fn span_from(&self, start: BytePos) -> Span {
        Span(start, self.get_pos())
    }

    /// Given an initial `Loc` *start*, returns the `Location` generated
    /// from the *start* to the current `Loc`.
    pub fn location_from(&self, start: Coord) -> Location {
        Location {
            start,
            end: self.get_loc(),
        }
    }

    /// Advances the underlying iterator until a non-whitespace character is
    /// encountered. Returns a span of byte positions corresponding to the
    /// number of bytes consumed.
    #[inline]
    pub fn eat_whitespace(&mut self) -> (Span, Location) {
        let start_pos = self.get_pos();
        let start_loc = self.get_loc();
        while matches!(self.peek(), Some(c) if c.is_whitespace()) {
            self.next();
        }
        (
            Span(start_pos, self.get_pos()),
            Location {
                start: start_loc,
                end: self.get_loc(),
            },
        )
    }

    /// Consumes characters until encountering a whitespace. For use when
    /// skipping the rest of a potential lexeme during a lexing error.
    #[inline]
    pub fn eat_until_whitespace(&mut self) -> (Span, Location) {
        self.eat_while(|c| !c.is_whitespace())
    }

    /// Advance the underlying iterator as long as the given character
    /// predicate holds true.
    pub fn eat_while<F>(&mut self, mut f: F) -> (Span, Location)
    where
        F: FnMut(char) -> bool,
    {
        let start_pos = self.get_pos();
        let start_loc = self.get_loc();
        while matches!(self.peek(), Some(c) if f(*c)) {
            self.next();
        }
        (self.span_from(start_pos), self.location_from(start_loc))
    }

    /// Identifies whether a given character matches that of the character
    /// reference returned by peeking. This will *always* return false if no
    /// more characters are left to be consumed.
    pub fn on_char(&mut self, c: char) -> bool {
        matches!(self.peek(), Some(ch) if ch == &c)
    }

    /// Identifies whether the character returned by `peek` satisfies a given
    /// predicate.
    pub fn test_char<F>(&mut self, f: F) -> bool
    where
        F: Fn(&char) -> bool,
    {
        matches!(self.peek().map(f), Some(true))
    }
}

impl<'t> std::ops::Index<Span> for Source<'t> {
    type Output = str;

    fn index(&self, Span(a, b): Span) -> &Self::Output {
        let len = self.src.len();
        let start = a.as_usize();
        let end = b.as_usize();
        debug_assert!(start <= len && end <= len);
        if start == end {
            ""
        } else if start > end {
            // allow for inverted spans?
            &self.src[end..start]
        } else {
            &self.src[start..end]
        }
    }
}

impl<'t> From<Source<'t>> for String {
    fn from(src: Source<'t>) -> Self {
        src.src.to_string()
    }
}

/// An iterator that produces `Token`s for a given string slice and
/// functions as an interface between source text and parsing.
/// Comments are lexed but stored internally and don't produce any tokens.
///
/// Note that the `Lexer` does not record file-related information but
/// *does* track positional information (such as the current byte position
/// (and "layout" related informations such as line an column numbers)
/// within the source text stream). Therefore it follows that each separate
/// source *file* require a new instance of the `Lexer`.
///
/// The `Lexer` may either be directly composed with another iterator,
/// allowing for functionality within a *single* pass. However, as the
/// `Lexer` implements `Iterator`, it is possible to use it as a
/// `Peekable<Lexer>>` for lookahead. Additionally, multiple passes could
/// also be executed by taking advantage of the free methods provided by
/// the `Iterator` trait such as `by_ref` and a pre-processing pass may be
/// implemented by first allocating a vector of `Token`'s using the
/// `Iteratorcollect::<Vec<_>>` method.
#[derive(Clone, Debug)]
pub struct Lexer<'t> {
    pub(crate) locs: Vec<Coord>,
    pub(crate) stack: Vec<Token>,
    pub(crate) source: Source<'t>,
    pub comments: Vec<Comment>,
    pub current: Option<Token>,
}

impl<'t> WithLoc for Lexer<'t> {
    fn get_loc(&self) -> Coord {
        if let Some(coord) = self.locs.last() {
            *coord
        } else {
            self.source.get_loc()
        }
    }
}

impl<'t> WithSpan for Lexer<'t> {
    fn get_pos(&self) -> BytePos {
        if let Some(ref tok) = self.current {
            // since we've already got the next token in our `current` field, should we return the beginning or end of that token?
            tok.span.start()
        } else {
            self.source.get_pos()
        }
    }
}

impl<'t> Lexer<'t> {
    pub fn new(src: &'t str) -> Self {
        Self {
            locs: Vec::new(),
            stack: Vec::new(),
            source: Source::new(src),
            comments: Vec::new(),
            current: None,
        }
    }

    pub fn src_len(&self) -> usize {
        self.source.src.len()
    }

    pub fn peek(&mut self) -> Option<&Token> {
        match self.current {
            Some(ref t) => Some(t),
            None => {
                if !self.stack.is_empty() {
                    Some(&self.stack[0])
                } else {
                    let token = self.token();
                    self.current.replace(token);
                    self.current.as_ref()
                }
            }
        }
    }

    pub fn bump(&mut self) -> Token {
        match self.current.take() {
            Some(token) => token,
            None => {
                if let Some(tok) = self.stack.pop() {
                    return tok;
                } else {
                    self.eof_token()
                }
            }
        }
    }

    pub fn eof_token(&self) -> Token {
        let pos = self.source.end_pos();
        Token {
            lexeme: Lexeme::Eof,
            span: Span(pos, pos),
        }
    }

    pub fn is_done(&mut self) -> bool {
        matches!(
            &self.current,
            Some(Token {
                lexeme: Lexeme::Eof,
                ..
            })
        ) || self.stack.is_empty() && (self.source.is_done())
    }
}
