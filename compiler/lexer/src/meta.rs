use wy_common::strenum;
use wy_intern::{Symbol, Symbolic};
use wy_span::{Span, Spanned};

use crate::{is_ident_char, Source};

strenum! { Lint is_lint ::
    All "all"
    Unused "unused"
}

impl Symbolic for Lint {
    fn get_symbol(&self) -> Symbol {
        Symbol::from_str(self.as_str())
    }
}

strenum! { Attr is_attr ::
    Inline "inline" | "in_line"
    NoInline "noinline" | "no_inline"
    Fixity "fixity" | "infix"
    Allow "allow"
    Test "test"
    Todo "todo"
    Specialize "specialize" | "specialise"
    Feature "feature" | "feat"
    Cfg "cfg"
    Macro "macro"
}

impl Attr {
    pub fn scan(stream: &mut Source) -> Option<Spanned<Self>> {
        let mut iter = stream.clone();
        let (span, _loc) = iter.eat_while(is_ident_char).parts();
        Self::from_str(&iter[span]).map(|attr| {
            *stream = iter;
            Spanned::new(attr, span)
        })
    }
}

impl Symbolic for Attr {
    fn get_symbol(&self) -> Symbol {
        Symbol::from_str(self.as_str())
    }
}

strenum! { Associativity
    @test_str: is_assoc
    Left "L" | "l" | "left" | "LEFT" | "Left" => is_left
    Right "R" | "r" | "right" | "RIGHT" | "Right" => is_right
    None "N" | "n" | "none" | "NONE" => is_none
}

impl Associativity {
    pub fn scan(stream: &mut Source) -> Option<Spanned<Self>> {
        let mut iter = stream.clone();
        let (span, _loc) = iter
            .eat_while(|c| "lLrRnNeEfFtTiIgGhHtToO".contains(c))
            .parts();
        let assoc = Self::from_str(&iter[span]);
        assoc.map(|assoc| {
            *stream = iter;
            Spanned::new(assoc, span)
        })
    }
}

impl Symbolic for Associativity {
    fn get_symbol(&self) -> Symbol {
        Symbol::from_str(self.as_str())
    }
}

strenum! { Digit is_digit ::
    Zero  "0"     One "1"
    Two   "2"     Three "3"
    Four  "4"     Five "5"
    Six   "6"     Seven "7"
    Eight "8"     Nine "9"
}

impl Digit {
    pub const DECIMAL: &'static str = "0123456789";
    #[inline]
    pub fn digit_char(c: char) -> bool {
        c.is_digit(10)
    }

    pub fn scan(stream: &mut Source) -> Option<Spanned<Self>> {
        let mut iter = stream.clone();
        iter.eat_whitespace();
        let start = iter.get_pos();
        let digit = iter.next().and_then(Self::from_char);
        let span = iter.span_from(start);
        digit.map(|digit| {
            *stream = iter;
            Spanned::new(digit, span)
        })
    }
}

impl Symbolic for Digit {
    fn get_symbol(&self) -> Symbol {
        Symbol::from_str(self.as_str())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Spec {
    BuiltIn(Attr),
    Custom(Symbol),
}

impl Spec {
    pub fn scan(stream: &mut Source) -> Option<Spanned<Spec>> {
        let mut iter = stream.clone();
        // if let Spanned(Some(spec), span) =
        let attr = Attr::scan(&mut iter).map(|attr| attr.map(Self::BuiltIn));
        if attr.is_none() {
            let mut first = true;
            let (span, _) = stream
                .eat_while(|c| {
                    if first {
                        first = false;
                        c.is_alphabetic() || matches!(c, '_')
                    } else {
                        c.is_alphanumeric() || matches!(c, '_' | '\'')
                    }
                })
                .parts();
            if span.is_empty() {
                None
            } else {
                let sym = wy_intern::intern_once(&iter[span]);
                let spec = Self::Custom(sym);
                *stream = iter;
                Some(Spanned(spec, span))
            }
        } else {
            *stream = iter;
            attr
        }
    }
}

impl Symbolic for Spec {
    fn get_symbol(&self) -> Symbol {
        match self {
            Spec::BuiltIn(attr) => attr.get_symbol(),
            Spec::Custom(s) => *s,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Pragma {
    Attr(Attr),
    Allow(Lint),
    Fixity(Associativity, Digit),
    Custom(Symbol),
    Spec(Spec),
    Error(Span),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Placement {
    Before,
    After,
}

impl Placement {
    pub fn str_pairs(&self) -> (&str, &str) {
        match self {
            Placement::Before => ("#[", "]"),
            Placement::After => ("#![", "]"),
        }
    }
    #[inline]
    pub fn is_before(&self) -> bool {
        matches!(self, Self::Before)
    }
    #[inline]
    pub fn is_after(&self) -> bool {
        matches!(self, Self::After)
    }
}
