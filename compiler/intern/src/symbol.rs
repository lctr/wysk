use super::sym;
use serde::{Deserialize, Serialize};
/// Key used to reference stored strings. When a string is interened, a
/// `Symbol` is returned, which can then be used to retrieve the original
/// string representation. This helps reduce the footprint of data structures
/// containing *immutable* strings like variable names, string literals, etc.
///
/// NOTE: These CANNOT be directly instantiated, and in fact may only be created
/// by the global interner as a result of interning strings.
#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Symbol(pub(crate) u32);

impl crate::interner::StrId for Symbol {
    fn from_usize(index: usize) -> Self {
        Symbol(index as u32)
    }

    fn to_usize(&self) -> usize {
        self.0 as usize
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Symbol({}: `{}`)", self.0, self)
    }
}

impl Symbol {
    pub fn as_u32(&self) -> u32 {
        self.0
    }

    pub fn from_char(c: char) -> Symbol {
        if c == ':' {
            sym::COLON
        } else {
            intern_once(&*c.to_string())
        }
    }

    #[inline]
    pub fn for_str(s: &str) -> Symbol {
        intern_once(s)
    }

    pub fn cmp_str(&self, s: impl std::ops::Deref<Target = str>) -> bool {
        &*lookup(*self) == &*s
    }

    pub fn is_digit(&self) -> bool {
        use super::sym::{
            DIGIT_0, DIGIT_1, DIGIT_2, DIGIT_3, DIGIT_4, DIGIT_5, DIGIT_6, DIGIT_7, DIGIT_8,
            DIGIT_9,
        };
        [
            DIGIT_0, DIGIT_1, DIGIT_2, DIGIT_3, DIGIT_4, DIGIT_5, DIGIT_6, DIGIT_7, DIGIT_8,
            DIGIT_9,
        ]
        .contains(self)
    }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl std::ops::Deref for Symbol {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl FromIterator<char> for Symbol {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        Symbol::intern(iter.into_iter().collect::<String>())
    }
}

impl From<&str> for Symbol {
    #[inline]
    fn from(s: &str) -> Self {
        Self::for_str(s)
    }
}

impl PartialEq<&Symbol> for Symbol {
    fn eq(&self, other: &&Symbol) -> bool {
        self.0 == other.0
    }
}

impl PartialEq<Symbol> for &Symbol {
    fn eq(&self, other: &Symbol) -> bool {
        self.0 == other.0
    }
}

impl PartialEq<str> for Symbol {
    fn eq(&self, other: &str) -> bool {
        self.cmp_str(other)
    }
}

impl PartialEq<str> for &Symbol {
    fn eq(&self, other: &str) -> bool {
        self.cmp_str(other)
    }
}

impl PartialEq<Symbol> for str {
    fn eq(&self, other: &Symbol) -> bool {
        self == other.as_str()
    }
}

impl PartialEq<&Symbol> for str {
    fn eq(&self, other: &&Symbol) -> bool {
        self == other.as_str()
    }
}

impl PartialEq<String> for Symbol {
    fn eq(&self, other: &String) -> bool {
        lookup(*self).eq(other)
    }
}

impl PartialEq<Box<str>> for Symbol {
    fn eq(&self, other: &Box<str>) -> bool {
        (&*lookup(*self)).eq(other.as_ref())
    }
}

/// If a given type *always* contains a single `Symbol`, i.e., if a type conveys
/// "labeling" or has a semantic notion of a "name" stemming from textual data
/// -- __and__ has had such data *interned* -- then the way to retrieve that
/// identifying `Symbol` is via this trait.
///
/// In particular, the `Symbol` type corresponds to the *keys* the string
/// interner uses to disambiguate stored string slices. Types encoding
/// *identifiers*, for example, generally only have a single corresponding
/// `Symbol`, which may easily be retrieved via the `Symbolic::get_symbol`
/// method.
pub trait Symbolic {
    fn get_symbol(&self) -> Symbol;
}

impl Symbolic for Symbol {
    fn get_symbol(&self) -> Symbol {
        *self
    }
}

impl Symbolic for str {
    fn get_symbol(&self) -> Symbol {
        Symbol::for_str(self)
    }
}

impl Symbolic for &str {
    fn get_symbol(&self) -> Symbol {
        Symbol::for_str(*self)
    }
}

impl Symbolic for String {
    fn get_symbol(&self) -> Symbol {
        Symbol::for_str(self.as_str())
    }
}

impl Symbolic for std::borrow::Cow<'_, str> {
    fn get_symbol(&self) -> Symbol {
        Symbol::for_str(self.as_ref())
    }
}

impl Symbolic for std::path::Path {
    fn get_symbol(&self) -> Symbol {
        Symbol::for_str(self.to_string_lossy().as_ref())
    }
}

impl Symbolic for char {
    fn get_symbol(&self) -> Symbol {
        Symbol::from_char(*self)
    }
}

pub fn intern_once<S: AsRef<str>>(s: S) -> Symbol {
    Symbol::intern(s)
}

pub fn intern_many<S: AsRef<str>, const N: usize>(strings: [S; N]) -> [Symbol; N] {
    Symbol::intern_many(strings)
}

pub fn intern_many_with<S: AsRef<str>, I, const N: usize>(
    strings: [S; N],
    f: impl FnMut(Symbol) -> I,
) -> [I; N] {
    Symbol::intern_many_with(strings, f)
}

pub fn lookup<S: Symbolic>(sym: S) -> String {
    Symbol::lookup(&sym.get_symbol())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_intern_once() {
        let word = "hello";
        let sym = intern_once(word);
        println!("{} : {}", word, sym);
    }

    #[test]
    fn test_parallel() {
        use std::thread;

        let [hi, bye] = intern_many(["hi", "bye"]);
        let [bye2, hi2, blue] = thread::spawn(move || intern_many(["bye", "hi", "blue"]))
            .join()
            .unwrap();
        let blue2 = intern_once("blue");
        for (x, y) in [(hi, hi2), (bye, bye2), (blue2, blue)] {
            assert_eq!(x, y)
        }

        let hello = Symbol::intern("hello");
        let hello_ = hello.as_str();
        assert_eq!(hello_, "hello")
    }
}
