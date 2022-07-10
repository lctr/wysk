use std::collections::HashMap;
use std::mem;
use std::sync::{Arc, Mutex};

use serde::{Deserialize, Serialize};
use wy_common::Mappable;

/// Key used to reference stored strings. When a string is interened, a
/// `Symbol` is returned, which can then be used to retrieve the original
/// string representation. This helps reduce the footprint of data structures
/// containing *immutable* strings like variable names, string literals, etc.
///
/// NOTE: These CANNOT be directly instantiated, and in fact may only be created
/// by the global interner as a result of interning strings.
#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Symbol(u32);

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display())
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

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }

    /// Equivalent to simply calling a closure with this as that closure's
    /// argument.
    #[inline]
    pub fn pure<X, F>(self, mut f: F) -> X
    where
        F: FnMut(Self) -> X,
    {
        f(self)
    }

    #[inline]
    pub fn display(self) -> String {
        lookup(self)
    }

    pub fn write_str(&self, buf: &mut String) {
        buf.push_str(self.as_str())
    }

    pub fn from_char(c: char) -> Symbol {
        if c == ':' {
            *reserved::COLON
        } else {
            intern_once(&*c.to_string())
        }
    }

    #[inline]
    pub fn from_str(s: &str) -> Symbol {
        intern_once(s)
    }

    pub fn cmp_str(&self, s: impl std::ops::Deref<Target = str>) -> bool {
        &*lookup(*self) == &*s
    }

    #[inline]
    pub fn intern<S: AsRef<str>>(s: S) -> Symbol {
        intern_once(s.as_ref())
    }

    pub fn as_str(&self) -> &str {
        let guard = INTERNER.lock().unwrap();
        // Safety: we are extending the lifetime of the string, however since it
        // is interned with a `'static` lifetime, the data pointed to should
        // always be valid. CONFIRM!
        unsafe { std::mem::transmute::<_, &str>(guard.lookup(*self)) }
    }

    #[inline]
    pub fn from_str_deref<S: std::ops::Deref<Target = str>>(s: S) -> Self {
        intern_once(&*s)
    }

    pub fn from_utf8(bytes: &[u8]) -> Result<Self, std::str::Utf8Error> {
        std::str::from_utf8(bytes).map(Self::from_str)
    }

    pub unsafe fn from_utf8_unchecked(bytes: &[u8]) -> Self {
        Self::from_str(std::str::from_utf8_unchecked(bytes))
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

impl From<&str> for Symbol {
    #[inline]
    fn from(s: &str) -> Self {
        Self::from_str(s)
    }
}

impl PartialEq<str> for Symbol {
    fn eq(&self, other: &str) -> bool {
        self.cmp_str(other)
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
        Symbol::from_str(&self)
    }
}

impl Symbolic for &str {
    fn get_symbol(&self) -> Symbol {
        Symbol::from_str(*self)
    }
}

impl Symbolic for String {
    fn get_symbol(&self) -> Symbol {
        Symbol::from_str(self.as_str())
    }
}

impl Symbolic for std::borrow::Cow<'_, str> {
    fn get_symbol(&self) -> Symbol {
        Symbol::from_str(self.as_ref())
    }
}

impl Symbolic for std::path::Path {
    fn get_symbol(&self) -> Symbol {
        Symbol::from_str(self.to_string_lossy().as_ref())
    }
}

impl Symbolic for char {
    fn get_symbol(&self) -> Symbol {
        Symbol::from_char(*self)
    }
}

impl Symbolic for (&str, char, [&str]) {
    fn get_symbol(&self) -> Symbol {
        let mut buf = String::new();
        let (a, b, cs) = self;
        buf.push_str(*a);
        for c in cs {
            buf.push(*b);
            buf.push_str(*c);
        }
        Symbol::from_str(buf.as_str())
    }
}

impl From<Symbol> for u32 {
    fn from(Symbol(i): Symbol) -> Self {
        i
    }
}

impl From<Symbol> for usize {
    fn from(Symbol(i): Symbol) -> Self {
        i as usize
    }
}

/// String interner. Instead of allocating a new string during the compilation
/// process, all strings are instead interned and mapped to instances of type
/// `Symbol`, which unlike `&str` and `String`, are [`Copy`] and additionally
/// more lightweight.
#[derive(Debug)]
struct Lexicon {
    map: HashMap<&'static str, Symbol>,
    vec: Vec<&'static str>,
    buf: String,
    all: Vec<String>,
}

impl Lexicon {
    /// Initial value just randomly guessed.
    /// This could/should maybe be optimized later.
    pub const BASE_CAPACITY: usize = 100;

    pub fn with_capacity(cap: usize) -> Self {
        let cap = cap.next_power_of_two();
        Self {
            map: HashMap::default(),
            vec: Vec::new(),
            buf: String::with_capacity(cap),
            all: Vec::new(),
        }
    }

    fn with_reserved<const N: usize>(strings: [&str; N]) -> Self {
        let mut this = Self::default();
        for s in strings {
            this.intern(s);
        }
        this
    }

    pub fn intern(&mut self, string: &str) -> Symbol {
        if let Some(&id) = self.map.get(string) {
            return id;
        }

        let string = unsafe { self.alloc(string) };
        let id = Symbol(self.map.len() as u32);

        self.map.insert(string, id);
        self.vec.push(string);

        debug_assert!(self.lookup(id) == string);
        debug_assert!(self.intern(string) == id);

        id
    }

    pub fn lookup(&self, id: Symbol) -> &str {
        self.vec[id.0 as usize]
    }

    unsafe fn alloc(&mut self, string: &str) -> &'static str {
        let cap = self.buf.capacity();
        if cap < self.buf.len() + string.len() {
            // just doubling isn't enough -- need to ensure the new string
            // actually fits
            let new_cap = (cap.max(string.len()) + 1).next_power_of_two();
            let new_buf = String::with_capacity(new_cap);
            let old_buf = mem::replace(&mut self.buf, new_buf);
            self.all.push(old_buf);
        }

        let interned = {
            let start = self.buf.len();
            self.buf.push_str(string);
            &self.buf[start..]
        };

        &*(interned as *const str)
    }

    pub fn capacity(&self) -> usize {
        #![allow(unused)]
        self.buf.capacity()
    }
}

impl Default for Lexicon {
    fn default() -> Self {
        Self::with_capacity(Self::BASE_CAPACITY)
    }
}

impl<S: Symbolic> std::ops::Index<S> for Lexicon {
    type Output = str;

    fn index(&self, index: S) -> &Self::Output {
        self.lookup(index.get_symbol())
    }
}

pub fn intern_once<S: AsRef<str>>(s: S) -> Symbol {
    match INTERNER.lock() {
        Ok(mut guard) => guard.intern(s.as_ref()),
        Err(poisoned) => {
            eprintln!("{}", poisoned);
            panic!("poisoned while interning `{}`", s.as_ref())
        }
    }
}

pub fn intern_all<S: AsRef<str>>(strings: impl Iterator<Item = S>) -> impl Iterator<Item = Symbol> {
    match INTERNER.lock() {
        Ok(mut guard) => strings.map(move |s| guard.intern(s.as_ref())),
        Err(e) => {
            eprintln!("{}", e);
            panic!(
                "poisoned while interning `{}`",
                &strings
                    .map(|s| s.as_ref().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    }
}

pub fn intern_many<S: AsRef<str>, const N: usize>(strings: [S; N]) -> [Symbol; N] {
    match INTERNER.lock() {
        Ok(mut guard) => {
            let mut syms = [Symbol(0); N];
            for (i, s) in strings.into_iter().enumerate() {
                syms[i] = guard.intern(s.as_ref());
            }
            syms
        }
        Err(e) => {
            eprintln!("{}", e);
            panic!(
                "poisoned while interning `{:?}`",
                &strings.iter().map(|s| s.as_ref()).collect::<Vec<_>>()
            )
        }
    }
}

pub fn intern_many_with<S: AsRef<str>, I, const N: usize>(
    strings: [S; N],
    mut f: impl FnMut(Symbol) -> I,
) -> [I; N] {
    match INTERNER.lock() {
        Ok(mut guard) => strings.fmap(|s| f(guard.intern(s.as_ref()))),
        Err(e) => {
            eprintln!("{}", e);
            panic!(
                "poisoned while interning `{:?}`",
                &strings.iter().map(|s| s.as_ref()).collect::<Vec<_>>()
            )
        }
    }
}

pub fn lookup<S: Symbolic>(sym: S) -> String {
    match INTERNER.lock() {
        Ok(guard) => guard.lookup(sym.get_symbol()).to_string(),
        Err(e) => {
            eprintln!("{}", e);
            panic!(
                "poisoned while looking up symbol `{:?}`",
                sym.get_symbol().as_u32()
            )
        }
    }
}

pub fn write_lookup<S: Symbolic>(s: S, buf: &mut String) {
    match INTERNER.lock() {
        Ok(guard) => buf.push_str(guard.lookup(s.get_symbol())),
        Err(e) => {
            eprintln!("{}", e);
            panic!("poisoned while trying to append to string buffer the result of looking up symbol `{:?}`", s.get_symbol().as_u32())
        }
    }
}

pub fn fmt_lookup<S: Symbolic>(s: S, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match INTERNER.lock() {
        Ok(guard) => {
            write!(f, "{}", guard.lookup(s.get_symbol()))
        }
        Err(e) => {
            eprintln!("{}", e);
            panic!(
                "poisoned while looking up symbol `{:?}` for formatter",
                s.get_symbol().as_u32()
            )
        }
    }
}

pub fn lookup_boxed<S: Symbolic>(sym: S) -> Box<str> {
    match INTERNER.lock() {
        Ok(guard) => guard.lookup(sym.get_symbol()).into(),
        Err(e) => {
            eprintln!("{}", e);
            panic!(
                "poisoned while looking up symbol `{:?}`",
                sym.get_symbol().as_u32()
            )
        }
    }
}

pub fn lookup_many<S: Symbolic>(syms: impl IntoIterator<Item = S>) -> Vec<String> {
    match INTERNER.lock() {
        Ok(guard) => syms
            .into_iter()
            .map(|s| guard.lookup(s.get_symbol()).to_string())
            .collect(),
        Err(e) => {
            eprintln!("{}", e);
            panic!(
                "poisoned while looking up symbols `{:?}`",
                syms.into_iter()
                    .map(|s| s.get_symbol().as_u32())
                    .collect::<Vec<_>>()
            )
        }
    }
}

macro_rules! with_reserved {
    (
        $interner_id:ident
        $(  $($(#[$com:meta])+)?
            | $idx:literal $(:)? $name:ident $lit:literal)*
    ) => {
        pub mod reserved {
            use super::{Symbol, Symbolic};

            #[derive(Copy, Clone, PartialEq, Eq, Hash)]
            pub struct Reserved { pub symbol: Symbol, text: &'static str }
            impl Reserved {
                #[inline] pub fn symbol(&self) -> Symbol { self.symbol }
                #[inline] pub fn text(&self) -> &'static str { self.text }
                #[inline] pub fn sym_eq(&self, other: impl Symbolic) -> bool {
                    self.symbol == other.get_symbol()
                }
            }

            impl std::ops::Deref for Reserved {
                type Target = Symbol;
                fn deref(&self) -> &Self::Target {
                    &self.symbol
                }
            }

            impl AsRef<Symbol> for Reserved {
                fn as_ref(&self) -> &Symbol { &self.symbol }
            }

            impl AsRef<str> for Reserved {
                fn as_ref(&self) -> &str { self.text }
            }

            // impl From<Reserved> for Symbol {
            //     fn from(reserved: Reserved) -> Symbol {
            //         reserved.symbol
            //     }
            // }

            impl From<Reserved> for &str {
                fn from(reserved: Reserved) -> &'static str {
                    reserved.text
                }
            }

            impl Symbolic for Reserved {
                #[inline] fn get_symbol(&self) -> Symbol { self.symbol }
            }

            $(
                #[allow(non_upper_case_globals)]
                #[doc = concat!("## ", stringify!($name), " ", "`", $lit, "`")]
                ///
                $($(#[$com])+)?
                pub const $name: Reserved = Reserved {
                    symbol: Symbol($idx),
                    text: $lit,
                };
            )*
        }

        $(
            pub const $name: Symbol = reserved::$name.symbol;
        )*

        lazy_static::lazy_static! {
            static ref $interner_id: Arc<Mutex<Lexicon>> =
                Arc::new(Mutex::new(Lexicon::with_reserved([
                    $($lit,)*
                ])));
        }
    };
}

with_reserved! {
    INTERNER
    | 0 EMPTY ""
    | 1 WILD "_"
    | 2 COLON ":"
    | 3 MINUS "-"
    | 4 ARROW "->"

    | 5 BOOL "Bool"
    | 6 BYTE "Byte"
    | 7 INT "Int"
    | 8 NAT "Nat"
    | 9 FLOAT "Float"
    | 10 DOUBLE "Double"
    | 11 CHAR "Char"
    | 12 STR "Str"
    | 13 IO "IO"

    | 14 MAIN_MOD "Main"
    | 15 MAIN_FUN "main"

    | 16 TRUE "True"
    | 17 FALSE "False"

    | 18 RS_U8 "U'8"
    | 19 RS_U16 "U'16"
    | 20 RS_U32 "U'32"
    | 21 RS_U64 "U'64"
    | 22 RS_U128 "U'128"
    | 23 RS_I8 "I'8"
    | 24 RS_I16 "I'16"
    | 25 RS_I32 "I'32"
    | 26 RS_I64 "I'64"
    | 27 RS_I128 "I'128"

    | 28 IT "it"
    | 29 SELF_MOD "Self"

    /// Reserved as a symbol in order since it is not strictly a keyword!
    | 30 AS "as"

    | 31 INLINE "inline"
    | 32 NO_INLINE "no_inline"
    | 33 FIXITY "fixity"

    | 34 LEFT "Left"
    | 35 RIGHT "Right"

    | 36 MAP_FN "map"
    | 37 FOLDR_FN "foldr"
    | 38 FOLDL_FN "foldl"
    | 39 LENGTH_FN "length"
    | 40 PANIC "panic"
    | 41 TODO "todo"
    | 42 UNDEFINED "undefined"

    | 43 SHOW "Show"
    | 44 EQ "Eq"
    | 45 ORD "Ord"
    | 46 NUM "Num"
    | 47 FUNCTOR "Functor"
    | 48 APPLICATIVE "Applicative"
    | 49 FOLDABLE "Foldable"
    | 50 SEMIGROUP "Semigroup"
    | 51 MONOID "Monoid"
    | 52 MONAD "Monad"
    | 53 FRACTIONAL "Fractional"

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
