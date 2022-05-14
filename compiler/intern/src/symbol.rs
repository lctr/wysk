use std::collections::HashMap;
use std::mem;
use std::sync::{Arc, Mutex};

/// Key used to reference stored strings. When a string is interened, a
/// `Symbol` is returned, which can then be used to retrieve the original
/// string representation. This helps reduce the footprint of data structures
/// containing *immutable* strings like variable names, string literals, etc.
#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
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
    pub fn pure<X, F>(self, f: F) -> X
    where
        F: Fn(Self) -> X,
    {
        f(self)
    }

    pub fn display(self) -> String {
        lookup(self)
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

impl From<Symbol> for usize {
    fn from(Symbol(i): Symbol) -> Self {
        i as usize
    }
}

/// String interner. Instead of allocating a new string during the compilation
/// process, all strings are instead interned and mapped to instances of type
/// `Symbol`, which unlike `&str` and `String`, are [`Copy`] and additionally
/// more lightweight.
#[derive(Clone, Debug)]
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
        self.vec[id.as_u32() as usize]
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

pub fn lookup<S: Symbolic>(sym: S) -> String {
    match INTERNER.lock() {
        Ok(guard) => guard.lookup(sym.get_symbol()).to_string(),
        Err(e) => {
            eprintln!("{}", e);
            panic!("poisoned while looking up symbol `{:?}`", sym.get_symbol())
        }
    }
}

pub fn lookup_many<S: Symbolic>(syms: &[S]) -> Vec<String> {
    match INTERNER.lock() {
        Ok(guard) => syms
            .into_iter()
            .map(|s| guard.lookup(s.get_symbol()).to_string())
            .collect(),
        Err(e) => {
            eprintln!("{}", e);
            panic!(
                "poisoned while looking up symbols `{:?}`",
                syms.iter().map(|s| s.get_symbol()).collect::<Vec<_>>()
            )
        }
    }
}

lazy_static::lazy_static! {
    static ref INTERNER: Arc<Mutex<Lexicon>> = Arc::new(Mutex::new(Lexicon::default()));

    pub static ref CONS: Symbol = intern_once(":");
    pub static ref MINUS: Symbol = intern_once("-");
    pub static ref ARROW: Symbol = intern_once("->");
}

// Instantiating a thread local string interner
#[macro_export]
macro_rules! local_lexicon {
    ($name:ident) => {
        thread_local! {
            /// A single global (thread local) handle to a single Lexicon.
            ///
            /// Since this `Lexicon` is wrapped within a `RefCell`, accessing
            /// it *must* be done through the provided utility_functions in
            /// order to ensure borrowing is limited in scope.
            static $name: RefCell<Lexicon> = RefCell::new(Lexicon::default())
        }

        /// Intern a string slice with the thread local `LEXICON` interner.
        /// Returns the corresponding `Symbol` key.
        /// Equivalent to calling `intern` on `&mut Lexicon`.
        pub fn intern_once(string: &str) -> Symbol {
            $name.with(|lexicon| lexicon.borrow_mut().intern(string))
        }

        pub fn intern_many<'t>(strings: &'t [&'t str]) -> Vec<(&'t str, Symbol)> {
            $name.with(|lexicon| {
                let mut lex = lexicon.borrow_mut();
                strings
                    .iter()
                    .map(|s| (*s, lex.intern(*s)))
                    .collect::<Vec<_>>()
            })
        }

        /// Given some element `sym` that implements the `Symbolic` trait,
        /// immutably borrows the thread local `Lexicon` to lookup the `&str`
        /// corresponding to the given `sym`. Since we cannot return anything
        /// with the same lifetime (as references must live beyond the
        /// immutable borrow, which they cannot), the resulting `&str` is
        /// converted into an owned `String` and returned.
        pub fn lookup_once(sym: impl Symbolic) -> String {
            $name.with(|lexicon| lexicon.borrow().lookup(sym.get_symbol()).into())
        }

        /// Given a slice of elements of type `S` where `S` implements the
        /// trait `Symbolic`, returns a vector of `(Symbol, String)` pairs.
        ///
        /// It is better to use this function over calling `lookup_once`
        /// multiple times, as multiple lookups are performed within a single
        /// immutable borrowing of `Lexicon`, while repeated calls to
        /// `lookup_once` would repeatedly borrow `Lexicon` immutably
        /// multiple times within separate scopes.
        pub fn lookup_many<S: Symbolic>(syms: &[S]) -> Vec<(Symbol, String)> {
            $name.with(|lexicon| {
                let lex = lexicon.borrow();
                syms.iter()
                    .map(|s| s.get_symbol())
                    .map(|s| (s, lex.lookup(s).to_string()))
                    .collect::<Vec<_>>()
            })
        }
    };
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
        let [hi2, bye2, blue] = thread::spawn(move || intern_many(["hi", "bye", "blue"]))
            .join()
            .unwrap();
        let blue2 = intern_once("blue");
        assert_eq!([hi, bye, blue2], [hi2, bye2, blue])
    }
}
