use serde::{Deserialize, Serialize};
use std::sync::{Arc, Mutex};
use wy_common::poison_error;
// use wy_common::Mappable;

use crate::{
    chain::Chain,
    ident::{Ident, Identifier},
};

/// A `Unique` represents a pointer to globally cached `Chain` instance
/// representing a qualified identifier.
///
/// Like `Symbol`, instances of this type cannot be manually
/// constructed, and are only created by the *single* lazy static
/// `Cache` instance for `Chain<Ident>`s.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Unique(usize);

impl Unique {
    pub fn display(&self) -> String {
        if let Some(chain) = lookup_chain(self) {
            chain.to_string()
        } else {
            String::new()
        }
    }

    /// Shortcut for interning an identifier chain
    #[inline]
    pub fn from_chain(chain: Chain<Ident>) -> Self {
        intern_chain(chain)
    }

    pub fn intern(chain: Chain<Ident>) -> Unique {
        intern_chain(chain)
    }

    pub fn intern_chains(
        chains: impl IntoIterator<Item = Chain<Ident>>,
    ) -> impl Iterator<Item = Unique> {
        intern_chains(chains)
    }

    pub fn lookup_chain(unique: &Unique) -> Option<Chain<Ident>> {
        lookup_chain(unique)
    }

    pub fn from_unique(unique: &Unique) -> Chain<Ident> {
        match CHAINS.lock() {
            Ok(guard) => guard.get_unchecked(unique).clone(),
            Err(err) => poison_error!(err, "getting chain in with `Unique`", &unique.0),
        }
    }

    pub fn map_from_unique(unique: &Unique, f: impl FnOnce(&Chain<Ident>)) {
        match CHAINS.lock() {
            Ok(guard) => {
                f(guard.get_unchecked(unique));
            }
            Err(err) => poison_error!(err, "mapping chain in `Unique`", &unique.0),
        }
    }

    pub fn intern_many_chains<const N: usize>(chains: [Chain<Ident>; N]) -> [Unique; N] {
        match CHAINS.lock() {
            Ok(mut guard) => {
                let mut uns = [Unique(0); N];
                let mut i = 0;
                for chain in chains {
                    uns[i] = guard.push(chain);
                    i += 1;
                }
                // chains.fmap(move |chain| guard.push(chain))
                uns
            }
            Err(err) => {
                poison_error!(
                    #error = err;
                    #msg = "interning chains";
                    #query = chains
                        .into_iter()
                        .map(|ch| ch.map(|id| id.map_symbol(|s| s.as_u32())))
                        .collect::<Vec<_>>()
                )
            }
        }
    }

    /// Instead of returning the reference itself, a continuation is
    /// provided the argument of which will be the result of the
    /// global chain lookup.
    ///
    /// Note that since this is a lookup based on `Chain`s and not
    /// `Unique`s, it's possible for the chain itself to not exist!
    pub fn find_chain(
        f: impl FnMut(&&Chain<Ident>) -> bool,
        cont: impl FnOnce(Option<&Chain<Ident>>),
    ) {
        match CHAINS.lock() {
            Ok(guard) => cont(guard.find(f)),
            Err(err) => poison_error!(err, "finding cached chain with continuation"),
        }
    }

    pub fn find_chains_ending_with(id: &Ident) -> Vec<Chain> {
        match CHAINS.lock() {
            Ok(guard) => guard.filter(|ch| ch.ends_with(id)).cloned().collect(),
            Err(err) => poison_error!(err, "finding chains ending with", &id),
        }
    }

    pub fn find_chains_starting_with(id: &Ident) -> Vec<Chain> {
        match CHAINS.lock() {
            Ok(guard) => guard.filter(|ch| ch.starts_with(id)).cloned().collect(),
            Err(err) => poison_error!(err, "finding chains starting with", &id),
        }
    }
}

impl std::fmt::Debug for Unique {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Unique({})", &self.0)
    }
}

impl std::fmt::Display for Unique {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(chain) = lookup_chain(self) {
            write!(f, "{}", chain)
        } else {
            write!(f, "Unique({})", self.0)
        }
    }
}

/// Interned identifier chains. Instead of collapsing a `Chain<Ident>` into a
/// single `Symbol` by concatenating idents, we store the chains in a separate
/// global static structure. This way, we can use simple pointer equality for
/// identifier chains composed of identifiers, as well as preserve the
/// identifiers comprising the chain. If we were to "collapse" multiple
/// identifiers into a single one -- i.e., join identifiers `A`, `B`, `c` into
/// the string `A.B.c` and interning it -- we would have to separate joined the
/// string into its components and look each up to get the corresponding
/// symbols.  
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Cache {
    buf: Vec<Chain<Ident>>,
}

impl Cache {
    #[inline]
    fn iter(&self) -> std::slice::Iter<'_, Chain<Ident>> {
        self.buf.iter()
    }

    #[inline]
    fn find(&self, f: impl FnMut(&&Chain<Ident>) -> bool) -> Option<&Chain<Ident>> {
        self.iter().find(f)
    }

    #[inline]
    fn position(&self, f: impl FnMut(&Chain<Ident>) -> bool) -> Option<Unique> {
        self.iter().position(f).map(Unique)
    }

    #[inline]
    fn filter<'a>(
        &'a self,
        f: impl FnMut(&&Chain<Ident>) -> bool,
    ) -> impl Iterator<Item = &'a Chain<Ident>> {
        self.iter().filter(f)
    }

    fn get(&self, unique: &Unique) -> Option<&Chain<Ident>> {
        self.buf.get(unique.0)
    }

    fn get_unchecked(&self, unique: &Unique) -> &Chain<Ident> {
        &self[unique]
    }

    fn push(&mut self, chain: Chain<Ident>) -> Unique {
        if let Some(u) = self.position(|ch| ch == &chain) {
            u
        } else {
            let u = Unique(self.buf.len());
            self.buf.push(chain);
            u
        }
    }
}

impl std::ops::Index<Unique> for Cache {
    type Output = Chain<Ident>;

    fn index(&self, index: Unique) -> &Self::Output {
        &self.buf[index.0]
    }
}

impl std::ops::Index<&Unique> for Cache {
    type Output = Chain<Ident>;

    fn index(&self, index: &Unique) -> &Self::Output {
        &self.buf[index.0]
    }
}

lazy_static::lazy_static! {
    static ref CHAINS: Arc<Mutex<Cache>> =
        Arc::new(Mutex::new(Cache { buf: Vec::new() }));
}

fn lookup_chain(unique: &Unique) -> Option<Chain<Ident>> {
    match CHAINS.lock() {
        Ok(guard) => guard.get(unique).cloned(),
        Err(err) => poison_error!(
            #error = err;
            #msg = "looking up chain in position";
            #query = &unique.0
        ),
    }
}

fn intern_chain(chain: Chain<Ident>) -> Unique {
    match CHAINS.lock() {
        Ok(mut guard) => guard.push(chain),
        Err(err) => poison_error!(
            #error = err;
            #msg = "interning chain";
            #query = chain
        ),
    }
}

fn intern_chains(chains: impl IntoIterator<Item = Chain<Ident>>) -> impl Iterator<Item = Unique> {
    match CHAINS.lock() {
        Ok(mut guard) => chains.into_iter().map(move |chain| guard.push(chain)),
        Err(err) => {
            let chs = chains
                .into_iter()
                .map(|ch| ch.map(|id| id.map_symbol(|s| s.as_u32())))
                .collect::<Vec<_>>();
            poison_error!(#error = err; #msg = "interning chains"; #query = chs)
        }
    }
}
