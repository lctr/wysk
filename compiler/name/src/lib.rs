use std::sync::{Arc, Mutex};

use module::ModuleId;
use serde::{Deserialize, Serialize};
use wy_common::{iter::Counter, Mappable};

pub mod ident;
pub mod module;

use ident::{Chain, Ident};

use crate::ident::Identifier;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Unique(usize);

impl Unique {
    pub fn display(&self) -> String {
        if let Some(chain) = lookup_chain(*self) {
            chain.to_string()
        } else {
            String::new()
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
        if let Some(chain) = lookup_chain(*self) {
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
pub struct Cache<T>(Vec<Chain<T>>);

impl<T> Cache<T> {
    pub const fn new() -> Self {
        Cache(vec![])
    }

    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, Chain<T>> {
        self.0.iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, Chain<T>> {
        self.0.iter_mut()
    }

    #[inline]
    pub fn find(&self, f: impl FnMut(&&Chain<T>) -> bool) -> Option<&Chain<T>> {
        self.iter().find(f)
    }

    #[inline]
    pub fn position(&self, f: impl FnMut(&Chain<T>) -> bool) -> Option<Unique> {
        self.iter().position(f).map(Unique)
    }

    #[inline]
    pub fn filter<'a>(
        &'a self,
        f: impl FnMut(&&Chain<T>) -> bool,
    ) -> impl Iterator<Item = &'a Chain<T>> {
        self.iter().filter(f)
    }

    pub fn get(&self, unique: Unique) -> Option<&Chain<T>> {
        self.0.get(unique.0)
    }

    pub fn push(&mut self, chain: Chain<T>) -> Unique
    where
        T: PartialEq,
    {
        if let Some(u) = self.position(|ch| ch == &chain) {
            u
        } else {
            let u = Unique(self.0.len());
            self.0.push(chain);
            u
        }
    }
}

impl<T> std::ops::Deref for Cache<T> {
    type Target = Vec<Chain<T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> std::ops::DerefMut for Cache<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl std::ops::Index<Unique> for Cache<Ident> {
    type Output = Chain<Ident>;

    fn index(&self, index: Unique) -> &Self::Output {
        &self.0[index.0]
    }
}

lazy_static::lazy_static! {
    static ref CHAINS: Arc<Mutex<Cache<Ident>>> =
        Arc::new(Mutex::new(Cache(Vec::new())));
}

pub fn lookup_chain(unique: Unique) -> Option<Chain<Ident>> {
    match CHAINS.lock() {
        Ok(guard) => guard.get(unique).cloned(),
        Err(err) => {
            eprintln!(
                "Poison error while looking up chain in position `{}`",
                unique.0
            );
            panic!("{}", err)
        }
    }
}

pub fn intern_chain(chain: Chain<Ident>) -> Unique {
    match CHAINS.lock() {
        Ok(mut guard) => guard.push(chain),
        Err(err) => {
            eprintln!("Poison error while interning chain `{}`", &chain);
            panic!("{}", err)
        }
    }
}

pub fn intern_chains(
    chains: impl IntoIterator<Item = Chain<Ident>>,
) -> impl Iterator<Item = Unique> {
    match CHAINS.lock() {
        Ok(mut guard) => chains.into_iter().map(move |chain| guard.push(chain)),
        Err(err) => {
            let chs = chains
                .into_iter()
                .map(|ch| ch.map(|id| id.map_symbol(|s| s.as_u32())))
                .collect::<Vec<_>>();
            eprintln!("Poison error while interning chains `{chs:?}`");
            panic!("{}", err)
        }
    }
}

pub fn intern_many_chains<const N: usize>(chains: [Chain<Ident>; N]) -> [Unique; N] {
    match CHAINS.lock() {
        Ok(mut guard) => chains.fmap(move |chain| guard.push(chain)),
        Err(err) => {
            let chs = chains
                .into_iter()
                .map(|ch| ch.map(|id| id.map_symbol(|s| s.as_u32())))
                .collect::<Vec<_>>();
            eprintln!("Poison error while interning chains `{chs:?}`");
            panic!("{}", err)
        }
    }
}

impl Chain<Ident> {
    pub fn intern(chain: Self) -> Unique {
        intern_chain(chain)
    }

    pub fn intern_chains(
        chains: impl IntoIterator<Item = Chain<Ident>>,
    ) -> impl Iterator<Item = Unique> {
        intern_chains(chains)
    }

    pub fn lookup_chain(unique: Unique) -> Option<Chain<Ident>> {
        lookup_chain(unique)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct NameState(Counter);

impl NameState {
    pub fn new() -> Self {
        NameState::default()
    }

    pub fn with_offset(n: usize) -> Self {
        NameState(Counter::new_from(n))
    }

    pub fn from_counter(counter: Counter) -> Self {
        NameState(counter)
    }

    pub fn increment(&mut self) -> usize {
        self.0.increment()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Name {
    modid: ModuleId,
    ident: Ident,
    unique: Unique,
}

impl Name {
    pub fn new(modid: ModuleId, ident: Ident, unique: Unique) -> Self {
        Self {
            modid,
            ident,
            unique,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_chains() {
        let [prelude, function] =
            wy_intern::intern_many_with(["Prelude", "Function"], Ident::Upper);
        let [curry, uncurry] = wy_intern::intern_many_with(["curry", "uncurry"], Ident::Lower);

        let curry_chain = Chain::from((prelude, [function, curry]));
        let uncurry_chain = Chain::from((prelude, [function, uncurry]));
        let [uid0, uid1] = intern_many_chains([curry_chain, uncurry_chain]);
        assert_eq!(uid0.display(), "Prelude.Function.curry");
        assert_eq!(uid1.display(), "Prelude.Function.uncurry");
    }
}
