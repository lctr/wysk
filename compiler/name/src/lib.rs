use std::sync::{Arc, Mutex};

use module::ModuleId;
use wy_common::Mappable;

pub mod ident;
pub mod module;

use ident::{Chain, Ident};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl std::fmt::Display for Unique {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(chain) = lookup_chain(*self) {
            write!(f, "{}", chain)
        } else {
            write!(f, "Unique({})", self.0)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
        self.iter().position(f).map(|idx| Unique(idx))
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
            eprintln!(
                "Poison error while interning chains `{}`",
                wy_common::pretty::List(&chains.into_iter().collect::<Vec<_>>()[..])
            );
            panic!("{}", err)
        }
    }
}

pub fn intern_many_chains<const N: usize>(chains: [Chain<Ident>; N]) -> [Unique; N] {
    match CHAINS.lock() {
        Ok(mut guard) => chains.fmap(move |chain| guard.push(chain)),
        Err(err) => {
            eprintln!(
                "Poison error while interning chains `{}`",
                wy_common::pretty::List(&chains.into_iter().collect::<Vec<_>>()[..])
            );
            panic!("{}", err)
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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
