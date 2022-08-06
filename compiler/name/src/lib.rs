use module::ModuleId;
use serde::{Deserialize, Serialize};
use wy_common::iter::Counter;

pub mod chain;
pub mod ident;
pub mod module;
pub mod unique;

pub use chain::Chain;
pub use ident::{Ident, Identifier};
pub use unique::Unique;

impl Ident {
    pub fn with_suffix(self, suffix: Self) -> Chain<Self> {
        Chain::new(self, wy_common::deque!(suffix))
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

    pub fn get_module_id(&self) -> &ModuleId {
        &self.modid
    }

    pub fn get_ident(&self) -> &Ident {
        &self.ident
    }

    pub fn get_unique(&self) -> &Unique {
        &self.unique
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
        let [uid0, uid1] = unique::Unique::intern_many_chains([curry_chain, uncurry_chain]);
        assert_eq!(uid0.display(), "Prelude.Function.curry");
        assert_eq!(uid1.display(), "Prelude.Function.uncurry");
    }
}
