pub mod symbol;

pub use symbol::*;

use wy_span::{Located, Positioned, Spanned};

impl<S> Symbolic for Spanned<S>
where
    S: Symbolic,
{
    fn get_symbol(&self) -> Symbol {
        self.item().get_symbol()
    }
}
impl<S> Symbolic for Positioned<S>
where
    S: Symbolic,
{
    fn get_symbol(&self) -> Symbol {
        self.item().get_symbol()
    }
}
impl<S> Symbolic for Located<S>
where
    S: Symbolic,
{
    fn get_symbol(&self) -> Symbol {
        self.item().get_symbol()
    }
}
