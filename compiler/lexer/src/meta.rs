use serde::{Deserialize, Serialize};
use wy_common::strenum;
use wy_intern::Symbol;

strenum! { Attr is_builtin_attr ::
    Inline "inline"
    NoInline "noinline" | "no_inline"
    Fixity "fixity" | "infix"
    Derive "derive"
    Allow "allow"
    Test "test"
    Todo "todo"
    Specialize "specialize" | "specialise"
    Feature "feature" | "feat"
    Cfg "cfg"
    Macro "macro"
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Pragma {
    BuiltIn(Attr),
    Custom(Symbol),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Placement {
    /// Indicates that the relative position of an attribute or compiler
    /// pragma is *before* the item that it annotates.
    Before,
    /// Indicates that the relative position of an attribute or
    /// compiler pragma is *after* the item that it annotates.
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
