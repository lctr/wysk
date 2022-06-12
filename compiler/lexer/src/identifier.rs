use wy_common::newtype;
use wy_intern::symbol::{Symbol, Symbolic};

newtype! {
    u64 in VarId | New Show AsUsize (+) (-) (+= usize |rhs| rhs as u64) (+= u32 |rhs| rhs as u64)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Shape {
    /// Text beginning with an uppercase alphabetic character
    Upper,
    /// Text beginning with a lowercase alphabetic character
    Lower,
    /// Text consisting of operator characters.
    Affix,
    /// Text beginning with an apostrophe
    Label,
    /// Text beginning with an underscore
    Under,
    /// Text generated internally
    Unique,
    /// Text consisting of multiple sub-identifiers. For example, an identifier
    /// `Foo.bar.baz` is an `Access` identifier.
    Access,
}

wy_common::variant_preds! { Shape
    | is_upper => Upper
    | is_lower => Lower [| Self::Under]
    | is_affix => Affix
    | is_label => Label
    | is_under => Under
    | is_simple => Unique
    | is_access => Access
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Identifier {
    /// What kind of identifier
    shape: Shape,
    /// Interned string symbol
    idsym: Symbol,
    /// Pointer to the position in which this identifier was found
    varid: VarId,
}

impl Identifier {
    pub fn shape(&self) -> Shape {
        self.shape
    }

    pub fn var_id(&self) -> VarId {
        self.varid
    }

    pub fn sym_eq(&self, other: Symbol) -> bool {
        self.idsym == other
    }

    pub fn shape_eq(&self, other: Shape) -> bool {
        self.shape == other
    }
}

impl Symbolic for Identifier {
    fn get_symbol(&self) -> Symbol {
        self.idsym
    }
}
