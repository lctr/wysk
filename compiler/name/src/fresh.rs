use std::fmt;

use serde::{Deserialize, Serialize};
use wy_intern::Symbol;

/// Represents a transient variable: an identifier highly likely to
/// change in an effort to escape name capture..
///
/// TODO: (for display/printing aesthetics) reserve `Tv(6)` and
/// `Tv(13)` for `f` and `m`, respectively for transient/type
/// variables in constructor position??? Or put off into a separate
/// type in a later phase.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize)]
pub struct Tv(pub u32);

impl Tv {
    pub fn as_u32(&self) -> u32 {
        self.0
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }

    pub fn as_u64(&self) -> u64 {
        self.0 as u64
    }

    pub fn display(&self) -> String {
        wy_common::text::display_var(self.0)
    }

    pub fn from_symbol(sym: Symbol) -> Self {
        Tv(sym.as_u32())
    }

    pub fn as_symbol(&self) -> Symbol {
        Symbol::intern(self.display())
    }

    // If a character is an ASCII lowercase character, i.e., in the
    // range U+0061 'a' ..= U+007A 'z', then directly creates the
    // corresponding `Tv` instance. Otherwise it will interpret the
    // character byte as a regular usize/u32 generated Tv.
    pub fn from_ascii_lowercase(c: char) -> Tv {
        if c.is_ascii_lowercase() {
            Tv((c as u8 - 0x61) as u32)
        } else {
            Tv(c as u8 as u32)
        }
    }

    pub fn write_str(&self, buf: &mut String) {
        wy_common::text::write_display_var(self.0 as usize, buf)
    }
}

impl From<Tv> for usize {
    fn from(tv: Tv) -> Self {
        tv.0 as usize
    }
}

impl fmt::Debug for Tv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Tv({})", self.0)
    }
}

impl fmt::Display for Tv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display())
    }
}
