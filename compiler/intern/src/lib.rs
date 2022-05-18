pub mod symbol;

pub use symbol::*;

pub mod sym {
    use super::{intern_many, Symbol};

    lazy_static::lazy_static! {
        pub static ref PRIM_TY_NAMES: [Symbol; 9] = intern_many([
            "Bool",
            "Byte",
            "Int",
            "Nat",
            "Float",
            "Double",
            "Char",
            "Str",
            "IO"
        ]);
    }
}
