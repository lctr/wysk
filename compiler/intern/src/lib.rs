#[macro_use]
mod interner;
pub mod symbol;

pub use symbol::{Symbol, Symbolic};

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

global_string_interner! {
    #with_reserved
    :handle INTERNER
    :key_type crate::symbol::Symbol
    :module sym
    :predefined
        | 0 EMPTY ""
        | 1 WILD "_"
        | 2 COLON ":"
        | 3 MINUS "-"
        | 4 STAR "*"
        | 5 AMPERSAND "&"
        | 6 PLUS "+"

        // built-in type constructors
        | 7 ARROW "->"
        | 8 PAREN_LR "()"
        | 9 BRACK_LR "[]"
        | 10 CURLY_LR "{}"

        // built-in types
        | 11 BOOL "Bool"
        | 12 BYTE "Byte"
        | 13 INT "Int"
        | 14 NAT "Nat"
        | 15 FLOAT "Float"
        | 16 DOUBLE "Double"
        | 17 CHAR "Char"
        | 18 STR "Str"
        | 19 IO "IO"

        // predefined (but not exhaustive) tuple constructors
        | 20 COMMA_1 ","
        | 21 COMMA_2 ",,"
        | 22 COMMA_3 ",,,"
        | 23 COMMA_4 ",,,,"
        | 24 COMMA_5 ",,,,,"
        | 25 COMMA_6 ",,,,,,"
        | 26 COMMA_7 ",,,,,,,"
        | 27 COMMA_8 ",,,,,,,,"
        | 28 COMMA_9 ",,,,,,,,,"
        | 29 COMMA_10 ",,,,,,,,,,,"

        //  constructors technically defined in the language but largely used
        //  the compiler
        | 30 TRUE "True"
        | 31 FALSE "False"
        | 32 NONE "None"
        | 33 SOME "Some"
        | 34 LEFT "Left"
        | 35 RIGHT "Right"
        | 36 OK "Ok"
        | 37 ERR "Err"

        // soft keywords
        | 38 AS "as"
        | 39 EXTERN "extern"
        | 40 PUB "pub"
        | 41 USE "use"
        | 42 QUALIFIED "qualified"
        | 43 HIDING "hiding"
        | 44 PACKAGE "package"
        | 45 REC "rec"

        // special identifiers
        | 46 WYSK "Wysk"
        | 47 MAIN_MOD "Main"
        | 48 MAIN_FN "main"
        | 49 PRELUDE "Prelude"
        | 50 PRIM "Prim"
        | 51 CORE "Core"

        // primitive Rust-based numeric type names
        | 52 RS_U8 "U'8"
        | 53 RS_U16 "U'16"
        | 54 RS_U32 "U'32"
        | 55 RS_U64 "U'64"
        | 56 RS_U128 "U'128"
        | 57 RS_I8 "I'8"
        | 58 RS_I16 "I'16"
        | 59 RS_I32 "I'32"
        | 60 RS_I64 "I'64"
        | 61 RS_I128 "I'128"
        | 62 RS_USIZE "Usize"
        | 63 RS_ISIZE "Isize"

        // lower level primitive names
        | 64 PRIM_ADD_NAT "prim'AddNat"
        | 65 PRIM_ADD_BYTE "prim'AddByte"
        | 66 PRIM_ADD_INT "prim'AddInt"
        | 67 PRIM_ADD_FLOAT "prim'AddFloat"
        | 68 PRIM_ADD_DOUBLE "prim'AddDouble"
        | 69 PRIM_NEGATE_INT "prim'NegateInt"
        | 70 PRIM_NEGATE_FLOAT "prim'NegateFloat"
        | 71 PRIM_NEGATE_DOUBLE "prim'NegateDouble"
        | 72 PRIM_MUL_NAT "prim'MulNat"
        | 73 PRIM_MUL_BYTE "prim'MulByte"
        | 74 PRIM_MUL_INT "prim'MulInt"
        | 75 PRIM_MUL_FLOAT "prim'MulFloat"
        | 76 PRIM_MUL_DOUBLE "prim'MulDouble"
        | 77 PRIM_SUB_NAT "prim'SubNat"
        | 78 PRIM_SUB_INT "prim'SubInt"
        | 79 PRIM_SUB_BYTE "prim'SubByte"
        | 80 PRIM_SUB_FLOAT "prim'SubFloat"
        | 81 PRIM_SUB_DOUBLE "prim'SubDouble"

        // basic digits
        | 82 DIGIT_0 "0"
        | 83 DIGIT_1 "1"
        | 84 DIGIT_2 "2"
        | 85 DIGIT_3 "3"
        | 86 DIGIT_4 "4"
        | 87 DIGIT_5 "5"
        | 88 DIGIT_6 "6"
        | 89 DIGIT_7 "7"
        | 90 DIGIT_8 "8"
        | 91 DIGIT_9 "9"

        // meta symbols
        | 92 IT "it"
        | 93 SELF "Self"
        | 94 TYPE "Type"
        | 95 CONSTRAINT "Constraint"
        | 96 KIND "Kind"

        // predefined attributes
        | 97 FIXITY "fixity"
        | 98 ASSOC_L "left"
        | 99 ASSOC_R "right"
        | 100 INLINE "inline"
        | 101 NO_INLINE "no_inline"
        | 102 SPECIALIZE "specialize"
        | 103 TEST "test"
        | 104 IGNORE "ignore"
        | 105 ALLOW "allow"
        | 106 WARN "warn"
        | 107 DOC "doc"
        | 108 EXTENSION "extension"

        // termination fns known to the compiler
        | 109 PANIC "panic"
        | 110 ERROR "error"
        | 111 UNDEFINED "undefined"

        // used in desugaring, etc; NOTE these names are NOT qualified
        | 112 MAP_LIST "mapList"
        | 113 MAP "map"
        | 114 FILTER "filter"
        | 115 FOLD_R "foldr"
        | 116 FOLD_L "foldl"
        | 117 CONCAT_MAP "concatMap"
        | 118 WRAP "wrap"
        | 119 EMBED "embed"
        | 120 AND_THEN ">>="
        | 121 SHOW_FN "show"

        // built-in class names
        | 122 EQ_CLASS "Eq"
        | 123 ORD_CLASS "Ord"
        | 124 SHOW_CLASS "Show"
        | 125 READ_CLASS "Read"
        | 126 ENUM_CLASS "Enum"
        | 127 BOUNDED_CLASS "Bounded"
        | 128 NUM_CLASS "Num"
        | 129 REAL_CLASS "Real"
        | 130 INTEGRAL_CLASS "Integral"
        | 131 FRACTIONAL_CLASS "Fractional"
        | 132 FLOATING_CLASS "Floating"
        | 133 REALFLOAT_CLASS "RealFloat"
        | 134 REALFRAC_CLASS "RealFrac"
        | 135 FUNCTOR_CLASS "Functor"
        | 136 APPLICATIVE_CLASS "Applicative"
        | 137 MONAD_CLASS "Monad"
        | 138 MONAD_PLUS_CLASS "MonadPlus"
        | 139 INDEX_CLASS "Index"
}
