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

        //  floating point numeric constants; type-specific contants contain
        //  type in the name, while the rest may be interpreted as 32-bit or
        //  based on later type inference
        | 92 EPSILON_FLOAT "1.19209290e-07"
        | 93 EPSILON_DOUBLE "2.2204460492503131e-16"
        | 94 FINITE_DIAMETER_FLOAT "3.40282347e+38"
        | 95 FINITE_DIAMETER_DOUBLE "1.7976931348623157e+308"
        | 96 MAX_FLOAT "3.40282347e+38"
        | 97 MAX_DOUBLE "1.7976931348623157e+308"
        | 98 MIN_POSITIVE_FLOAT "1.17549435e-38"
        | 99 MIN_POSITIVE_DOUBLE "2.2250738585072014e-308"
        | 100 PI "3.14159265358979323846264338327950288"
        | 101 TAU "6.28318530717958647692528676655900577"
        | 102 FRAC_PI_2 "1.57079632679489661923132169163975144"
        | 103 FRAC_PI_3 "1.04719755119659774615421446109316763"
        | 104 FRAC_PI_4 "0.785398163397448309615660845819875721"
        | 105 FRAC_PI_6 "0.52359877559829887307710723054658381"
        | 106 FRAC_PI_8 "0.39269908169872415480783042290993786"
        | 107 FRAC_1_PI "0.318309886183790671537767526745028724"
        | 108 FRAC_2_PI "0.636619772367581343075535053490057448"
        | 109 SQRT_2 "1.41421356237309504880168872420969808"
        | 110 FRAC_2_SQRT_PI "1.12837916709551257389615890312154517"
        | 111 FRAC_180_PI "57.2957795130823208767981548141051703"
        | 112 FRAC_1_SQRT_2 "0.707106781186547524400844362104849039"
        | 113 EULER "2.71828182845904523536028747135266250"
        | 114 LOG2_10 "3.32192809488736234787031942948939018"
        | 115 LOG2_E "1.44269504088896340735992468100189214"
        | 116 LOG10_2 "0.301029995663981195213738894724493027"
        | 117 LOG10_E "0.434294481903251827651128918916605082"
        | 118 LN_2 "0.693147180559945309417232121458176568"
        | 119 LN_10 "2.30258509299404568401799145468436421"

        // meta symbols
        | 120 IT "it"
        | 121 SELF "Self"
        | 122 TYPE "Type"
        | 123 CONSTRAINT "Constraint"
        | 124 KIND "Kind"

        // predefined attributes
        | 125 FIXITY "fixity"
        | 126 ASSOC_L "left"
        | 127 ASSOC_R "right"
        | 128 INLINE "inline"
        | 129 NO_INLINE "no_inline"
        | 130 SPECIALIZE "specialize"
        | 131 TEST "test"
        | 132 IGNORE "ignore"
        | 133 ALLOW "allow"
        | 134 WARN "warn"
        | 135 DOC "doc"
        | 136 EXTENSION "extension"

        // termination fns known to the compiler
        | 137 PANIC "panic"
        | 138 ERROR "error"
        | 139 UNDEFINED "undefined"

        // used in desugaring, etc; NOTE these names are NOT qualified
        | 140 MAP_LIST "mapList"
        | 141 MAP "map"
        | 142 FILTER "filter"
        | 143 FOLD_R "foldr"
        | 144 FOLD_L "foldl"
        | 145 CONCAT_MAP "concatMap"
        | 146 WRAP "wrap"
        | 147 EMBED "embed"
        | 148 AND_THEN ">>="
        | 149 SHOW_FN "show"

        // built-in class names
        | 150 SHOW_CLASS "Show"
        | 151 EQ_CLASS "Eq"
        | 152 ORD_CLASS "Ord"
        | 153 ENUM_CLASS "Enum"
        | 154 BOUNDED_CLASS "Bounded"
        | 155 NUM_CLASS "Num"
        | 156 REAL_CLASS "Real"
        | 157 FRACTIONAL_CLASS "Fractional"
        | 158 APPLICATIVE_CLASS "Applicative"
        | 159 MONAD_CLASS "Monad"
}
