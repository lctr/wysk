use std::fmt::Write;

pub const LOWER_LATIN: [char; 26] = [
    'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's',
    't', 'u', 'v', 'w', 'x', 'y', 'z',
];

// pub const UPPER_LATIN: [char; 26] = [
//     'A', 'B', 'C', 'D', 'E', 'F', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z'
// ];

// pub const LOWER_CONS: [char; 6] = ['f', 'm', 't', 's', 'p', 'w'];

/// Generate a textual representation of a variable not bound to a specific name.
/// This is useful when generating type variables whose actual *names* only matter when displayed to the user.
pub fn display_var(n: u32) -> String {
    let azs = LOWER_LATIN;
    let mut buf = String::new();
    let mut tmp = n as usize;
    let lim = azs.len();
    let mut ct = 0;
    loop {
        if tmp < lim {
            buf.push(azs[tmp]);
            break buf;
        } else {
            buf.push(azs[ct % lim]);
            ct += 1;
            tmp -= lim;
        }
    }
}

/// Similar to `display_var`, but writes to a given string buffer instead of
/// allocating a new string.
pub fn write_display_var(mut n: usize, buf: &mut String) {
    let mut ct = 0;
    loop {
        if n < 26 {
            buf.push(LOWER_LATIN[n]);
            break;
        } else {
            buf.push(LOWER_LATIN[ct % 26]);
            ct += 1;
            n -= 26;
        }
    }
}

pub fn fmt_display_var(mut n: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut ct = 0;
    loop {
        if n < 26 {
            break f.write_char(LOWER_LATIN[n]);
        } else {
            f.write_char(LOWER_LATIN[ct % 26])?;
            ct += 1;
            n -= 6;
        }
    }
}

/// Capitalizes the first letter in a given string.
pub fn capitalize_first(s: impl AsRef<str>) -> String {
    let mut buf = String::new();
    let s = s.as_ref();
    if s.len() > 0 {
        let mut chars = s.chars();
        chars.next().map(|c: char| {
            buf.push({
                if c.is_ascii_lowercase() {
                    c.to_ascii_uppercase()
                } else {
                    c
                }
            })
        });
        chars.for_each(|c| buf.push(c));
    };
    buf
}

#[test]
fn test_capitalize_first() {
    assert_eq!(String::from("Function"), capitalize_first("function"))
}

/// Enums corresponding to a literal, but that *don't* hold any data values,
/// instead dynamically converting between literal and enum. Literal values are
/// automatically recorded in doc comments for each enum variant.
#[macro_export]
macro_rules! strenum {
    (
        $name:ident
        $(@short: $prefix:ident)?
        $(@test_str: $test_str:ident)?
        $(@any_case: $any_case:ident)?
        $(@label: $label:ident)?
        // $(::)?
        $(
           $(:)? $kind:ident $lit:literal $(| $alt:literal)* $(=> $lower:ident)?
        )+
    ) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash,
            serde::Serialize, serde::Deserialize
        )]
        pub enum $name {
            $(
                #[doc = $lit]
                $kind
            ),+
        }

        #[allow(unused)]
        impl $name {
            pub const STRINGS:
                [&'static str; $crate::strenum!(# $($lit $($alt)*)+)]
                = [$($lit, $($alt,)*)+];

            pub const KINDS: [Self; $crate::strenum!(# $($kind)+)]
                = [$($name::$kind,)+];

            pub fn from_str(s: &str) -> Option<Self> {
                match s {
                    $($lit $(| $alt)* => { Some($name::$kind) })+
                    _ => None
                }
            }

            pub fn as_str(&self) -> &str {
                match self {
                    $($name::$kind => {$lit})+
                }
            }

            $(
                $(
                    /// If a lowercase alias was ascribed to a variant (i.e., a
                    /// variant ends in `=> IDENTIFIER`), then this method will
                    /// exist and try to convert a given string slice into that
                    /// variant
                    pub fn $lower(s: &str) -> Option<Self>  {
                        if s == $lit { Some($name::$kind) } else { None }
                    }
                )?
            )+

            pub fn is_kind(word: &str) -> bool {
                match word {
                    $($lit $(| $alt)* => { true })+
                    _ => false
                }
            }

            $(
                pub fn $test_str(word: &str) -> bool {
                    Self::is_kind(word)
                }
            )?


            pub fn eq_ignore_ascii_case(word: &str) -> bool {
                Self::is_kind(word) $(
                    || word.eq_ignore_ascii_case($lit)
                    $(|| word.eq_ignore_ascii_case($alt))*
                )+
            }


            pub fn alt_strs(&self) -> &[&'static str] {
                match self {
                    $($name::$kind => {
                        &[$($alt,)*]
                    })+
                    // _ => &[]
                }
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                match self {
                    $($name::$kind => { write!(f, "{}", $lit) })+
                }
            }
        }

        impl std::str::FromStr for $name {
            type Err = ();

            fn from_str(s: &str) -> Result<$name, Self::Err> {
                $name::from_str(s).ok_or(())
            }
        }
    };
    (
        $opk:ident :: $(
            $name:ident
            $lit:literal
        )+
    ) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash,
            serde::Serialize, serde::Deserialize
        )]
        pub enum $opk {
            $(
                #[doc = $lit]
                $name
            ),+
        }

        impl $opk {
            pub const STRINGS: [&'static str; $crate::strenum!(# $($lit)+)] = [$($lit,)+];

            pub const KINDS: [Self; $crate::strenum!(# $($name)+)]
                = [$($opk::$name,)+];

            pub fn from_str(s: &str) -> Option<Self> {
                match s {
                    $($lit => {Some($opk::$name)})+
                    _ => None
                }
            }
            pub fn as_str(&self) -> &str {
                match self {
                    $($opk::$name => {$lit})+
                }
            }
            pub fn from_char(c: char) -> Option<Self> {
                $(if matches!($lit.chars().next(), Some(ch) if ch == c) {
                    return Some($opk::$name);
                })+
                None
            }
        }

        impl AsRef<str> for $opk {
            fn as_ref(&self) -> &str {
                match self {
                    $($opk::$name => {$lit})+
                }
            }
        }

        impl std::fmt::Display for $opk {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                match self {
                    $($opk::$name => { write!(f, "{}", $lit) })+
                }
            }
        }
    };
    (ident $t:tt) => {$t};
    (# $t:tt $($ts:tt)*) => {
        1  $( + $crate::strenum!(# $ts) )*
    };
    (# $t:tt) => { 1 };
    (#) => { 0 };
    (
        $opk:ident
        $is_kind:tt $([&$parent:ident $variant:ident(self)])? :: $(
            $name:ident
            $lit:literal $(| $alt:literal)*
        )+) => {
        $crate::strenum! {
            $opk :: $(
                $name
                $lit
            )+
        }

        #[allow(unused)]
        impl $opk {
            pub fn $is_kind(word: &str) -> bool {
                match word {
                    $($lit => {true})+
                    _ => false
                }
            }
            pub fn all_variants() -> Vec<Self> {
                let mut variants = vec![];
                $(
                    variants.push(Self::$name);
                )*
                variants
            }
            pub fn all_variant_str() -> Vec<&'static str> {
                let mut labels = vec![];
                $(
                    labels.push($lit);
                )*
                labels
            }
            pub const fn array() -> [Self; $crate::strenum!(# $($name)+)] {
                [$($opk::$name,)+]
            }
            pub fn array_str() -> [&'static str; $crate::strenum!(# $($name)+)] {
                [$($lit,)+]
            }
            pub fn is_any_of(&self, others: &[$opk]) -> bool {
                others.contains(self)
            }
            pub fn get_ord(&self) -> usize {
                let mut i = 0;
                $(
                    if self == &Self::$name { return i; } else { i += 1; };
                )+
                i
            }
            pub fn as_cow<'t>(self) -> std::borrow::Cow<'t, str> {
                match self {
                    $($opk::$name => {
                        let s = $lit;
                        s.into()
                    })+
                }
            }
            pub fn eq_ignore_ascii_case(word: &str) -> bool {
                Self::$is_kind(word) $(
                    || word.eq_ignore_ascii_case($lit)
                    $(|| word.eq_ignore_ascii_case($alt))*
                )+
            }


            pub fn alt_strs(&self) -> &[&'static str] {
                match self {
                    $($opk::$name => {
                        &[$($alt,)*]
                    })+
                    // _ => &[]
                }
            }
        }
    };
}

/// Allows generating code for `AsRef` and `Deref` for a type that's a simple
/// wrapper without having to re-specify all of the constructors, e.g.,
/// `AsRef<A>::as_ref(&C) -> &A::B(C)`
#[macro_export]
macro_rules! ref_lifting_strenum {
    (
        $name:ident $pred:ident => $parent:ident $variant:ident ::
        $($kind:ident $lit:literal)+
    ) => {
        $crate::strenum! { $name $pred :: $($kind $lit)+ }

        impl AsRef<$parent> for $name {
            fn as_ref(&self) -> &$parent {
                match self {
                    $($name::$kind => { &$parent::$variant($name::$kind) })+
                }
            }
        }

        impl std::ops::Deref for $name {
            type Target = $parent;

            fn deref(&self) -> &Self::Target {
                match self {
                    $($name::$kind => { &$parent::$variant($name::$kind) })+
                }
            }
        }
    };
}

#[cfg(test)]
mod test {
    #[test]
    fn test_strenums_1() {
        strenum! {
            Greeting
            @label: greeting
            Hello "hello" | "hi" | "hey" => hello
            Bye "bye" | "goodbye" | "later" => bye
        }

        let _x = 5;
        let _alts = Greeting::Hello.alt_strs();
        let _g = Greeting::Hello;
        let _x = Greeting::hello("hi");
    }
}
