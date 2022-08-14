use std::fmt::Write;

/// Generate a textual representation of a variable not bound to a specific name.
/// This is useful when generating type variables whose actual *names* only matter when displayed to the user.
pub fn display_var(n: u32) -> String {
    const LIM: u32 = 26;
    const OFFSET: u32 = 0x61;
    if n < LIM {
        return String::from((n % LIM + OFFSET) as u8 as char);
    }
    let mut bytes = Vec::with_capacity((n as f64).log(LIM as f64).ceil() as usize);
    let mut ch = n;
    while ch >= LIM {
        bytes.push((ch % LIM + OFFSET) as u8);
        ch /= LIM;
    }
    let mut buf = String::with_capacity(bytes.len() + 1);
    buf.push((ch % LIM + OFFSET) as u8 as char);
    bytes.into_iter().rfold(buf, |mut a, c| {
        a.push(c as char);
        a
    })
}

/// Similar to `display_var`, but writes to a given string buffer instead of
/// allocating a new string.
pub fn write_display_var(n: usize, buf: &mut String) {
    const LIM: usize = 26;
    const OFFSET: usize = 0x61;
    if n < LIM {
        buf.push((n % LIM + OFFSET) as u8 as char);
        return;
    }
    let mut bytes = Vec::with_capacity((n as f64).log(LIM as f64).ceil() as usize);
    let mut ch = n;
    while ch >= LIM {
        bytes.push((ch % LIM + OFFSET) as u8);
        ch /= LIM;
    }
    bytes.push((ch % LIM + OFFSET) as u8);
    buf.reserve_exact(bytes.len());
    buf.extend(bytes.into_iter().rev().map(|b| b as char));
}

pub fn fmt_display_var(mut n: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    const LIM: usize = 26;
    const OFFSET: usize = 0x61;
    if n < LIM {
        return f.write_char((n % LIM + OFFSET) as u8 as char);
    }
    let mut bytes = Vec::with_capacity((n as f64).log(LIM as f64).ceil() as usize);
    while n >= LIM {
        bytes.push((n % LIM + OFFSET) as u8);
        n /= LIM;
    }
    bytes.push((n % LIM + OFFSET) as u8);
    for b in bytes.into_iter().rev() {
        f.write_char(b as char)?;
    }
    Ok(())
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

/// Compares two strings for equality while ignoring the ASCII case of
/// the *first* character in each respective string. Note that this
/// operation may not necessarily be cheap as it performs unicode NFC
/// normalization on both strings (but does *not* allocate any
/// `String`s); the function similarly named (without the `nfc`
/// suffix) may be preferred otherwise.
pub fn cmp_str_tails_nfc<S: AsRef<str>, T: AsRef<str>>(left: S, right: T) -> bool {
    use unicode_normalization::*;
    let sa = left.as_ref();
    let sb = right.as_ref();
    let mut left_chars = sa.nfc();
    let mut right_chars = sb.nfc();
    if left_chars.clone().count() != right_chars.clone().count() {
        return false;
    }
    left_chars.next();
    right_chars.next();
    left_chars.zip(right_chars).all(|(lc, rc)| lc == rc)
}

pub fn cmp_str_tails<S: AsRef<str>, T: AsRef<str>>(s: S, t: T) -> bool {
    let s = s.as_ref();
    let t = t.as_ref();
    if s.len() != t.len() {
        false
    } else {
        let mut s = s.char_indices();
        let mut t = t.char_indices();
        s.next();
        t.next();
        match (s.next(), t.next()) {
            // both are empty, so trivially tails are equal
            (None, None) => true,
            // ignore cmp on first char within char boundary, ensure
            // only that char boundaries match
            (Some((i, _ci)), Some((j, _cj))) if i == j => s
                .zip(t)
                .all(|((s_idx, s_c), (t_idx, t_c))| s_idx == t_idx && s_c == t_c),
            // initial char boundaries don't match, so
            // case we know they're not equal since the char indices
            // would be out of sync and hence not composed of the same
            // bytes in the same order (regardless of whether they are
            // equilengthed, e.g., 'ébép' and 'ébép' are of the same
            // length, but the first has 'e' + '\u+301' and 'é', while the
            // second has 'é' and 'e' + '\u+301')
            _ => false,
        }
    }
}

#[test]
fn test_cmp_str_tails() {
    let left = "ébép";
    let right = "ébép";
    assert!(!cmp_str_tails(left, right))
}

/// http://www.unicode.org/reports/tr31/
pub fn is_xid_start(c: char) -> bool {
    unicode_xid::UnicodeXID::is_xid_start(c)
}

pub fn is_xid_continue(c: char) -> bool {
    unicode_xid::UnicodeXID::is_xid_continue(c)
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
