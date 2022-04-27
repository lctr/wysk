pub fn lower_latin_alphabet() -> [char; 26] {
    [
        'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n',
        'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
    ]
}

/// Generate a textual representation of a variable not bound to a specific name.
/// This is useful when generating type variables whose actual *names* only matter when displayed to the user.
pub fn display_var(n: u32) -> String {
    let azs = lower_latin_alphabet();
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

/// Enums corresponding to a literal, but that *don't* hold any data values,
/// instead dynamically converting between literal and enum. Literal values are
/// automatically recorded in doc comments for each enum variant.
#[macro_export]
macro_rules! strenum {
    (
        $opk:ident :: $(
            $name:ident
            $lit:literal
        )+
    ) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash,
            // serde::Serialize, serde::Deserialize
        )]
        pub enum $opk {
            $(
                #[doc = $lit]
                $name
            ),+
        }

        impl $opk {
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
        $is_kind:tt :: $(
            $name:ident
            $lit:literal
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
            pub fn array() -> [Self; $crate::strenum!(# $($name)+)] {
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
        }
    };
}
