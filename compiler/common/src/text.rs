pub fn lower_latin_alphabet() -> [char; 26] {
    [
        'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r',
        's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
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
        $name:ident
        $(@short: $prefix:ident)?
        $(@label: $label:ident)?
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

            fn from_str(s: &str) -> Option<Self> {
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
                    $($lit $(| $alt)* => {true})+
                    _ => false
                }
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

        $(
            #[allow(unused)]
            pub struct $kind<T = ()>(T);

            impl<T> $kind<T> {
                pub const fn parent() -> $name { $name::$kind }

                pub const fn text() -> [&'static str; $crate::strenum!(# $lit $($alt)*)] {
                    [ $lit, $($alt ,)* ]
                }

                pub fn new(t: T) -> $kind<T> {
                    $kind(t)
                }

                pub fn map<F, U>(self, mut f: F) -> $kind<U>
                where F: FnMut(T) -> U {
                    $kind(f(self.0))
                }

                pub fn get(&self) -> &T { &self.0 }

                pub fn take(self) -> T { self.0 }

                pub fn replace(&mut self, t: T) -> T {
                    std::mem::replace(&mut self.0, t)
                }
            }

            impl PartialEq<$name> for $kind {
                fn eq(&self, other: &$name) -> bool {
                    matches!(other, $name::$kind)
                }
            }

            impl PartialEq<$kind> for $name {
                fn eq(&self, _: &$kind) -> bool {
                    matches!(self, $name::$kind)
                }
            }

            impl<T> From<$kind<T>> for ($name, T) {
                fn from(k: $kind<T>) -> ($name, T) {
                    ($name::$kind, k.0)
                }
            }

            impl<T> AsRef<str> for $kind<T> {
                fn as_ref(&self) -> &str {
                    $name::$kind.as_str()
                }
            }

            impl std::str::FromStr for $kind<()> {
                type Err = ();
                fn from_str(s: &str) -> Result<$kind<()>, Self::Err> {
                   match $name::from_str(s) {
                       Some($name::$kind) => { Ok($kind(())) }
                       _ => Err(())
                   }
                }
            }

            $crate::generic! { $name, T, T
                | Copy Clone Debug Display PartialEq Eq Hash Default }
        )+

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

        let x = 5;
        let alts = Greeting::Hello.alt_strs();
        let g = Greeting::Hello;
        let x = Greeting::hello("hi");
    }
}
