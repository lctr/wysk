pub trait Newtype<T, Inner = T> {
    type Inner;
}

// Simplify generating newtype definitions and implementations
// (predominantly for numeric indexing purposes)
#[macro_export]
macro_rules! newtype {
    // Repeated macro invocations are separated by curly braces
    // Additionally, comments before/above the curly braces are
    // applied to the entire macro invocation
    ($($($(#[$com:meta])+)? { $($ts:tt)+ })+ ) => {
        $(
            // $($(#[$com])+)?
            $crate::newtype! { $($(#[$com])+)? $($ts)+ }
        )+
    };
    (
        $($(#[$com:meta])+)?
        $tipo:ident in $name:ident
        $($(#[$coms2:meta])+)?
        | $($ts:tt)*
    ) => {
        $crate::newtype!{ $($(#[$com])+)? $name => $tipo }
        $($(#[$coms2])+)?
        $(
            $crate::newtype!{ $name |$tipo| $ts }
        )*
    };
    ($($(#[$com:meta])+)? $name:ident => $tipo:ty) => {
        $($(#[$com])+)?
        #[derive(
            Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord
        )]
        pub struct $name($tipo);

        impl std::cmp::PartialEq<$tipo> for $name {
            fn eq(&self, other: &$tipo) -> bool {
                &(self.0) == other
            }
        }

        impl std::cmp::PartialOrd<$tipo> for $name {
            fn partial_cmp(&self, other: &$tipo) -> Option<std::cmp::Ordering> {
                self.0.partial_cmp(other)
            }
        }

        impl std::fmt::Debug for $name where $tipo: std::fmt::Debug {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}({})", stringify!($name), &self.0)
            }
        }
    };
    ($($(#[$com:meta])+)? $name:ident |$tipo:ty| $trait:tt $($ts:tt)+) => {
        $crate::newtype! { $name |$tipo| $trait }
    };
    ($($(#[$com:meta])+)? $name:ident |$tipo:ty| Wrapper) => {
        $($(#[$com])+)?
        $crate::newtype! { $name |$tipo| PartialEq }
        $crate::newtype! { $name |$tipo| PartialOrd }
    };
    ($($(#[$com:meta])+)? $name:ident |$tipo:ty| (= $rhs:ty |$x:ident| $y:expr)) => {
        impl std::cmp::PartialEq<$rhs> for $name {
            fn eq(&self, other: &$rhs) -> bool {
                self.0 == (|$x: &$rhs| $y)(other)
            }
        }
    };
    ($($(#[$com:meta])+)? $name:ident |$tipo:ty| PartialEq) => {
        impl std::cmp::PartialEq<$tipo> for $name {
            fn eq(&self, other: &$tipo) -> bool {
                &(self.0) == other
            }
        }
    };
    ($($(#[$com:meta])+)? $name:ident |$tipo:ty| PartialOrd) => {
        impl std::cmp::PartialOrd<$tipo> for $name {
            fn partial_cmp(&self, other: &$tipo) -> Option<std::cmp::Ordering> {
                self.0.partial_cmp(other)
            }
        }
    };
    ($($(#[$com:meta])+)? $name:ident |$tipo:ty| [$data:ty]) => {
        impl std::ops::Index<$name> for Vec<$data> {
            type Output = $data;
            fn index(&self, index: $name) -> &Self::Output {
                &self[index.0 as usize]
            }
        }
    };
    ($($(#[$com:meta])+)? $name:ident |$tipo:ty| New) => {
        impl $name {
            $($(#[$com])+)?
            pub fn new(inner: $tipo) -> Self {
                $name(inner)
            }
        }
    };
    ($($(#[$com:meta])+)? $name:ident |$tipo:ty| Isize) => {
        impl $name {
            $($(#[$com])+)?
            #![allow(unused)]
            #[inline]
            pub const ZERO: Self = $name(0);
            #[inline]
            pub const ONE: Self = $name(1);
            #[inline]
            pub const MIN: Self = $name(<$tipo>::MIN);
            #[inline]
            pub const MAX: Self = $name(<$tipo>::MAX);
            #[inline]
            pub fn is_zero(&self) -> bool {
                *self == Self::ZERO
            }
            #[inline]
            pub fn as_isize(&self) -> isize {
                self.0 as isize
            }
        }

        $crate::newtype! { $name |$tipo| Neg }
    };
    ($name:ident |usize| AsUsize) => {
        impl From<$name> for usize {
            fn from($name(n): $name) -> usize {
                n as usize
            }
        }
    };
    ($name:ident |$tipo:ty| AsUsize) => {
        impl From<$name> for usize {
            fn from($name(n): $name) -> usize {
                n as usize
            }
        }

        impl std::cmp::PartialEq<usize> for $name {
            fn eq(&self, other: &usize) -> bool {
                &(self.0 as usize) == other
            }
        }

        impl std::cmp::PartialOrd<usize> for $name {
            fn partial_cmp(&self, other: &usize) -> Option<std::cmp::Ordering> {
                (self.0 as usize).partial_cmp(other)
            }
        }
    };
    ($name:ident |isize| AsIsize) => {
        impl From<$name> for isize {
            fn from($name(n): $name) -> isize {
                n as isize
            }
        }
    };
    ($name:ident |$tipo:ty| AsIsize) => {
        impl From<$name> for isize {
            fn from($name(n): $name) -> isize {
                n as isize
            }
        }

        impl std::cmp::PartialEq<isize> for $name {
            fn eq(&self, other: &isize) -> bool {
                &(self.0 as isize) == other
            }
        }

        impl std::cmp::PartialOrd<isize> for $name {
            fn partial_cmp(&self, other: &isize) -> Option<std::cmp::Ordering> {
                (self.0 as isize).partial_cmp(other)
            }
        }
    };
    ($name:ident |$tipo:ty| Neg) => {
        impl std::ops::Neg for $name {
            type Output = Self;
            fn neg(self) -> Self::Output {
                $name(-(self.0))
            }
        }
    };
    ($name:ident |$tipo:ty| Usize) => {
        impl $name {
            #![allow(unused)]
            #[inline]
            pub const ZERO: Self = $name(0);
            #[inline]
            pub const ONE: Self = $name(1);
            #[inline]
            pub const MIN: $name = $name(<$tipo>::MIN);
            #[inline]
            pub const MAX: Self = $name(<$tipo>::MAX);
            pub fn is_zero(&self) -> bool {
                *self == Self::ZERO
            }
            pub fn as_usize(&self) -> usize {
                self.0 as usize
            }
        }
    };
    ($name:ident |$tipo:ty| Show) => {
        impl std::fmt::Display for $name where $tipo: std::fmt::Display {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", &self.0)
            }
        }
    };
    ($name:ident |$tipo:ty| (Show $func:ident)) => {
        impl std::fmt::Display for $name where $tipo: std::fmt::Display {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", $func(self))
            }
        }
    };
    ($name:ident |$tipo:ty| ShowTuple) => {
        impl std::fmt::Display for $name where $tipo: std::fmt::Display {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}({})", stringify!($name), &(self.0))
            }
        }
    };
    ($name:ident |$tipo:ty| ShowPair) => {
        impl std::fmt::Display for $name where $tipo: std::fmt::Display {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "({} {})", stringify!($name), &(self.0))
            }
        }
    };
    ($name:ident |$tipo:ty| Deref) => {
        impl std::ops::Deref for $name {
            type Target = $tipo;
            fn deref(&self) -> &Self::Target {
                &(self.0)
            }
        }
    };
    ($name:ident |$tipo:ty| DerefMut) => {
        $crate::newtype!($name |$tipo| Deref);

        impl std::ops::DerefMut for $name {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut (self.0)
            }
        }
    };
    ($name:ident |$tipo:ty| AsRef) => {
        impl AsRef<$tipo> for $name {
            fn as_ref(&self) -> &$tipo {
                &(self.0)
            }
        }
    };
    ($name:ident |$tipo:ty| AsMut) => {
        impl AsMut<$tipo> for $name {
            fn as_mut(&mut self) -> &mut $tipo {
                &mut (self.0)
            }
        }
    };
    ($name:ident |$tipo:ty| (+)) => {
        impl std::ops::Add for $name {
            type Output = Self;
            fn add(self, rhs: Self) -> Self::Output {
                Self(self.0 + rhs.0)
            }
        }
        impl std::ops::Add<$tipo> for $name {
            type Output = Self;
            fn add(self, rhs: $tipo) -> Self::Output {
                Self(self.0 + rhs)
            }
        }
    };
    ($name:ident |$tipo:ty| (+ $rhs:ty |$x:ident| $y:expr)) => {
        impl std::ops::Add<$rhs> for $name {
            type Output = Self;
            fn add(self, rhs: $rhs) -> Self::Output {
                Self(self.0 + (|$x: $rhs| $y)(rhs))
            }
        }
    };
    ($name:ident |$tipo:ty| (+=)) => {
        $crate::newtype! { $name |$tipo| (+) }
        impl std::ops::AddAssign for $name {
            fn add_assign(&mut self, rhs: Self) {
                self.0 += rhs.0;
            }
        }
    };
    ($name:ident |$tipo:ty| (+= $rhs:ty |$x:ident| $y:expr)) => {
        $crate::newtype! { $name |$tipo| (+ $rhs |$x| $y) }
        impl std::ops::AddAssign<$rhs> for $name {
            fn add_assign(&mut self, rhs: $rhs) {
                self.0 += (|$x: $rhs| $y)(rhs)
            }
        }
    };
    ($name:ident |$tipo:ty| (-)) => {
        impl std::ops::Sub<$tipo> for $name {
            type Output = Self;
            fn sub(self, rhs: $tipo) -> Self::Output {
                Self(if self.0 < rhs { 0 } else { self.0 - rhs })
            }
        }

        impl std::ops::Sub for $name {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self::Output {
                Self(if self.0 < rhs.0 { 0 } else { self.0 - rhs.0 })
            }
        }
    };
    ($name:ident |$tipo:ty| (- $rhs:ty |$x:ident| $y:expr)) => {
        impl std::ops::Sub<$rhs> for $name {
            type Output = Self;
            fn sub(self, rhs: $rhs) -> Self::Output {
                Self(self.0 - (|$x: $rhs| $y)(rhs))
            }
        }
    };
    ($name:ident |$tipo:ty| (-=)) => {
        $crate::newtype! { $name |$tipo| (-) }
        impl std::ops::SubAssign for $name {
            fn sub_assign(&mut self, rhs: Self) {
                if rhs.0 < self.0 { self.0 -= rhs.0 };
            }
        }
    };
    ($name:ident |$tipo:ty| (-= $rhs:ty |$x:ident| $y:expr)) => {
        $crate::newtype! { $name |$tipo| (- $rhs |$x| $y) }
        impl std::ops::SubAssign<$rhs> for $name {
            fn add_assign(&mut self, rhs: $rhs) {
                self.0 -= (|$x: $rhs| $y)(rhs)
            }
        }
    };
    ($name:ident |$tipo:ty| (%)) => {
        impl std::ops::Rem for $name {
            type Output = Self;
            fn rem(self, rhs: Self) -> Self::Output {
                Self(self.0 % rhs.0)
            }
        }
        impl std::ops::Rem<$tipo> for $name {
            type Output = Self;
            fn rem(self, rhs: $tipo) -> Self::Output {
                Self(self.0 % rhs)
            }
        }
    };
    ($name:ident |$tipo:ty| (% $rhs:ty |$x:ident| $y:expr)) => {
        impl std::ops::Rem<$rhs> for $name {
            type Output = Self;
            fn rem(self, rhs: $rhs) -> Self::Output {
                Self(self.0 % (|$x:ident| $y)(rhs))
            }
        }
    };
    ($name:ident |$tipo:ty| (%=)) => {
        $crate::newtype! { $name |$tipo| (%) }
        impl std::ops::RemAssign for $name {
            fn rem_assign(&mut self, rhs: Self) {
                self.0 %= rhs.0;
            }
        }
    };
    ($name:ident |$tipo:ty| (%= $rhs:ty |$x:ident| $y:expr)) => {
        $crate::newtype! { $name |$tipo| (% $rhs |$x| $y) }
        impl std::ops::AddAssign<$rhs> for $name {
            fn add_assign(&mut self, rhs: $rhs) {
                self.0 %= (|$x: $rhs| $y)(rhs)
            }
        }
    };
}

#[cfg(test)]
mod test {}
