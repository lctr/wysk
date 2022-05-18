pub trait Newtype<T, Inner = T> {
    type Inner;
}

#[macro_export]
/// Dealing with enums with uniformly shaped variants.
///
///
/// # Examples
/// ```
/// /// An enum whose variants are all uniformly shaped
/// enum Thing<X> {
///     A(X),
///     B(X),
///     C(X)
/// }
/// /// Implement a `get_inner` method to return `&X`
/// variants!{ #(X Thing :A :B :C) }
/// ```
/// to return a reference to the data held of type `X`.
macro_rules! variants {
    (
        #(($inner:ty) $name:ident $(:$ids:ident)+)
    ) => {
        impl $name {
            pub fn get_inner(&self) -> &$inner {
                match self {
                    // Self::$id($a0 $(, $as)*) => { ($a, $(, $as)*) }
                    $($name::$ids(s) => { s })+
                }
            }
        }
    };
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
            Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord
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
    ($($(#[$com:meta])+)? $name:ident |$tipo:ty| New) => {
        impl $name {
            $($(#[$com])+)?
            pub(crate) fn new(inner: $tipo) -> Self {
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
        $crate::newtype! { $name |$tipo| (&*)}
    };
    ($name:ident |$tipo:ty| (&*)) => {
        impl std::ops::Deref for $name {
            type Target = $tipo;
            fn deref(&self) -> &Self::Target {
                &(self.0)
            }
        }
    };
    ($name:ident |$tipo:ty| DerefMut) => {
        $crate::newtype! { $name |$tipo| (mut &*)}
    };
    ($name:ident |$tipo:ty| (mut &*)) => {
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
    ($name:ident |$tipo:ty| [#$gen:ident]) => {
        impl std::ops::Index<$name> for Vec<$gen> {
            type Output = $gen;
            fn index(&self, index: $name) -> &Self::Output {
                &self[usize::from(index)]
            }
        }
    };
    ($name:ident |$tipo:ty| [#mut $gen:ident]) => {
        $crate::newtype! { $name |$tipo| [$gen] }
        impl std::ops::IndexMut<$name> for Vec<$gen> {
            fn index_mut(&mut self, index: $name) -> &mut Self::Output {
                &mut self[usize::from(index)]
            }
        }
    };
    ($name:ident |$tipo:ty| [#$item:ty]) => {
        impl std::ops::Index<$name> for Vec<$item> {
            type Output = $item;
            fn index(&self, index: $name) -> &Self::Output {
                &self[usize::from(index)]
            }
        }
        impl<const N: usize> std::ops::Index<$name> for [$item; N] {
            type Output = $item;
            fn index(&self, index: $name) -> &Self::Output {
                &self[usize::from(index)]
            }
        }
    };
    ($name:ident |$tipo:ty| [#mut $item:ty]) => {
        impl std::ops::Index<$name> for Vec<$item> {
            fn index_mut(&mut self, index: $name) -> &mut Self::Output {
                &mut self[usize::from(index)]
            }
        }

        impl<const N: usize> std::ops::Index<$name> for [$item; N] {
            fn index_mut(&mut self, index: $name) -> &mut Self::Output {
                &mut self[usize::from(index)]
            }
        }
    };
    ($name:ident |$tipo:ty| [$gen:ident]) => {
        impl<$gen> std::ops::Index<$name> for Vec<$gen> {
            type Output = $gen;
            fn index(&self, index: $name) -> &Self::Output {
                &self[usize::from(index)]
            }
        }
    };
    ($name:ident |$tipo:ty| [mut $gen:ident]) => {
        $crate::newtype! { $name |$tipo| [$gen] }
        impl<$gen> std::ops::IndexMut<$name> for Vec<$gen> {
            fn index_mut(&mut self, index: $name) -> &mut Self::Output {
                &mut self[usize::from(index)]
            }
        }
    };
    ($name:ident |$tipo:ty| [$item:ty]) => {
        impl std::ops::Index<$name> for Vec<$item> {
            type Output = $item;
            fn index(&self, index: $name) -> &Self::Output {
                &self[usize::from(index)]
            }
        }
        impl<const N: usize> std::ops::Index<$name> for [$item; N] {
            type Output = $item;
            fn index(&self, index: $name) -> &Self::Output {
                &self[usize::from(index)]
            }
        }
    };
    ($name:ident |$tipo:ty| [mut $item:ty]) => {
        impl std::ops::Index<$name> for Vec<$item> {
            fn index_mut(&mut self, index: $name) -> &mut Self::Output {
                &mut self[usize::from(index)]
            }
        }

        impl<const N: usize> std::ops::Index<$name> for [$item; N] {
            fn index_mut(&mut self, index: $name) -> &mut Self::Output {
                &mut self[usize::from(index)]
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
    ($outer:ty[$name:ty] <> $elm:ty) => {
        impl std::ops::Index<$name> for $outer {
            type Output = $elm;
            fn index(&self, index: $name) -> &Self::Output {
                &self.0[usize::from(index)]
            }
        }
    };
    ($outer:ty[$name:ty] <mut> $elm:ty) => {
        $crate::newtype! { $outer[$name] <> $elm }
        impl std::ops::IndexMut<$name> for $outer where usize: From<$name> {
            fn index_mut(&mut self, index: $name) -> &mut Self::Output {
                &mut self.0[usize::from(index)]
            }
        }
    };
    (#$outer:ident<$g1:tt $(, $gs:tt)*>[$name:ty] <> #$elm:tt) => {
        /// Implementation `Index` for some newtype store `S<T, U>` and an index
        /// of type `U` such that `usize: From<U>`.
        /// The `g1` and `gs` fragments correspond to generic parameters.
        /// REQUIRES THE UNDERLYING STORAGE TO SUPPORT INDEXING WITH USIZES.
        impl<$g1 $(, $gs)*> std::ops::Index<$name> for $outer<$g1 $(, $gs)*> where
            usize: From<U>
        {
            type Output = $elm;
            fn index(&self, index: $name) -> &Self::Output {
                &self.0[usize::from(index)]
            }
        }
    };
    (#$outer:ident<$g1:tt $(, $gs:tt)*>[$name:ty] <mut> #$elm:tt) => {
        $crate::newtype! { #$outer<$g1 $(, $gs)*>[$name] <> #$elm }
        impl<$g1 $(, $gs)*> std::ops::IndexMut<$name> for $outer<$g1 $(, $gs)*> where usize: From<U> {
            fn index_mut(&mut self, index: $name) -> &mut Self::Output {
                &mut self.0[usize::from(index)]
            }
        }
    };
}

/// Some utilities for parametrizable (new)types. In particular, it may not be
/// ideal to automatically derive certain traits for containers or generic
/// newtypes, as this would provide potentially unnecessary constraints on the
/// type parameter. Instead, it is often more prudent to conditionally implement
/// traits based on the type parameter's trait bounds (as opposed to
/// vice-versa), though this has the downside of requiring quite the boilerplate
/// (e.g., the two types `Foo<A>` and `Bar<B>` would need four impl blocks just
/// to conditionally implement `Clone` and `PartialEq`, for example)
#[macro_export]
macro_rules! generic {
    (do ** for $name:ident, $gen:ident $(, $inner:ty)?) => {
        $crate::generic! { $name, $gen $(, $inner)?
            | Clone Copy
              Debug Display
              PartialEq Eq
              PartialOrd Ord
              Hash Default
        }
    };
    (
        $name:ident, $gen:ident $(, $inner:ty)?
        | $($trait:ident $(|)?)+
    ) => {};
    ($name:ident, $gen:ident $(, $inner:ty)? | Debug) => {
        impl<$gen> std::fmt::Debug for $name<$gen>
        where
            $gen: std::fmt::Debug,
            $($inner: std::fmt::Display)?
        {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_tuple(stringify!($name)).field(&self.0).finish()
            }
        }
    };
    ($name:ident, $gen:ident $(, $inner:ty)? | Display) => {
        impl<$gen> std::fmt::Display for $name<$gen>
        where
            $gen: std::fmt::Display,
            $($inner: std::fmt::Display)?
        {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}({})", stringify!($name), &self.0)
            }
        }
    };
    ($name:ident, $gen:ident $(, $inner:ty)? | Clone) => {
        impl<$gen> Clone for $name<$gen>
        where
            $gen: Clone,
            $($inner: Clone)?
        {
            fn clone(&self) -> Self {
                Self(self.0.clone())
            }
        }
    };
    ($name:ident, $gen:ident $(, $inner:ty)? | Copy) => {
        impl<$gen> Copy for $name<$gen>
        where
            $gen: Copy,
            $($inner: Copy)? {}
    };
    ($name:ident, $gen:ident $(, $inner:ty)? | PartialEq) => {
        impl<$gen> PartialEq for $name<$gen>
        where
            $gen: PartialEq,
            $($inner: PartialEq)? {
                fn eq(&self, other: &Self) -> bool {
                    self.0 == other.0
                }
            }
    };
    ($name:ident, $gen:ident $(, $inner:ty)? | Eq) => {
        impl<$gen> Eq for $name<$gen>
        where
            $gen: Eq,
            $($inner: Eq)? {}

    };
    ($name:ident, $gen:ident $(, $inner:ty)? | PartialOrd) => {
        impl<$gen> PartialOrd for $name<$gen>
        where
            $gen: PartialOrd,
            $($inner: PartialOrd)?
        {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                self.0.partial_cmp(&other.0)
            }
        }
    };
    ($name:ident, $gen:ident $(, $inner:ty)? | Ord) => {
        impl<$gen> Ord for $name<$gen>
        where
            $gen: Ord,
            $($inner: Ord)? {}
    };
    ($name:ident, $gen:ident $(, $inner:ty)? | Hash) => {
        impl<$gen> std::hash::Hash for $name<$gen>
        where
            $gen: std::hash::Hash,
            $($inner: std::hash::Hash)? {
                fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                    self.0.hash(state);
                }
            }
    };
    ($name:ident, $gen:ident | Default) => {
        impl<$gen> Default for $name<$gen>
        where
            $gen: Default,
            $inner: Default
        {
            fn default() -> Self {
                Self(<$gen as Default>::default())
            }
        }
    };
    ($name:ident, $gen:ident, $inner:ty | Default) => {
        impl<$gen> Default for $name<$gen>
        where
            $gen: Default,
            $inner: Default
        {
            fn default() -> Self {
                Self(Default::default())
            }
        }
    };
    ($name:ident, $gen:ident, $inner:ty | Deref) => {
        impl<$gen> std::ops::Deref for $name<$gen>
        where
            $gen: std::ops::Deref,
            $inner: std::ops::Deref
        {
            type Target = $inner;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }
    };
    ($name:ident, $gen:ident, $inner:ty | DerefMut) => {
        impl<$gen> std::ops::DerefMut for $name<$gen>
        where
            $gen: std::ops::DerefMut,
            $inner: std::ops::DerefMut
        {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.0
            }
        }
    };
}

#[cfg(test)]
mod test {
    newtype!(usize in U | Show Usize AsUsize [#char] (+) (-));
    struct Many<T>(Vec<T>);

    // implementing Clone for a newtype around a generic vector
    generic! { Many, T, Vec<T> | Clone Debug }

    newtype!(Many<()>[U] <mut> ());

    #[test]
    fn test_usize_newtype() {
        assert_eq!(U(3) + U(5), U(8));
        assert_eq!(U(150) - 50usize, U(100));
        assert_eq!(vec!['a', 'b', 'c'][U(1)], 'b');
        assert_eq!(Many(vec![(), (), (), ()])[U(3)], ());
        newtype!(Many<char>[U] <> char);
        assert_eq!(Many(vec!['a', 'b', 'c', 'd'])[U(3)], 'd');
    }
}
