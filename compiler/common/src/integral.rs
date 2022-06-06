use std::ops;

pub trait Zero: PartialEq + Sized {
    const ZERO: Self;
    const ONE: Self;
    const LIMIT: Self;

    /// may be overwritten for efficiency
    #[inline]
    fn is_zero(&self) -> bool {
        self == &Self::ZERO
    }

    #[inline]
    fn size_of() -> usize {
        std::mem::size_of::<Self>()
    }

    #[inline]
    fn size_of_val(&self) -> usize {
        std::mem::size_of_val(self)
    }

    #[inline]
    fn nat() -> Nat<Self> {
        Nat::Zero
    }

    #[inline]
    fn tick(self) -> Self
    where
        Self: Sized + ops::Add<Output = Self>,
    {
        self + Self::ONE
    }

    #[inline]
    fn plus(self, rhs: Self) -> <Self as ops::Add>::Output
    where
        Self: ops::Add + Sized,
    {
        self + rhs
    }

    #[inline]
    fn succ<R: Zero + ops::Add<Self, Output = Self>>(
        self,
        rhs: Option<R>,
    ) -> Nat<<Self as ops::Add<R>>::Output>
    where
        Self: ops::Add<R, Output = Self> + Sized,
    {
        match rhs {
            Some(r) if r.is_zero() && self.is_zero() => Nat::Zero,
            None if self.is_zero() => Nat::Zero,
            Some(r) => Nat::Succ(self + r),
            None => Nat::Succ(self + R::ZERO),
        }
    }
}

macro_rules! impl_zero {
    (
        $((Int | $ity0:ident $($(,)? $ity:ident)*))?
        $((Real | $fty0:ident $($(,)? $fty:ident)*))?
        $((Wrapping $t:ident))?
    ) => {
        $(impl_zero! { @Int $ity0 }
        $(
            impl_zero! { @Int $ity }
        )*)?
        $(impl_zero! { @Real $fty0 }
        $(
            impl_zero! { @Real $fty }
        )*)?
        $(
            impl_zero! { @Wrapping $t }
        )?
    };
    (
        @Int $ty:ident
    ) => {
        impl Zero for $ty {
            const ZERO: Self = 0;
            const ONE: Self = 1;
            const LIMIT: Self = $ty::MAX;
        }
        impl Integral for $ty {
            fn as_usize(&self) -> usize {
                *self as usize
            }
            fn as_u32(&self) -> u32 {
                *self as u32
            }
        }
    };
    (
        @Real $fty:ident
    ) => {
        impl Zero for $fty {
            const ZERO: Self = 0.0;
            const ONE: Self = 1.0;
            const LIMIT: Self = $fty::MAX;
        }
    };
    (
        @Wrapping $gen:ident
    ) => {
        impl<$gen> Zero for std::num::Wrapping<$gen> where $gen: Zero {
            const ZERO: Self = std::num::Wrapping($gen::ZERO);
            const ONE: Self = std::num::Wrapping($gen::ONE);
            const LIMIT: Self = std::num::Wrapping($gen::LIMIT);
        }
    };
    (
        @$t:ty[$gen:ty]()
    ) => {
        impl<$gen> Zero for $t<$gen> where $gen: Zero {
            const ZERO: Self = Self($gen::ZERO);
            const ONE: Self = Self($gen::ONE);
            const LIMIT: Self = Self($gen::LIMIT);
        }
    };
}

impl_zero! {
    (Int | usize isize u8 i8 u16 i16 u32 i32 u64 i64 u128 i128)
    (Real | f32 f64)
    (Wrapping N)
}

#[derive(Clone, Copy, PartialEq)]
pub enum Nat<N> {
    Zero,
    Succ(N),
}

impl<N: std::fmt::Debug> std::fmt::Debug for Nat<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ty = std::any::type_name::<N>();
        match self {
            Nat::Zero => write!(f, "0{}'{}", if ty.starts_with('f') { ".0" } else { "" }, ty),
            Nat::Succ(n) => write!(f, "{:?}'{}", n, ty),
        }
    }
}

impl<N: std::fmt::Display> std::fmt::Display for Nat<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ty = std::any::type_name::<N>();
        match self {
            Nat::Zero => write!(f, "0{}'{}", if ty.starts_with('f') { ".0" } else { "" }, ty),
            Nat::Succ(n) => write!(f, "{}'{}", n, ty),
        }
    }
}

crate::variant_preds! {
    |N| Nat[N]
    | is_zero_variant => Zero
    | is_nonzero_variant => Succ(_)
}

impl<N> Nat<N> {
    #[inline]
    pub fn into_inner(self) -> N
    where
        N: Zero,
    {
        match self {
            Nat::Zero => N::ZERO,
            Nat::Succ(n) => n,
        }
    }
    /// Corrects variant used in representation by replacing any `Succ` variants
    /// containing `0` with the `Zero` variant.
    pub fn sync(&mut self)
    where
        N: Zero,
    {
        if let Self::Succ(n) = self {
            if n.is_zero() {
                *self = Self::Zero
            }
        }
    }
}

impl<N: Zero + Eq> Eq for Nat<N> {}
impl<N: Zero + PartialOrd> PartialOrd for Nat<N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering::*;
        match (self, other) {
            (Self::Zero, Self::Zero) => Some(Equal),
            (Self::Succ(n), Self::Zero) | (Self::Zero, Self::Succ(n)) if n.is_zero() => Some(Equal),
            (Self::Zero, Self::Succ(n)) => N::ZERO.partial_cmp(n),
            (Self::Succ(n), Self::Zero) => n.partial_cmp(&N::ZERO),
            (Self::Succ(n), Self::Succ(m)) => n.partial_cmp(m),
        }
    }
}

impl<N: Zero> PartialEq<N> for Nat<N> {
    fn eq(&self, other: &N) -> bool {
        match (self, other) {
            (Self::Zero, n) => n.is_zero(),
            (Self::Succ(m), n) => m == n,
        }
    }
}

impl<N: Zero + PartialOrd> PartialOrd<N> for Nat<N> {
    fn partial_cmp(&self, other: &N) -> Option<std::cmp::Ordering> {
        match self {
            Nat::Zero => N::ZERO.partial_cmp(other),
            Nat::Succ(n) => n.partial_cmp(other),
        }
    }
}

impl<N> ops::Add for Nat<N>
where
    N: Zero + ops::Add<Output = N>,
{
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Zero, Self::Zero) => Self::Zero,
            (Self::Zero, n) | (n, Self::Zero) => {
                if n.is_zero() {
                    Self::Zero
                } else {
                    n
                }
            }
            (Self::Succ(n), Self::Succ(m)) => {
                if n.is_zero() {
                    Self::Succ(m)
                } else if m.is_zero() {
                    Self::Succ(n)
                } else {
                    Self::Succ(n + m)
                }
            }
        }
    }
}

impl<N> ops::AddAssign for Nat<N>
where
    N: Copy + Zero + ops::Add<N, Output = N>,
{
    fn add_assign(&mut self, rhs: Self) {
        match rhs {
            Nat::Zero => (),
            Nat::Succ(n) if n.is_zero() => (),
            Nat::Succ(n) => {
                if !n.is_zero() {
                    self.sync();
                    *self = match self {
                        Nat::Zero => Nat::Succ(n),
                        Nat::Succ(m) => {
                            let k = *m + n;
                            if k.is_zero() {
                                Nat::Zero
                            } else {
                                Nat::Succ(k)
                            }
                        }
                    }
                }
            }
        }
    }
}

impl<N: Zero> Zero for Nat<N> {
    const ZERO: Self = Self::ZERO;

    const ONE: Self = Self::Succ(N::ONE);

    const LIMIT: Self = Self::Succ(N::LIMIT);

    #[inline]
    fn is_zero(&self) -> bool {
        match self {
            Nat::Zero => true,
            Nat::Succ(n) => n.is_zero(),
        }
    }
}

impl<N: Integral> Integral for Nat<N> {
    #[inline]
    fn as_usize(&self) -> usize {
        match self {
            Nat::Zero => 0,
            Nat::Succ(n) => n.as_usize(),
        }
    }

    #[inline]
    fn as_u32(&self) -> u32 {
        match self {
            Nat::Zero => 0,
            Nat::Succ(n) => n.as_u32(),
        }
    }
}

pub trait Integral: Zero {
    fn as_usize(&self) -> usize;
    fn as_u32(&self) -> u32;
    fn index_in<I: ops::Index<usize>>(self, item: &I) -> &I::Output {
        &item[self.as_usize()]
    }
    fn fresh_var_label(&self) -> String {
        crate::text::display_var(self.as_u32())
    }
}

impl<N> From<N> for Nat<N>
where
    N: Zero,
{
    fn from(n: N) -> Self {
        if n.is_zero() {
            Self::Zero
        } else {
            Self::Succ(n)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_integral() {
        let items = ['a', 'b', 'c'];
        let it = Nat::from(2usize).index_in(&items);
        assert_eq!(it, &'c')
    }
}
