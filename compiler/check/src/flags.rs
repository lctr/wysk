use wy_common::{newtype, variant_preds};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Level {
    Top,
    Other,
}

variant_preds! { Level
    | is_top_level => Top
    | is_other_level => Other
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Boxity {
    Boxed,
    Unboxed,
}

variant_preds! { Boxity
    | is_boxed => Boxed
    | is_unboxed => Unboxed
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Recur {
    Recursive,
    NonRecursive,
}

impl From<bool> for Recur {
    fn from(b: bool) -> Self {
        if b {
            Self::Recursive
        } else {
            Self::NonRecursive
        }
    }
}

variant_preds! { Recur
    | is_rec => Recursive
    | is_nonrec => NonRecursive
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Origin {
    FromSource,
    Generated,
}

variant_preds! { Origin
    | is_from_source => FromSource
    | is_generated => Generated
}

/// Embedded-Projection pairs contain two pieces of code.
///
/// If we have arbitrary functions representing the following pairs
///     `from :: T -> Thing`
///     `to :: Thing -> T`
/// such that `to (from x) = x`, we treat `Thing` as the *main* type and `Thing`
/// as the *representation* type. This is useful in remembering which direction
/// to take, i.e., using `from` vs `to`.
pub trait Paired {
    type Main;
    type Repr;
}

impl<X, Y> Paired for (X, Y) {
    type Main = X;
    type Repr = Y;
}

impl<T> Paired for Option<T>
where
    T: Paired,
{
    type Main = Option<T::Main>;
    type Repr = Option<T::Repr>;
}

impl<X, E> Paired for Result<X, E>
where
    X: Paired,
{
    type Main = Result<X::Main, E>;
    type Repr = Result<X::Repr, E>;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Pair<T: Paired, F, G>
where
    F: Fn(T::Repr) -> T::Main,
    G: Fn(T::Main) -> T::Repr,
{
    from: F,
    into: G,
    _owns: std::marker::PhantomData<T>,
}
impl<T, F, G> Pair<T, F, G>
where
    T: Paired,
    F: Fn(T::Repr) -> T::Main,
    G: Fn(T::Main) -> T::Repr,
{
    pub fn new(from: F, into: G) -> Self {
        Self {
            from,
            into,
            _owns: std::marker::PhantomData,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Occurrence {
    /// Many or unknown occurrences
    Unknown,
    Unused,
    /// If this identifier occurs exactly once
    Single {
        in_lambda: bool,
        single_branch: bool,
        interesting_ctx: bool,
    },
}

impl Default for Occurrence {
    fn default() -> Self {
        Occurrence::Unknown
    }
}

variant_preds! { Occurrence
    | is_unknown => Unknown
    | is_unused => Unused
    | is_single => Single {..}
}

newtype! { usize in PhaseId | ShowPair (-) }

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Activation {
    Never,
    Always,
    Before(PhaseId),
    After(PhaseId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Phase {
    Initial,
    Phase(PhaseId),
}

impl std::fmt::Display for Phase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Phase::Initial => write!(f, "InitialPhase"),
            Phase::Phase(ph) => write!(f, "{}", ph),
        }
    }
}
