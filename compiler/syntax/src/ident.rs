use wy_intern::symbol::{self, Symbol};

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Ident {
    Upper(Symbol),
    Lower(Symbol),
    Infix(Symbol),
}

impl std::fmt::Debug for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Upper(arg0) => write!(f, "Upper({})", arg0),
            Self::Lower(arg0) => write!(f, "Lower({})", arg0),
            Self::Infix(arg0) => write!(f, "Infix({})", arg0),
        }
    }
}

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.get_symbol())
    }
}

impl Ident {
    pub fn get_symbol(&self) -> Symbol {
        match self {
            Self::Upper(s) | Self::Lower(s) | Self::Infix(s) => *s,
        }
    }
    pub fn is_upper(&self) -> bool {
        matches!(self, Self::Upper(..))
    }
    pub fn is_lower(&self) -> bool {
        matches!(self, Self::Lower(..))
    }
    pub fn is_infix(&self) -> bool {
        matches!(self, Self::Infix(..))
    }

    #[inline]
    pub fn minus_sign() -> Self {
        symbol::MINUS.pure(Self::Infix)
        // Self::Infix(*symbol::MINUS)
    }

    #[inline]
    pub fn cons_sign() -> Self {
        Self::Infix(*symbol::CONS)
    }

    pub fn tuples_sign(extras: usize) -> Self {
        Self::Infix(symbol::intern_once(
            &*(0..(extras + 1)).map(|_| ',').collect::<String>(),
        ))
    }
}

pub struct Grouped<T>(T);
wy_common::generic! { Grouped, T, T
    | Clone Copy Debug Display PartialEq Eq PartialOrd Ord Default Hash
}

#[test]
fn test_idents() {
    let cons = Ident::cons_sign();
    let minus = Ident::minus_sign();
    let tuples = (0..5).map(Ident::tuples_sign).collect::<Vec<_>>();
    assert_eq!(cons, Ident::Infix(symbol::intern_once(":")));
    assert_eq!(minus, Ident::Infix(symbol::intern_once("-")));
    assert_eq!(tuples[0], Ident::Infix(symbol::intern_once(",")));
    assert_eq!(tuples[1], Ident::Infix(symbol::intern_once(",,")));
    assert_eq!(tuples[2], Ident::Infix(symbol::intern_once(",,,")));
    assert_eq!(tuples[3], Ident::Infix(symbol::intern_once(",,,,")));
    assert_eq!(tuples[4], Ident::Infix(symbol::intern_once(",,,,,")));
}

/// Single wrapper for the parts comprising an identifier path. A `Path`
/// consists of a *root* identifier (or *head*) and a *tail* set of identifiers.
/// The *root* of an identifier path is the first identifier in a
/// period-delimited chain of identifiers, and is modeled in a design similar to
/// cons lists to allow for ergonomic conversion from simple identifiers
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Qualified<Id = Ident>(Id, Vec<Id>);

impl<Id> Qualified<Id> {
    pub fn new(root: Id, tail: Vec<Id>) -> Self {
        Self(root, tail)
    }

    pub fn root(&self) -> &Id {
        &self.0
    }

    pub fn tail(&self) -> &[Id] {
        &self.1[..]
    }

    /// Deconstructs into a tuple of its inner parts, returning a pair
    /// containing the root identifier along with a vector of tail identifiers.
    pub fn parts(self) -> (Id, Vec<Id>) {
        (self.0, self.1)
    }

    /// Return the length of the vector containing non-root identifiers. For
    /// example, the string `Foo.Bar.Baz` as an instance of `Qualified` contains
    /// the identifier `Foo` in the root and [`Bar`, `Baz`] in the tail, hence
    /// having a tail length of `2`. This is equivalent to calling `len` on the
    /// tail component's vector of identifiers.
    pub fn tail_len(&self) -> usize {
        self.1.len()
    }

    /// Given a slice of `Id`s of length > 1, returns a new instance (wrapped in
    /// a `Some` variant) of type `Self` where the first `Id` is in the root and
    /// the rest in the tail. If the slice is empty or has length 1, `None` is
    /// returned.
    ///
    /// Note that this method requires the identifier parameter `Id` to
    /// implement `Copy`.
    pub fn from_slice(ids: &[Id]) -> Option<Self>
    where
        Id: Copy,
    {
        if ids.len() < 2 {
            None
        } else {
            Some(Qualified(ids[0], ids[1..].iter().copied().collect()))
        }
    }

    /// Given that a `Qualified` struct is parametrized over the identifiers
    /// involved, it is possible to transform a value of type `Qualified<X>`
    /// into a value of type `Qualified<Y>`. This method does not distinguish
    /// between head and tail identifiers, applying the given closure to *all*
    /// identifiers, with the only invariant being that the root identifier is
    /// the first identifier mapped.
    pub fn map<F, Y>(self, mut f: F) -> Qualified<Y>
    where
        F: FnMut(Id) -> Y,
    {
        let Qualified(x, xs) = self;
        Qualified(f(x), xs.into_iter().map(f).collect())
    }
}

impl<Id> std::fmt::Display for Qualified<Id>
where
    Id: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self.0)?;
        for id in &self.1 {
            write!(f, ".{}", id)?;
        }
        Ok(())
    }
}
