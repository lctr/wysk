use wy_common::Deque;
use wy_intern::symbol::{self, Symbol, Symbolic};

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Ident {
    Upper(Symbol),
    Lower(Symbol),
    Infix(Symbol),
    /// Represent user-input type variables. These are for documentation
    /// primarily, as types are mapped to use `Tv` for variables during
    /// typechecking.
    Fresh(Symbol),
}

impl std::fmt::Debug for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Upper(arg0) => write!(f, "Upper({})", arg0),
            Self::Lower(arg0) => write!(f, "Lower({})", arg0),
            Self::Infix(arg0) => write!(f, "Infix({})", arg0),
            Self::Fresh(arg0) => write!(f, "Fresh({})", arg0),
        }
    }
}

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.symbol())
    }
}

impl Symbolic for Ident {
    fn get_symbol(&self) -> Symbol {
        self.symbol()
    }
}

wy_common::variants!(#((Symbol) Ident :Upper :Lower :Infix :Fresh));

impl Ident {
    pub fn symbol(&self) -> Symbol {
        *self.get_inner()
        // match self {
        //     Self::Upper(s) | Self::Lower(s) | Self::Infix(s) | Self::Fresh(s) => *s,
        // }
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
    pub fn is_fresh(&self) -> bool {
        matches!(self, Self::Fresh(..))
    }

    pub fn as_u32(self) -> u32 {
        self.get_inner().as_u32()
        // match self {
        //     Ident::Upper(s) | Ident::Lower(s) | Ident::Infix(s) | Ident::Fresh(s) => s.as_u32(),
        // }
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

    pub fn tuple_commas(extras: usize) -> Self {
        Self::Infix(symbol::intern_once(
            &*(0..(extras + 1)).map(|_| ',').collect::<String>(),
        ))
    }
}

#[test]
fn test_idents() {
    let cons = Ident::cons_sign();
    let minus = Ident::minus_sign();
    let tuples = (0..5).map(Ident::tuple_commas).collect::<Vec<_>>();
    assert_eq!(cons, Ident::Infix(symbol::intern_once(":")));
    assert_eq!(minus, Ident::Infix(symbol::intern_once("-")));
    assert_eq!(tuples[0], Ident::Infix(symbol::intern_once(",")));
    assert_eq!(tuples[1], Ident::Infix(symbol::intern_once(",,")));
    assert_eq!(tuples[2], Ident::Infix(symbol::intern_once(",,,")));
    assert_eq!(tuples[3], Ident::Infix(symbol::intern_once(",,,,")));
    assert_eq!(tuples[4], Ident::Infix(symbol::intern_once(",,,,,")));
}

/// Single wrapper for the parts comprising an identifier path (named `Chain` to
/// avoid ambiguity/similarity with relevant `Path` type(s)). A `Chain`
/// consists of a *root* identifier (or *head*) and a list of sequentially
/// suffixed identifiers, i.e., a *tail* set of identifiers.
///
/// The *root* of an identifier path is the first identifier in a
/// period-delimited chain of identifiers. Additionally, a chain of identifiers
/// may be *concatenated*.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chain<Id = Ident>(Id, Deque<Id>);

impl<Id> Chain<Id> {
    pub fn new(root: Id, tail: Deque<Id>) -> Self {
        Self(root, tail)
    }

    pub fn make_contiguous(&mut self) -> &mut [Id] {
        self.1.make_contiguous()
    }

    pub fn root(&self) -> &Id {
        &self.0
    }

    pub fn tail(&self) -> impl Iterator<Item = &Id> {
        self.1.iter()
    }

    /// Deconstructs into a tuple of its inner parts, returning a pair
    /// containing the root identifier along with a vector of tail identifiers.
    pub fn parts(self) -> (Id, Deque<Id>) {
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

    /// Returns an iterator over references to all identifiers in the `Chain`,
    /// with the `&Id` yielded in order.
    pub fn iter(&self) -> impl Iterator<Item = &Id> {
        vec![&self.0].into_iter().chain(self.1.iter())
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
            Some(Chain(ids[0], ids[1..].iter().copied().collect()))
        }
    }

    /// Given that a `Qualified` struct is parametrized over the identifiers
    /// involved, it is possible to transform a value of type `Qualified<X>`
    /// into a value of type `Qualified<Y>`. This method does not distinguish
    /// between head and tail identifiers, applying the given closure to *all*
    /// identifiers, with the only invariant being that the root identifier is
    /// the first identifier mapped.
    pub fn map<F, Y>(self, mut f: F) -> Chain<Y>
    where
        F: FnMut(Id) -> Y,
    {
        let Chain(x, xs) = self;
        Chain(f(x), xs.into_iter().map(f).collect())
    }

    pub fn contains_in_tail(&self, id: &Id) -> bool
    where
        Id: PartialEq,
    {
        self.1.contains(id)
    }

    pub fn concat_right(self, rhs: Self) -> Self {
        let head = self.0;
        let mut tail = self.1;
        tail.push_back(rhs.0);
        tail.extend(rhs.1);
        Chain(head, tail)
    }
}

impl<Id> Extend<Id> for Chain<Id> {
    fn extend<T: IntoIterator<Item = Id>>(&mut self, iter: T) {
        self.1.extend(iter)
    }
}

impl<Id> std::fmt::Display for Chain<Id>
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
