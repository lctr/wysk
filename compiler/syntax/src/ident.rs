use wy_common::{deque, Deque};
use wy_intern::symbol::{self, reserved, Symbol, Symbolic};

pub trait Identifier: Eq {
    fn is_upper(&self) -> bool;
    fn is_lower(&self) -> bool;
    fn is_infix(&self) -> bool;
    fn is_fresh(&self) -> bool;
    fn pure(&self) -> fn(Symbol) -> Ident {
        if self.is_upper() {
            Ident::Upper
        } else if self.is_lower() {
            Ident::Lower
        } else if self.is_infix() {
            Ident::Infix
        } else {
            Ident::Fresh
        }
    }
    fn map_symbol<X>(self, f: impl Fn(Symbol) -> X) -> X
    where
        Self: Sized + Symbolic,
    {
        self.get_symbol().pure(f)
    }
}

impl Identifier for Ident {
    fn is_upper(&self) -> bool {
        Ident::is_upper(&self)
    }
    fn is_lower(&self) -> bool {
        Ident::is_lower(&self)
    }
    fn is_fresh(&self) -> bool {
        Ident::is_fresh(&self)
    }
    fn is_infix(&self) -> bool {
        Ident::is_infix(&self)
    }
}

impl<Id> Identifier for Option<Id>
where
    Id: Identifier,
{
    fn is_upper(&self) -> bool {
        matches!(self, Some(id) if id.is_upper())
    }

    fn is_lower(&self) -> bool {
        matches!(self, Some(id) if id.is_lower())
    }

    fn is_infix(&self) -> bool {
        matches!(self, Some(id) if id.is_infix())
    }

    fn is_fresh(&self) -> bool {
        matches!(self, Some(id) if id.is_fresh())
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Ident {
    Upper(Symbol),
    Lower(Symbol),
    Infix(Symbol),
    /// Represent internally generated variables distinguishable from `Lower`
    /// variants, either for type variables or for parser/compiler generated
    /// variables.
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
        write!(
            f,
            "{}{}",
            if self.is_fresh() { "#" } else { "" },
            self.symbol()
        )
    }
}

impl Symbolic for Ident {
    fn get_symbol(&self) -> Symbol {
        self.symbol()
    }
}

wy_common::variants!(#((Symbol) Ident :Upper :Lower :Infix :Fresh));

impl Ident {
    pub const MAIN_MOD: Self = Ident::Upper(reserved::MAIN_MOD.symbol);
    pub const MAIN_FUN: Self = Ident::Lower(reserved::MAIN_FUN.symbol);
    pub const COLON: Self = Ident::Infix(reserved::COLON.symbol);
    pub const ARROW: Self = Ident::Infix(reserved::ARROW.symbol);
    pub const MINUS: Self = Ident::Infix(reserved::MINUS.symbol);
    pub const TRUE: Self = Ident::Upper(reserved::TRUE.symbol);
    pub const FALSE: Self = Ident::Lower(reserved::FALSE.symbol);
    pub const WILD: Self = Ident::Fresh(reserved::WILD.symbol);

    pub fn symbol(&self) -> Symbol {
        *self.get_inner()
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
    }

    /// Returns the constructor for the given `Ident` variant
    pub fn pure(&self) -> fn(Symbol) -> Self {
        match self {
            Ident::Upper(_) => Ident::Upper,
            Ident::Lower(_) => Ident::Lower,
            Ident::Infix(_) => Ident::Infix,
            Ident::Fresh(_) => Ident::Fresh,
        }
    }

    #[inline]
    pub fn minus_sign() -> Self {
        Self::MINUS
    }

    #[inline]
    pub fn cons_sign() -> Self {
        Self::COLON
    }

    #[inline]
    pub fn is_cons_sign(&self) -> bool {
        self == &Self::COLON
    }

    pub fn mk_tuple_commas(extras: usize) -> Self {
        Self::Infix(symbol::intern_once(
            &*(0..(extras + 1)).map(|_| ',').collect::<String>(),
        ))
    }

    pub fn with_suffix(self, suffix: Self) -> Chain<Self> {
        Chain(self, wy_common::deque!(suffix))
    }

    /// If an identifier's string form consists entirely of commas, then this
    /// returns the number of commas. Otherwise, it returns `None`.
    pub fn comma_count(&self) -> Option<usize> {
        if let Self::Infix(s) = self {
            symbol::lookup(*s).chars().fold(Some(0), |a, c| {
                a.and_then(|n| if c == ',' { Some(n + 1) } else { None })
            })
        } else {
            None
        }
    }
}

#[test]
fn test_idents() {
    let cons = Ident::cons_sign();
    let minus = Ident::minus_sign();
    let tuples = (0..5).map(Ident::mk_tuple_commas).collect::<Vec<_>>();
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

impl From<Chain<Ident>> for Ident {
    fn from(chain: Chain<Ident>) -> Self {
        chain.root().pure()(chain.canonicalize())
    }
}

impl From<&Chain<Ident>> for Ident {
    fn from(chain: &Chain<Ident>) -> Self {
        chain.root().pure()(chain.canonicalize())
    }
}

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

    /// This returns a reference to the last (right-most) identifier in the
    /// chain. If the chain is trivial, i.e., has only a head and not a tail,
    /// then this method returns the same thing as `root`, i.e., the first
    /// identifier.
    pub fn last(&self) -> &Id {
        self.1.iter().last().unwrap_or_else(|| &self.0)
    }

    /// Deconstructs into a tuple of its inner parts, returning a pair
    /// containing the root identifier along with a vector of tail identifiers.
    pub fn parts(self) -> (Id, Deque<Id>) {
        (self.0, self.1)
    }

    pub fn parts_cloned(&self) -> (Id, Deque<Id>)
    where
        Id: Clone,
    {
        (self.0.clone(), self.1.clone())
    }

    /// Returns the number of identifiers in the entire identifier chain.
    pub fn len(&self) -> usize {
        1 + self.1.len()
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
        std::iter::once(&self.0).chain(self.tail())
    }

    #[inline]
    pub fn any(&self, f: impl FnMut(&Id) -> bool) -> bool {
        self.iter().all(f)
    }

    pub fn contains(&self, id: &Id) -> bool
    where
        Id: PartialEq,
    {
        &self.0 == id || self.1.contains(id)
    }

    pub fn contains_root(&self, id: &Id) -> bool
    where
        Id: PartialEq,
    {
        &self.0 == id
    }

    pub fn contains_in_tail(&self, id: &Id) -> bool
    where
        Id: PartialEq,
    {
        self.1.contains(id)
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

    /// Analogous to `map`, but without taking ownership of `Self`.
    pub fn map_ref<F, Y>(&self, mut f: F) -> Chain<Y>
    where
        F: FnMut(&Id) -> Y,
    {
        let Chain(x, xs) = self;
        Chain(f(x), xs.iter().map(f).collect())
    }

    pub fn concat_right(self, rhs: Self) -> Self {
        let head = self.0;
        let mut tail = self.1;
        tail.push_back(rhs.0);
        tail.extend(rhs.1);
        Chain(head, tail)
    }

    pub fn add_prefix(&mut self, prefix: Id) {
        self.1.push_front(std::mem::replace(&mut self.0, prefix));
    }

    pub fn add_suffix(&mut self, suffix: Id) {
        self.1.push_back(suffix);
    }

    pub fn symbols(&self) -> impl Iterator<Item = Symbol> + '_
    where
        Id: Symbolic,
    {
        std::iter::once(self.0.get_symbol()).chain(self.tail().map(|id| id.get_symbol()))
    }

    pub fn into_string(&self) -> String
    where
        Id: std::fmt::Display,
    {
        format!("{}", self)
    }

    pub fn to_vec(self) -> Vec<Id> {
        std::iter::once(self.0).chain(self.1).collect()
    }

    pub fn write_to_string(&self, buf: &mut String)
    where
        Id: std::fmt::Display,
    {
        buf.push_str(&*(self.into_string()))
    }

    /// Takes the string representation of this `Chain` and interns it,
    /// returning the `Symbol` corresponding to the concatenated (dot-separated)
    /// identifier. Notice that this does NOT return an `Ident`: this is because
    /// the upper/lower distinction is lost at this level!
    pub fn canonicalize(&self) -> Symbol
    where
        Id: std::fmt::Display,
    {
        symbol::intern_once(&*(self.into_string()))
    }

    pub fn as_ident(&self) -> Ident
    where
        Id: Identifier + std::fmt::Display,
    {
        self.pure()(self.canonicalize())
    }
}

impl<Id, const N: usize> From<(Id, [Id; N])> for Chain<Id> {
    fn from((root, ids): (Id, [Id; N])) -> Self {
        let mut deque = deque!();
        deque.extend(ids);
        Chain(root, deque)
    }
}

impl<Id> From<(Id, Id)> for Chain<Id> {
    fn from((root, tail): (Id, Id)) -> Self {
        Chain(root, deque![tail])
    }
}

impl<Id> From<(Id, Id, Id)> for Chain<Id> {
    fn from((root, tail_a, tail_b): (Id, Id, Id)) -> Self {
        Chain(root, deque![tail_a, tail_b])
    }
}

impl<Id> PartialEq<Id> for Chain<Id>
where
    Id: PartialEq,
{
    fn eq(&self, other: &Id) -> bool {
        &self.0 == other && self.1.is_empty()
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

/// The categorization of a `Chain` depends on its last identifier, i.e., if
/// the last identifier in the chain is an infix, then the `Chain` is
/// categorized as an infix, etc.
impl<Id: Identifier> Identifier for Chain<Id> {
    fn is_upper(&self) -> bool {
        self.last().is_upper()
    }

    fn is_lower(&self) -> bool {
        self.last().is_lower()
    }

    fn is_infix(&self) -> bool {
        self.last().is_infix()
    }

    fn is_fresh(&self) -> bool {
        self.last().is_fresh()
    }
}
