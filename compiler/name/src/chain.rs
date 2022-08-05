use serde::{Deserialize, Serialize};
use wy_common::{deque, Deque};
use wy_intern::{Symbol, Symbolic};

use crate::ident::{Ident, Identifier};

/// Single wrapper for the parts comprising an identifier path (named `Chain` to
/// avoid ambiguity/similarity with relevant `Path` type(s)). A `Chain`
/// consists of a *root* identifier (or *head*) and a list of sequentially
/// suffixed identifiers, i.e., a *tail* set of identifiers.
///
/// The *root* of an identifier path is the first identifier in a
/// period-delimited chain of identifiers. Additionally, a chain of identifiers
/// may be *concatenated*.
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Chain<Id = Ident>(Id, Deque<Id>);

impl From<Chain<Ident>> for Ident {
    fn from(chain: Chain<Ident>) -> Self {
        chain.last().constructor()(chain.flattened_symbol())
    }
}

impl From<&Chain<Ident>> for Ident {
    fn from(chain: &Chain<Ident>) -> Self {
        chain.last().constructor()(chain.flattened_symbol())
    }
}

impl<Id> Chain<Id> {
    pub fn new(root: Id, tail: Deque<Id>) -> Self {
        Self(root, tail)
    }

    pub fn root(&self) -> &Id {
        &self.0
    }

    pub fn tail(&self) -> impl Iterator<Item = &Id> {
        self.1.iter()
    }

    pub fn mapf<F, X>(self, f: &mut wy_common::functor::Func<'_, F>) -> Chain<X>
    where
        F: FnMut(Id) -> X,
    {
        let Chain(root, tail) = self;
        let root = f.apply(root);
        let tail = tail.into_iter().map(|id| f.apply(id)).collect();
        Chain(root, tail)
    }

    /// This returns a reference to the last (right-most) identifier in the
    /// chain. If the chain is trivial, i.e., has only a head and not a tail,
    /// then this method returns the same thing as `root`, i.e., the first
    /// identifier.
    pub fn last(&self) -> &Id {
        self.1.iter().last().unwrap_or(&self.0)
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

    pub fn starts_with(&self, id: &Id) -> bool
    where
        Id: PartialEq,
    {
        &self.0 == id
    }

    pub fn ends_with(&self, id: &Id) -> bool
    where
        Id: PartialEq,
    {
        if self.1.is_empty() {
            &self.0 == id
        } else {
            self.1
                .iter()
                .last()
                .map(|last| last == id)
                .unwrap_or_else(|| false)
        }
    }

    pub fn contains_in_tail(&self, id: &Id) -> bool
    where
        Id: PartialEq,
    {
        self.1.contains(id)
    }

    pub fn get(&self, index: usize) -> Option<&Id> {
        if self.len() <= index {
            None
        } else if index == 0 {
            Some(self.root())
        } else {
            self.iter().nth(index)
        }
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

    /// Clones and returns the current `Chain` instance with the given prefix
    /// appended
    pub fn with_prefix(&self, prefix: Id) -> Self
    where
        Id: Clone,
    {
        let mut chain = self.clone();
        chain.add_prefix(prefix);
        chain
    }

    /// Clones and returns the current `Chain` instance with the given suffix
    /// appended
    pub fn with_suffix(&self, suffix: Id) -> Self
    where
        Id: Clone,
    {
        let mut chain = self.clone();
        chain.add_suffix(suffix);
        chain
    }

    /// Returns an iterator of `Symbol`s contained by each identifier in this
    /// chain.
    pub fn symbols(&self) -> impl Iterator<Item = Symbol> + '_
    where
        Id: Symbolic,
    {
        std::iter::once(self.0.get_symbol()).chain(self.tail().map(|id| id.get_symbol()))
    }

    /// Takes the string representation of this `Chain` and interns it,
    /// returning the `Symbol` corresponding to the concatenated (dot-separated)
    /// identifier. Notice that this does NOT return an `Ident`: this is because
    /// the upper/lower distinction is lost at this level!
    pub fn flattened_symbol(&self) -> Symbol
    where
        Id: Symbolic,
    {
        let mut buf = String::new();
        buf.push_str(self.root().get_symbol().as_str());

        for id in self.tail() {
            buf.push('.');
            buf.push_str(id.get_symbol().as_str());
        }

        Symbol::intern(buf)
    }

    pub fn as_ident(&self) -> Ident
    where
        Id: Identifier + Symbolic,
    {
        self.ident_constructor()(self.flattened_symbol())
    }

    pub fn from_strings<S: AsRef<str>, const N: usize>(head: S, strings: [S; N]) -> Chain<Symbol> {
        let root = wy_intern::intern_once(head.as_ref());
        let tail = wy_intern::intern_many(strings);
        Chain::from((root, tail))
    }

    pub fn from_strings_with<S: AsRef<str>, const N: usize>(
        head: S,
        strings: [S; N],
        mut f: impl FnMut(Symbol) -> Id,
    ) -> Self {
        let root = f(wy_intern::intern_once(head.as_ref()));
        let tail = wy_intern::intern_many_with(strings, f);
        Self::from((root, tail))
    }

    pub fn of_path_components<'p, P: AsRef<std::path::Path>>(
        p: &'p P,
    ) -> Chain<std::path::Component<'p>> {
        let mut parts = p.as_ref().components();
        let head = parts.next().unwrap_or(std::path::Component::CurDir);
        let tail = parts.collect::<Deque<_>>();
        Chain(head, tail)
    }
}

impl<Id> IntoIterator for Chain<Id> {
    type Item = Id;

    type IntoIter = std::iter::Chain<std::iter::Once<Id>, <Deque<Id> as IntoIterator>::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self.0).chain(self.1)
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

impl<Id> From<Chain<Chain<Id>>> for Chain<Id> {
    fn from(chain: Chain<Chain<Id>>) -> Self {
        let Chain(head, tail) = chain;
        let Chain(head, mut htail) = head;
        let tails = tail.into_iter().flatten().collect::<Deque<_>>();
        htail.extend(tails);
        Chain(head, htail)
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

impl<Id> std::fmt::Debug for Chain<Id>
where
    Id: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Chain(")
            .and(f.debug_list().entry(&self.0).entries(&self.1).finish())
            .and(f.write_str(")"))
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

/// Printer to display infix identifiers wrapped within parentheses
/// when within `Chain`s.
pub struct Chained<'id>(&'id Chain<Ident>);

impl<'id> Chained<'id> {
    #[inline]
    pub fn each(&self) -> impl Iterator<Item = &'id Ident> + '_ {
        self.0.iter()
    }
}

impl<'id> std::fmt::Display for Chained<'id> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (n, id) in self.each().enumerate() {
            if n > 0 {
                write!(f, ".")?;
            }
            if id.is_infix() {
                write!(f, "({})", id)?;
            } else {
                write!(f, "{}", id)?;
            }
        }
        Ok(())
    }
}

/// The categorization of a `Chain` depends on its last identifier, i.e., if
/// the last identifier in the chain is an infix, then the `Chain` is
/// categorized as an infix, etc.
impl<Id: Identifier + Symbolic> Identifier for Chain<Id> {
    fn is_upper(&self) -> bool {
        self.last().is_upper()
    }

    fn is_lower(&self) -> bool {
        self.last().is_lower()
    }

    fn is_infix(&self) -> bool {
        self.last().is_infix()
    }

    fn is_label(&self) -> bool {
        self.last().is_label()
    }

    fn is_fresh(&self) -> bool {
        self.last().is_fresh()
    }

    fn get_ident(&self) -> Ident {
        self.as_ident()
    }
}
