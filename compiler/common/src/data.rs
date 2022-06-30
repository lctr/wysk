use crate::functor::Bifunctor;

pub trait Comparator<A> {
    fn compare(&self, other: &A) -> bool;
    fn compare_deref(&self, other: &impl std::ops::Deref<Target = A>) -> bool {
        self.compare(&*other)
    }
    fn compare_as_ref(&self, other: &impl AsRef<A>) -> bool {
        self.compare(other.as_ref())
    }
}

impl<A> Comparator<A> for A
where
    A: PartialEq,
{
    fn compare(&self, other: &A) -> bool {
        self == other
    }
}

impl<A> Comparator<A> for &[A]
where
    A: PartialEq,
{
    fn compare(&self, other: &A) -> bool {
        self.into_iter().any(|a| a == other)
    }
}

impl<A> Comparator<A> for [A]
where
    A: PartialEq,
{
    fn compare(&self, other: &A) -> bool {
        for a in self {
            if a == other {
                return true;
            }
        }
        false
    }
}

impl<A, const N: usize> Comparator<A> for [A; N]
where
    A: PartialEq,
{
    fn compare(&self, other: &A) -> bool {
        for a in self {
            if a == other {
                return true;
            }
        }
        false
    }
}

impl<A> Comparator<A> for fn(&A) -> bool {
    fn compare(&self, other: &A) -> bool {
        (self)(other)
    }
}

impl<A> Comparator<Option<A>> for A
where
    A: PartialEq,
{
    fn compare(&self, other: &Option<A>) -> bool {
        match other {
            Some(a) => a == self,
            None => false,
        }
    }
}

impl<A> Comparator<Option<&A>> for A
where
    A: PartialEq,
{
    fn compare(&self, other: &Option<&A>) -> bool {
        match other {
            Some(a) => a == &self,
            None => false,
        }
    }
}

/// A specialized iterator trait.
/// TODO: describe similarities and relationship with the `Iterator` trait
/// TODO: describe defining features of `Stream`s
///
pub trait Stream {
    type Item;
    type Halt: std::error::Error;
    type End: Comparator<Self::Item>;
    type Next: Bifunctor<Self::Item, Self::Halt>;
    const EOS: Self::End;
    fn peek(&mut self) -> &Self::Item;
    fn bump(&mut self) -> Self::Item;
    fn is_done(&mut self) -> bool {
        self.peek_on(Self::EOS)
    }
    fn peek_on(&mut self, item: impl Comparator<Self::Item>) -> bool {
        item.compare(self.peek())
    }
    fn bump_on(&mut self, item: impl Comparator<Self::Item>) -> bool {
        let test = self.peek_on(item);
        if test {
            self.bump();
        }
        test
    }
    fn bump_or_peek_on(
        &mut self,
        peek_item: impl Comparator<Self::Item>,
        bump_item: impl Comparator<Self::Item>,
    ) -> bool {
        let peeked = self.peek();
        if bump_item.compare(peeked) {
            self.bump();
            return true;
        }
        if peek_item.compare(peeked) {
            return true;
        }
        false
    }
    fn peek_or_bump_on(
        &mut self,
        peek_item: impl Comparator<Self::Item>,
        bump_item: impl Comparator<Self::Item>,
    ) -> bool {
        let peeked = self.peek();
        if peek_item.compare(peeked) {
            true
        } else if bump_item.compare(peeked) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn bump_while(&mut self, pred: impl Comparator<Self::Item>) -> Vec<Self::Item> {
        std::iter::from_fn(|| {
            if pred.compare(self.peek()) {
                Some(self.bump())
            } else {
                None
            }
        })
        .collect()
    }
    fn bump_until(&mut self, mut pred: impl FnMut(&mut Self) -> bool) -> Vec<Self::Item> {
        std::iter::from_fn(|| if !pred(self) { Some(self.bump()) } else { None }).collect()
    }
    fn expect(&mut self, item: impl Comparator<Self::Item>) -> Option<Self::Halt>;
    fn eat(&mut self, item: impl Comparator<Self::Item>) -> Result<Self::Item, Self::Halt> {
        if let Some(err) = self.expect(item) {
            Err(err)
        } else {
            Ok(self.bump())
        }
    }
    fn lookahead<const N: usize>(&mut self) -> [Self::Item; N];
}
