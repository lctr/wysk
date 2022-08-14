use wy_common::functor::{MapFst, MapSnd};
use wy_span::{Span, Spanned};

/// TODO: box/heap allocation optimization?
type Ptr<X> = Box<X>;

#[allow(non_snake_case)]
pub fn Ptr<T>(value: T) -> Ptr<T> {
    Box::new(value)
}

#[derive(Clone)]
pub struct Node<T, M = ()> {
    item: Ptr<T>,
    meta: M,
}

#[allow(non_snake_case)]
pub fn Node<T, M>(item: T, meta: M) -> Node<T, M> {
    Node::new(item, meta)
}

impl<T, M> Node<T, M> {
    pub fn new(item: T, meta: M) -> Self {
        Node {
            item: Ptr(item),
            meta,
        }
    }

    pub fn item(&self) -> &T {
        &self.item
    }

    pub fn item_mut(&mut self) -> &mut T {
        &mut self.item
    }

    pub fn parts(self) -> (T, M) {
        (*self.item, self.meta)
    }

    pub fn map<F, U>(self, f: F) -> Node<U, M>
    where
        F: FnOnce(T) -> U,
    {
        Node {
            item: Ptr(f(*self.item)),
            meta: self.meta,
        }
    }

    pub fn meta(&self) -> &M {
        &self.meta
    }

    pub fn meta_mut(&mut self) -> &mut M {
        &mut self.meta
    }
}

impl<T, M> std::ops::Deref for Node<T, M> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.item()
    }
}

impl<T, M> std::ops::DerefMut for Node<T, M> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.item_mut()
    }
}

impl<T: PartialEq, M> PartialEq for Node<T, M> {
    /// Only compares values in the `item` field, not the `meta` field.
    fn eq(&self, other: &Self) -> bool {
        self.item == other.item
    }
}

impl<T: Eq, M> Eq for Node<T, M> {}

impl<T: Ord, M> Ord for Node<T, M> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.item.cmp(&other.item)
    }
}

impl<T: PartialOrd, M> PartialOrd for Node<T, M> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.item.partial_cmp(&other.item)
    }
}

impl<T: std::fmt::Debug, M: std::fmt::Debug> std::fmt::Debug for Node<T, M> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if std::any::type_name::<M>() == "()" {
            write!(f, "{:#?}", &self.item)
        } else {
            write!(f, "{:#?} & {:?}", self.item, self.meta)
        }
    }
}

pub type SrcNode<T> = Node<T, Span>;

#[allow(non_snake_case)]
pub fn SrcNode<T>(Spanned(item, span): Spanned<T>) -> SrcNode<T> {
    Node::new(item, span)
}

impl<T> SrcNode<T> {
    pub fn span(&self) -> Span {
        self.meta
    }

    pub fn span_mut(&mut self) -> &mut Span {
        &mut self.meta
    }
}

impl<T> From<Spanned<T>> for SrcNode<T> {
    fn from(Spanned(item, span): Spanned<T>) -> Self {
        Node(item, span)
    }
}

impl<T> std::ops::Index<&SrcNode<T>> for str {
    type Output = str;

    fn index(&self, index: &SrcNode<T>) -> &Self::Output {
        assert!(index.span().contained_in(self));
        &self[index.span()]
    }
}

impl<T, M, X> MapFst<T, X> for Node<T, M> {
    type WrapFst = Node<X, M>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(T) -> X,
    {
        Node {
            item: Ptr(f.apply(*self.item)),
            meta: self.meta,
        }
    }
}

impl<T, M, X> MapSnd<M, X> for Node<T, M> {
    type WrapSnd = Node<T, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(M) -> X,
    {
        Node {
            item: self.item,
            meta: f.apply(self.meta),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_node_debug_doesnt_print_meta_when_unit() {
        let node = Node('x', ());
        let mut buf = String::new();
        std::fmt::write(&mut buf, format_args!("{node:?}")).unwrap();
        assert_eq!(buf.as_str(), "'x'")
    }
}
