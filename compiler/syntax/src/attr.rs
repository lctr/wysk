use serde::{Deserialize, Serialize};
use wy_common::functor::{MapFst, MapSnd};
// use wy_intern::Symbol;

pub use wy_lexer::{
    comment::{CommentId, LineKind},
    meta::Placement,
    Token,
};

use wy_span::Span;

use crate::{fixity::Fixity, tipo::Type};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Pragma<Id, V> {
    pub span: Span,
    pub plmt: Placement,
    pub attr: Attribute<Id, V>,
}

impl<Id, V, X> MapFst<Id, X> for Pragma<Id, V> {
    type WrapFst = Pragma<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        Pragma {
            span: self.span,
            plmt: self.plmt,
            attr: self.attr.map_fst(f),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Pragma<Id, V> {
    type WrapSnd = Pragma<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        Pragma {
            span: self.span,
            plmt: self.plmt,
            attr: self.attr.map_snd(f),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DocLine {
    pub id: CommentId,
    pub span: Span,
    pub line_kind: LineKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Attribute<Id, V> {
    Test,
    Todo,
    Inline,
    NoInline,
    Doc(DocLine),
    Fixity(Fixity),
    Derive(Vec<Id>),
    Specialize(Id, Vec<Type<Id, V>>),
    Custom(Id, Vec<Token>),
}

impl<Id, V, X> MapFst<Id, X> for Attribute<Id, V> {
    type WrapFst = Attribute<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Attribute::Test => Attribute::Test,
            Attribute::Todo => Attribute::Todo,
            Attribute::Inline => Attribute::Inline,
            Attribute::NoInline => Attribute::NoInline,
            Attribute::Doc(doc) => Attribute::Doc(doc),
            Attribute::Fixity(fixity) => Attribute::Fixity(fixity),
            Attribute::Derive(ids) => {
                Attribute::Derive(ids.into_iter().map(|id| f.apply(id)).collect())
            }
            Attribute::Specialize(id, tys) => Attribute::Specialize(f.apply(id), tys.map_fst(f)),
            Attribute::Custom(id, tokens) => Attribute::Custom(f.apply(id), tokens),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Attribute<Id, V> {
    type WrapSnd = Attribute<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Attribute::Test => Attribute::Test,
            Attribute::Todo => Attribute::Todo,
            Attribute::Inline => Attribute::Inline,
            Attribute::NoInline => Attribute::NoInline,
            Attribute::Doc(doc) => Attribute::Doc(doc),
            Attribute::Fixity(fixity) => Attribute::Fixity(fixity),
            Attribute::Derive(ids) => Attribute::Derive(ids),
            Attribute::Specialize(id, tys) => Attribute::Specialize(id, tys.map_snd(f)),
            Attribute::Custom(id, tokens) => Attribute::Custom(id, tokens),
        }
    }
}
