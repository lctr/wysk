use wy_common::functor::{MapFst, MapSnd};

use crate::tipo::Type;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Attribute<Id, V> {
    Inline(Id),
    NoInline(Id),
    Specialize(Id, Vec<Type<Id, V>>),
}

impl<Id, V> Attribute<Id, V> {
    pub fn name(&self) -> &Id {
        match self {
            Attribute::Inline(id) | Attribute::NoInline(id) | Attribute::Specialize(id, _) => id,
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Attribute<Id, V> {
    type WrapFst = Attribute<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Attribute::Inline(id) => Attribute::Inline(f.apply(id)),
            Attribute::NoInline(id) => Attribute::NoInline(f.apply(id)),
            Attribute::Specialize(id, tys) => Attribute::Specialize(f.apply(id), tys.map_fst(f)),
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
            Attribute::Inline(id) => Attribute::Inline(id),
            Attribute::NoInline(id) => Attribute::NoInline(id),
            Attribute::Specialize(id, tys) => Attribute::Specialize(id, tys.map_snd(f)),
        }
    }
}
