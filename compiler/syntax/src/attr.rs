use wy_common::Mappable;

use crate::tipo::Type;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Attribute<Id, T> {
    Inline(Id),
    NoInline(Id),
    Specialize(Id, Vec<Type<Id, T>>),
}

impl<Id, T> Attribute<Id, T> {
    pub fn name(&self) -> &Id {
        match self {
            Attribute::Inline(id) | Attribute::NoInline(id) | Attribute::Specialize(id, _) => id,
        }
    }

    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> Attribute<X, T> {
        match self {
            Attribute::Inline(id) => Attribute::Inline(f(id)),
            Attribute::NoInline(id) => Attribute::NoInline(f(id)),
            Attribute::Specialize(id, tys) => {
                Attribute::Specialize(f(id), tys.fmap(|ty| ty.map_id(&mut f)))
            }
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> Attribute<X, T>
    where
        T: Copy,
    {
        match self {
            Attribute::Inline(id) => Attribute::Inline(f(id)),
            Attribute::NoInline(id) => Attribute::NoInline(f(id)),
            Attribute::Specialize(id, ty) => {
                Attribute::Specialize(f(id), ty.into_iter().map(|ty| ty.map_id_ref(f)).collect())
            }
        }
    }

    pub fn map_t<X>(self, mut f: impl FnMut(T) -> X) -> Attribute<Id, X> {
        match self {
            Attribute::Inline(id) => Attribute::Inline(id),
            Attribute::NoInline(id) => Attribute::NoInline(id),
            Attribute::Specialize(id, ts) => {
                Attribute::Specialize(id, ts.fmap(|ty| ty.map_t(&mut f)))
            }
        }
    }

    pub fn map_t_ref<X>(&self, f: &mut impl FnMut(&T) -> X) -> Attribute<Id, X>
    where
        Id: Copy,
    {
        match self {
            Attribute::Inline(id) => Attribute::Inline(*id),
            Attribute::NoInline(id) => Attribute::NoInline(*id),
            Attribute::Specialize(id, ts) => {
                Attribute::Specialize(*id, ts.into_iter().map(|ty| ty.map_t_ref(f)).collect())
            }
        }
    }
}
