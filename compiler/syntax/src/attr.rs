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
}
