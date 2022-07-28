use serde::{Deserialize, Serialize};
use wy_common::{iter::Hashable, HashMap, Map, Set};

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Record<Id, T> {
    /// Anonymous records don't have a *constructor* and are hence *extensible*,
    /// but less type-safe
    Anon(Vec<Field<Id, T>>),
    /// Records associated with a given *constructor* and hence are statially
    /// associated with that constructor's type.
    Data(Id, Vec<Field<Id, T>>),
}

impl<Id, T> Record<Id, T> {
    pub const VOID: Self = Self::Anon(vec![]);
    /// Returns `true` if the record contains no fields, *regardless* of
    /// `Record` variant. This is equivalent to calling `Record::len` and
    /// comparing it to `0`.
    pub fn is_empty(&self) -> bool {
        match self {
            Record::Anon(fields) | Record::Data(_, fields) => fields.is_empty(),
        }
    }

    pub fn has_rest(&self) -> bool {
        self.fields().into_iter().any(|fld| fld.is_rest())
    }

    pub fn has_repeated_keys(&self) -> bool
    where
        Id: Eq + std::hash::Hash,
    {
        let set: Set<&Id> = self.keys().collect();
        self.len() == set.len()
    }

    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Record::Anon(es) | Record::Data(_, es) => es.len(),
        }
    }

    pub fn to_pairs(self) -> Vec<(Id, T)> {
        match self {
            Record::Anon(kvs) | Record::Data(_, kvs) => kvs
                .into_iter()
                .filter_map(|fld| {
                    if let Field::Entry(k, v) = fld {
                        Some((k, v))
                    } else {
                        None
                    }
                })
                .collect(),
        }
    }

    /// Returns a slice of all the `Field`s contained by this `Record`. Note
    /// that this method *makes no distinction* regarding its *constructor*.
    pub fn fields(&self) -> &[Field<Id, T>] {
        match self {
            Record::Anon(fields) | Record::Data(_, fields) => fields.as_slice(),
        }
    }

    #[inline]
    pub fn keys(&self) -> impl Iterator<Item = &Id> + '_ {
        self.fields().iter().filter_map(|field| match field {
            Field::Rest => None,
            Field::Key(k) | Field::Entry(k, _) => Some(k),
        })
    }

    pub fn values(&self) -> impl Iterator<Item = &T> + '_ {
        self.fields().iter().filter_map(|field| match field {
            Field::Rest | Field::Key(_) => None,
            Field::Entry(_, v) => Some(v),
        })
    }

    #[inline]
    pub fn ctor(&self) -> Option<&Id> {
        match self {
            Record::Anon(_) => None,
            Record::Data(c, _) => Some(c),
        }
    }

    pub fn contains_key(&self, key: &Id) -> bool
    where
        Id: PartialEq,
    {
        self.keys().any(|id| id == key)
    }

    pub fn get(&self, key: &Id) -> Option<&T>
    where
        Id: PartialEq,
    {
        self.fields().into_iter().find_map(|field| {
            field
                .get_key()
                .and_then(|id| if id == key { field.get_value() } else { None })
        })
    }

    pub fn find(&self, pred: impl FnMut(&&Field<Id, T>) -> bool) -> Option<&Field<Id, T>>
    where
        Id: PartialEq,
        T: PartialEq,
    {
        self.fields().into_iter().find(pred)
    }

    pub fn into_hashmap(self) -> HashMap<Id, T>
    where
        Id: Hashable,
    {
        Hashable::hashmap_from(self.to_pairs())
    }

    /// Applies a transformation to the underlying components of a `Record`.
    /// Since a `Record` may or may not have a *constructor*, it follows that
    /// the kind of record *returned* will also depend on whether the first
    /// component of the tuple returned by the closure contains a `Some` variant
    /// or not. This means that it is possible to map from an `Record::Anon`
    /// variant to a `Record::Data` variant and vice-versa.
    pub fn map<F, U, V>(self, mut f: F) -> Record<U, V>
    where
        F: FnMut((Option<Id>, Vec<Field<Id, T>>)) -> (Option<U>, Vec<Field<U, V>>),
    {
        match self {
            Record::Anon(fields) => {
                let (_, fs) = f((None, fields));
                Record::Anon(fs)
            }
            Record::Data(con, fields) => {
                let (c, fs) = f((Some(con), fields));
                if let Some(ctor) = c {
                    Record::Data(ctor, fs)
                } else {
                    Record::Anon(fs)
                }
            }
        }
    }

    pub fn map_ref<U, V>(
        &self,
        f: &mut impl FnMut(Option<&Id>, &Vec<Field<Id, T>>) -> (Option<U>, Vec<Field<U, V>>),
    ) -> Record<U, V> {
        let (k, vs) = match self {
            Record::Anon(fields) => f(None, fields),
            Record::Data(k, v) => f(Some(k), v),
        };
        if let Some(con) = k {
            Record::Data(con, vs)
        } else {
            Record::Anon(vs)
        }
    }

    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> Record<X, T> {
        match self {
            Record::Anon(fs) => {
                Record::Anon(fs.into_iter().map(|fld| fld.map_id(|id| f(id))).collect())
            }
            Record::Data(k, vs) => Record::Data(
                f(k),
                vs.into_iter().map(|fld| fld.map_id(|id| f(id))).collect(),
            ),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> Record<X, T>
    where
        T: Copy,
    {
        match self {
            Record::Anon(fs) => Record::Anon(fs.iter().map(|fld| fld.map_id_ref(f)).collect()),
            Record::Data(k, vs) => {
                Record::Data(f(k), vs.iter().map(|fld| fld.map_id_ref(f)).collect())
            }
        }
    }

    pub fn map_t<U>(self, mut f: impl FnMut(T) -> U) -> Record<Id, U> {
        let mut entries = vec![];
        if let Record::Anon(es) = self {
            for field in es {
                match field {
                    Field::Rest => entries.push(Field::Rest),
                    Field::Key(k) => entries.push(Field::Key(k)),
                    Field::Entry(k, v) => entries.push(Field::Entry(k, f(v))),
                };
            }
            return Record::Anon(entries);
        } else if let Record::Data(k, vs) = self {
            for field in vs {
                match field {
                    Field::Rest => entries.push(Field::Rest),
                    Field::Key(k) => entries.push(Field::Key(k)),
                    Field::Entry(k, v) => entries.push(Field::Entry(k, f(v))),
                };
            }
            return Record::Data(k, entries);
        } else {
            unreachable!()
        }
    }

    pub fn map_t_ref<F, U>(&self, mut f: F) -> Record<Id, U>
    where
        F: FnMut(&T) -> U,
        Id: Clone,
    {
        match self {
            Record::Anon(es) => Record::Anon(iter_map_t_ref_field(&es[..], &mut |t| f(t))),
            Record::Data(k, v) => {
                Record::Data(k.clone(), iter_map_t_ref_field(&v[..], &mut |t| f(t)))
            }
        }
    }
}

fn iter_map_t_ref_field<X, Y, Z>(
    fields: &[Field<X, Y>],
    mut f: &mut impl FnMut(&Y) -> Z,
) -> Vec<Field<X, Z>>
where
    X: Clone,
{
    let mut fs = vec![];
    for field in fields {
        fs.push(field.map_t_ref(&mut f))
    }
    fs
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Field<Id, T> {
    /// Primarily used in partial records to indicate that a given record's list
    /// of fields is incomplete. Note that it is a syntactic error for this
    /// field to *not* be the last field in record's list of fields.
    Rest,
    /// A `Field` containing only a key. Depending on the syntactic context,
    /// this may correspond to "punning" of field labels, where the field
    /// `Field::Key(x)` is interpreted as an `Field::Entry(x, x')`, with `x'`
    /// being the result of some simple mapping `f :: Id -> T` applied to `x`.
    /// For *expressions*, this `f` is equivalent to `Expression::Ident`, while
    /// for *patterns* it corresponds to `Pattern::Var`.
    Key(Id),
    /// A (record) `Field` corresponding to a key-value pair of type `(Id, T)`.
    Entry(Id, T),
}

impl<Id, T> Field<Id, T> {
    pub fn is_rest(&self) -> bool {
        matches!(self, Self::Rest)
    }
    pub fn key_only(&self) -> bool {
        matches!(self, Self::Key(..))
    }
    pub fn get_key(&self) -> Option<&Id> {
        match self {
            Field::Rest => None,
            Field::Key(k) | Field::Entry(k, _) => Some(k),
        }
    }

    /// If the `Field` is an `Entry` variant, then this returns a reference to
    /// the held value, wrapped in `Option::Some`. Otherwise, this returns
    /// `None`.
    pub fn get_value(&self) -> Option<&T> {
        match self {
            Field::Rest | Field::Key(_) => None,
            Field::Entry(_, v) => Some(v),
        }
    }

    /// Expand a field consisting of only a key into a field where the value is
    /// the value-equivalent of the key, e.g., `{foo} -> { foo = foo }`.
    ///
    /// Since field types are generic, a function lifting the key into a value
    /// type must be provided.
    pub fn expand_key_shorthand(self, f: impl Fn(Id) -> T) -> Self
    where
        Id: Clone,
    {
        if let Self::Key(k) = self {
            Self::Entry(k.clone(), f(k))
        } else {
            self
        }
    }

    /// Returns `None` unless both lhs and rhs are present.
    pub fn as_pair(&self) -> Option<(&Id, &T)> {
        match self {
            Field::Rest => None,
            Field::Key(_) => None,
            Field::Entry(k, v) => Some((k, v)),
        }
    }

    pub fn map<F, U, X>(self, mut f: F) -> Field<U, X>
    where
        F: FnMut((Id, Option<T>)) -> (U, Option<X>),
    {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => match f((k, None)) {
                (a, None) => Field::Key(a),
                (a, Some(b)) => Field::Entry(a, b),
            },
            Field::Entry(k, v) => match f((k, Some(v))) {
                (a, None) => Field::Key(a),
                (a, Some(b)) => Field::Entry(a, b),
            },
        }
    }

    pub fn map_ref<U, X>(
        &self,
        f: &mut impl FnMut((&Id, Option<&T>)) -> (U, Option<X>),
    ) -> Field<U, X> {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => Field::Key(f((k, None)).0),
            Field::Entry(k, v) => match f((k, Some(v))) {
                (key, None) => Field::Key(key),
                (key, Some(val)) => Field::Entry(key, val),
            },
        }
    }

    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> Field<X, T> {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => Field::Key(f(k)),
            Field::Entry(k, v) => Field::Entry(f(k), v),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> Field<X, T>
    where
        T: Copy,
    {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => Field::Key(f(k)),
            Field::Entry(k, v) => Field::Entry(f(k), *v),
        }
    }

    pub fn map_t<F, U>(self, mut f: F) -> Field<Id, U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => Field::Key(k),
            Field::Entry(k, v) => Field::Entry(k, f(v)),
        }
    }

    pub fn map_t_ref<F, U>(&self, mut f: F) -> Field<Id, U>
    where
        F: FnMut(&T) -> U,
        Id: Clone,
    {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => Field::Key(k.clone()),
            Field::Entry(k, v) => Field::Entry(k.clone(), f(v)),
        }
    }
}
