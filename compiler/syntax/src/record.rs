use serde::{Deserialize, Serialize};
use wy_common::{iter::Hashable, HashMap, Set};

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Record<Id, V> {
    /// Anonymous records don't have a *constructor* and are hence
    /// *extensible*, but less type-safe. They are currently not
    /// supported!
    Anon(Vec<Field<Id, V>>),
    /// Records associated with a given *constructor* and hence are statially
    /// associated with that constructor's type.
    Data(Id, Vec<Field<Id, V>>),
}

impl<Id, V> Record<Id, V> {
    pub const VOID: Self = Self::Anon(vec![]);
    /// Returns `true` if the record contains no fields, *regardless* of
    /// `Record` variant. This is equivalent to calling `Record::len` and
    /// comparing it to `0`.
    pub fn is_empty(&self) -> bool {
        match self {
            Record::Anon(fields) | Record::Data(_, fields) => fields.is_empty(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Record::Anon(es) | Record::Data(_, es) => es.len(),
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

    pub fn to_pairs(self) -> Vec<(Id, V)> {
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
    pub fn fields(&self) -> &[Field<Id, V>] {
        match self {
            Record::Anon(fields) | Record::Data(_, fields) => fields.as_slice(),
        }
    }

    pub fn fields_mut(&mut self) -> &mut [Field<Id, V>] {
        match self {
            Record::Anon(fields) | Record::Data(_, fields) => fields.as_mut_slice(),
        }
    }

    #[inline]
    pub fn keys(&self) -> impl Iterator<Item = &Id> + '_ {
        self.fields().into_iter().filter_map(|field| match field {
            Field::Rest => None,
            Field::Key(k) | Field::Entry(k, _) => Some(k),
        })
    }

    pub fn keys_mut(&mut self) -> impl Iterator<Item = &mut Id> + '_ {
        self.fields_mut()
            .into_iter()
            .filter_map(|field| match field {
                Field::Rest => None,
                Field::Key(k) | Field::Entry(k, _) => Some(k),
            })
    }

    pub fn values(&self) -> impl Iterator<Item = &V> + '_ {
        self.fields().into_iter().filter_map(|field| match field {
            Field::Rest | Field::Key(_) => None,
            Field::Entry(_, v) => Some(v),
        })
    }

    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> + '_ {
        self.fields_mut()
            .into_iter()
            .filter_map(|field| match field {
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

    pub fn get(&self, key: &Id) -> Option<&V>
    where
        Id: PartialEq,
    {
        self.fields().into_iter().find_map(|field| {
            field
                .get_key()
                .and_then(|id| if id == key { field.get_value() } else { None })
        })
    }

    pub fn find(&self, pred: impl FnMut(&&Field<Id, V>) -> bool) -> Option<&Field<Id, V>>
    where
        Id: PartialEq,
        V: PartialEq,
    {
        self.fields().into_iter().find(pred)
    }

    pub fn into_hashmap(self) -> HashMap<Id, V>
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
    pub fn map<F, A, B>(self, mut f: F) -> Record<A, B>
    where
        F: FnMut((Option<Id>, Vec<Field<Id, V>>)) -> (Option<A>, Vec<Field<A, B>>),
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
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Field<Id, V> {
    /// Primarily used in partial records to indicate that a given record's list
    /// of fields is incomplete. Note that it is a syntactic error for this
    /// field to *not* be the last field in record's list of fields.
    Rest,
    /// A `Field` containing only a key. Depending on the syntactic context,
    /// this may correspond to "punning" of field labels, where the field
    /// `Field::Key(x)` is interpreted as an `Field::Entry(x, x')`, with `x'`
    /// being the result of some simple mapping `f :: Id -> V` applied to `x`.
    /// For *expressions*, this `f` is equivalent to `Expression::Ident`, while
    /// for *patterns* it corresponds to `Pattern::Var`.
    Key(Id),
    /// A (record) `Field` corresponding to a key-value pair of type `(Id, V)`.
    Entry(Id, V),
}

impl<Id, V> Field<Id, V> {
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

    pub fn get_key_mut(&mut self) -> Option<&mut Id> {
        match self {
            Field::Rest => None,
            Field::Key(k) | Field::Entry(k, _) => Some(k),
        }
    }

    /// If the `Field` is an `Entry` variant, then this returns a reference to
    /// the held value, wrapped in `Option::Some`. Otherwise, this returns
    /// `None`.
    pub fn get_value(&self) -> Option<&V> {
        match self {
            Field::Rest | Field::Key(_) => None,
            Field::Entry(_, v) => Some(v),
        }
    }

    pub fn get_value_mut(&self) -> Option<&V> {
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
    pub fn expand_key_shorthand(self, f: impl FnOnce(Id) -> V) -> Self
    where
        Id: Clone,
    {
        if let Self::Key(k) = self {
            Self::Entry(k.clone(), f(k))
        } else {
            self
        }
    }

    pub fn map<F, A, B>(self, mut f: F) -> Field<A, B>
    where
        F: FnMut((Id, Option<V>)) -> (A, Option<B>),
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
}
