use std::collections::HashMap;
use std::hash::Hash;

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Scoped<K> {
    /// Used to delineate the boundaries of a collection of scoped items. When a
    /// new scope is created, and a stack of scoped items is being recorded,
    /// this variant is included before the addition of other scoped items. This
    /// ensures clear boundaries between clusters of scopes. Note that it is
    /// more efficient to wrap *keys* to a hashmap, or indices into a vector as
    /// scoped items.
    ///
    /// The sequence `Init, Local(k1), Local(k2), Local(k3)` indicates that a
    /// scope was entered, and three keys -- `k1`, `k2`, `k3` -- originate from
    /// said scope.
    Init,
    /// A "locally scoped" entity.
    Local(K),
}

impl<K> Scoped<K> {
    #[inline]
    pub fn is_init(&self) -> bool {
        matches!(self, Scoped::Init)
    }

    /// Checks whether this scoped item is a `Scoped::Local` variant. Equivalent
    /// to `!Scoped::is_init(scope)`.
    #[inline]
    pub fn has_data(&self) -> bool {
        matches!(self, Scoped::Local(_))
    }

    /// If the scope is a `Scoped::Local` variant (and hence holds some data,
    /// then a reference to it is returned in a `Some` variant. Otherwise this
    /// returns `None`.
    pub fn data(&self) -> Option<&K> {
        if let Scoped::Local(k) = self {
            Some(k)
        } else {
            None
        }
    }

    /// Checks whether the given data provided matches the data held by `Self`.
    /// If `Self` is a `Scoped::Init` variant, false is returned.
    pub fn cmp_data(&self, other: &K) -> bool
    where
        K: PartialEq,
    {
        matches!(self, Self::Local(k) if k == other)
    }

    /// Returns a new `Scoped` value holding a reference to the inner data held
    /// by `Self`.
    pub fn as_ref(&self) -> Scoped<&K> {
        match self {
            Scoped::Init => Scoped::Init,
            Scoped::Local(k) => Scoped::Local(k),
        }
    }

    /// Consumes the current instance of `Self`, applying a closure to the
    /// contained data (if any) and returning the result lifted into a `Scoped`
    /// type. If `Self` is a `Scoped::Init` variant, this method is effectively
    /// a no-op in that the same variant (but parameterized by the return type
    /// of the given closure) is returned.
    pub fn map<Y>(self, mut f: impl FnMut(K) -> Y) -> Scoped<Y> {
        match self {
            Scoped::Init => Scoped::Init,
            Scoped::Local(k) => Scoped::Local(f(k)),
        }
    }

    /// Applies a closure to a reference to the data held by `Self`, if any. If
    /// no data is held (i.e., `Self == Scoped::Init`, then `Scoped::Init` is
    /// returned as in `map`). Unlike `map`, this doesn't take ownership of
    /// `Self`.
    pub fn map_ref<Y>(&self, mut f: impl FnMut(&K) -> Y) -> Scoped<Y> {
        match self {
            Scoped::Init => Scoped::Init,
            Scoped::Local(k) => Scoped::Local(f(k)),
        }
    }

    /// Applies a closure to a mutable reference to the data held by `Self`, if
    /// any. If no data is held (i.e., `Self == Scoped::Init`, then this returns
    /// a `Scoped::Init` variant as in the other variations of this method).
    pub fn map_mut<Y>(&mut self, mut f: impl FnMut(&mut K) -> Y) -> Scoped<Y> {
        match self {
            Scoped::Init => Scoped::Init,
            Scoped::Local(k) => Scoped::Local(f(k)),
        }
    }

    /// Returns the change in depth provided by this scoped key.
    /// Functions as an identifier function for scopes, adding `1` if
    /// it marks the beginning of a scope and otherwise adding `0`.
    fn depth_incr(depth: usize, scoped: &Self) -> usize {
        if scoped.is_init() {
            depth
        } else {
            depth + 1
        }
    }
}

/// A `MapStack` struct is essentially a collection of stacked maps. With
/// stacked maps, it is possible to "extend" prior maps with new bindings,
/// potentially shadowing those defined in prior maps until removal.
#[derive(Debug)]
pub struct MapStack<K, V> {
    /// A map of *stacks* contains a vector of values for every inserted key.
    /// This vector of values functions as a stack of values, where the value
    /// returned for a given key is the *last element in the vector*, i.e., the
    /// "top" of the value stack.
    store: HashMap<K, Vec<V>>,
    /// A stack of "scopes". Since "scopes" are added and removed dynamically --
    /// that is, entered and exited -- we must be able to distinguish scope
    /// *breakpoints*, that is, track where scopes were added at the beginning
    /// of a given iteration. This is because it is possible for multiple scopes
    /// to be added in a single pass, and in order to remove these multiple
    /// scopes we must be able to tell where we added the first of said
    /// (potentially) multiple scopes.
    ///
    /// A scope may be "entered" and "exited". On "entering" a scope, we push
    /// the scope `Scoped::Init` to flag the most recent entry point.
    /// Afterwards, any bindings added to the `store` have their keys wrapped in
    /// a `Scoped::Local` variant. When exiting a scope, scoped keys are popped
    /// from this stack and removed from the map *until* encountering a
    /// `Scoped::Init` variant.
    scopes: Vec<Scoped<K>>,
}

impl<K, V> MapStack<K, V>
where
    K: Eq + Hash,
{
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
            scopes: Vec::new(),
        }
    }

    /// Returns the number of *keys* stored in the `store` field's map. As such,
    /// it does *not* take into account the number of values stored for each key
    /// (since it effectively takes the length of the hashmap held in
    /// `self.store`).
    pub fn len(&self) -> usize {
        self.store.len()
    }

    /// Returns the "depth" of the current scope, i.e., the number of *new
    /// scopes* have been added (including the current one), **starting from
    /// 0**.
    pub fn depth(&self) -> usize {
        self.scopes.iter().fold(0, Scoped::depth_incr)
    }

    /// Introduce a new scope. Upon entering a new scope, a `Scope::Init` is
    /// pushed onto the scopes stack to allow for any additionally appended
    /// scopes to be removed.
    pub fn enter_scope(&mut self) {
        self.scopes.push(Scoped::Init)
    }

    /// Exit the current scope, removing anything that's been inserted since the
    /// scope was entered
    pub fn exit_scope(&mut self) {
        while let Some(Scoped::Local(key)) = self.scopes.pop() {
            if let Some(vs) = self.store.get_mut(&key) {
                vs.pop();
            }
        }
    }

    /// Remove the most recently inserted value from the `store` for a given key
    /// as well as from the `scopes` stack. If the `store` contains the given
    /// key, the top of the stack of values in the corresponding entry is
    /// popped, and the list of scopes if traversed from the end towards the
    /// beginning, removing scoped keys that match the given one.
    ///
    /// Returns an optional pair containing the value removed and the number of
    /// scopes that were removed. Otherwise, if no scope contained the key,
    /// `None` is returned.
    pub fn remove(&mut self, k: &K) -> Option<(V, usize)> {
        match self.store.get_mut(k).and_then(Vec::pop) {
            Some(v) => {
                let len = self.scopes.len();
                // reminder that `retain` deletes all elements for which the
                // predicate returns false. since we want to delete all the
                // elements holding a matching key `k`, we use the negation of
                // calling `Scoped::cmp_data` (which itself is a utility method
                // for comparing with equality).
                self.scopes.retain(|scoped| !scoped.cmp_data(k));
                Some((v, len - self.scopes.len()))
            }
            None => None,
        }
    }

    /// Same as `remove`, but returning the value only and not the number of
    /// associated scopes that were removed.
    pub fn pop_top_val(&mut self, k: &K) -> Option<V> {
        self.remove(k).map(|(v, _)| v)
    }

    /// Checks whether a given key was added to the `store` from the current
    /// scope. This works by traversing the list of scopes from the end until
    /// a `Scoped::Local` variant with a matching key is found without
    /// encountering any `Scoped::Init` flags.
    ///
    /// For example, the following list describes the keys bound throughout
    /// __two__ scopes. The key `k1` was bound in the first scope, and the keys
    /// `k2` and `k3` were bound in the second scope. Since the second scope is
    /// the most recent scope in the list, calling this method on a `MapStack`
    /// with the following scopes would return `true` for keys `k2` and `k3`
    /// and `false` otherwise.
    ///
    /// ```rust,ignore
    /// [
    ///     // START OF FIRST SCOPE     => last one to go out of scope
    ///     Scoped::Init,
    ///     Scoped::Local(k1),
    ///     // START OF SECOND SCOPE
    ///     Scoped::Init,               => first one to go out of scope
    ///     Scoped::Local(k2),
    ///     Scoped::Local(k3)
    /// ]
    /// ```
    pub fn in_scope(&self, k: &K) -> bool {
        for scoped in self.scopes.iter().rev() {
            match scoped {
                Scoped::Init => break,
                Scoped::Local(key) if key == k => return true,
                _ => (),
            }
        }
        false
    }

    /// Returns an iterator over key-value pairs held by the inner `store`
    /// containing immutable references to keys and their corresponding stacks
    /// of values.
    #[inline]
    pub fn iter(&self) -> std::collections::hash_map::Iter<'_, K, Vec<V>> {
        self.store.iter()
    }

    /// Returns an iterator ove key-value pairs held by the inner `store`
    /// containing immutable references to the key with *mutable* references to
    /// each key's corresponding stack of values.
    #[inline]
    pub fn iter_mut(&mut self) -> std::collections::hash_map::IterMut<'_, K, Vec<V>> {
        self.store.iter_mut()
    }

    /// Returns a reference to a given key's *most recently stored* value. In
    /// other words, this returns a reference to the top of the stack of values
    /// for a given key. If no values were stored, `None` is returned.
    #[inline]
    pub fn get(&self, k: &K) -> Option<&V> {
        self.store.get(k).and_then(|vs| vs.last())
    }

    /// Returns a mutable reference to a given key's *most recently stored*
    /// value. In other words, this returns a mutable reference to the top of
    /// the stack of values for the given key. If no values were stored --
    /// either by the key not existing in the `store`, OR by its stack of vales
    /// being empty -- then `None` is returned.
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        self.store.get_mut(k).and_then(|vs| vs.last_mut())
    }

    /// **Note:** for keys that only implement `Clone` but not `Copy`, use the
    /// `inserted` method.
    ///
    /// Adds the given value to the stack of values corresponding to the given
    /// key. If the key does not exist in the `store`, then it will insert it
    /// and record the key in the `scopes` field.
    ///
    /// This method returns the number of elements stored for a given key
    /// *after* inserting the new value.
    pub fn insert(&mut self, k: K, v: V) -> usize
    where
        K: Copy,
    {
        let vals = self.bump(k);
        vals.push(v);
        vals.len()
    }

    #[inline]
    fn bump(&mut self, k: K) -> &mut Vec<V>
    where
        K: Copy,
    {
        self.store.entry(k).or_insert_with_key(|k| {
            self.scopes.push(Scoped::Local(*k));
            vec![]
        })
    }

    /// Equivalent to the `insert` method but for keys that only implement
    /// `Clone`.
    ///
    /// This method returns the number of elements stored for a given key
    /// *after* inserting the new value.
    pub fn inserted(&mut self, k: K, v: V) -> usize
    where
        K: Clone,
    {
        let vals = self.store.entry(k.clone()).or_insert({
            self.scopes.push(Scoped::Local(k));
            vec![]
        });
        vals.push(v);
        vals.len()
    }

    /// **Note:** for keys that only implement `Clone` and not copy, use the
    /// `swapped` method.
    ///
    /// Given a key and a value, if the key exists in the map held by `store`,
    /// this will replace the last value in the stack of values corresponding to
    /// the given key and return the old value. Otherwise, this will add the key
    /// to the map (as well as adding the scoped key to the list of scopes),
    /// placing the given value as the first element in the key's corresponding
    /// stack of values and return `None`.
    ///
    /// Note that the given key will also be added to the list of scoped keys if
    /// its stack of values exists but is empty.
    pub fn swap(&mut self, k: K, v: V) -> Option<V>
    where
        K: Copy,
    {
        let vals = self.store.entry(k).or_insert({
            self.scopes.push(Scoped::Local(k));
            vec![]
        });
        let old = vals.pop();
        vals.push(v);
        old
    }

    /// Equivalent to `swap` method for keys that implement `Clone` but not
    /// `Copy`.
    ///
    /// Given a key, if the `store` contains a non-empty stack of values, it
    /// will remove the last value in the stack, replacing it with the value
    /// given, and return the old value. Otherwise, if either the `store` did
    /// not contain an entry with the given key OR if the entry does exist but
    /// has an empty value stack, this will insert it into the map as well as
    /// recording the key, scoped, in the MapStack's `scopes` field.
    pub fn swapped(&mut self, k: K, v: V) -> Option<V>
    where
        K: Clone,
    {
        let vals = self.store.entry(k.clone()).or_insert({
            self.scopes.push(Scoped::Local(k));
            vec![]
        });
        let old = vals.pop();
        vals.push(v);
        old
    }
}
