use std::{
    collections::{hash_map, HashMap as Map, HashSet as Set},
    hash::Hash,
};

use wy_syntax::{
    ident::Ident,
    tipo::{Tv, Type},
    Arity, DataDecl, Program, Tag,
};

use super::{
    constraint::{Constraint, Scheme},
    error::Error,
    subst::{Subst, Substitutable},
};

#[derive(Clone, Debug, PartialEq, Eq)]
/// TODO: should this be polymorphic with respect to the type representation?
pub struct DataCon {
    pub tag: Tag,
    pub name: Ident,
    pub tipo: Type<Ident, Tv>,
    pub arity: Arity,
}

impl DataCon {
    /// If the data constructor's type is a function, return the return type of
    /// that function type. Otherwise, returns the type contained in the `tipo`
    /// field.
    pub fn ret_ty(&self) -> &Type<Ident, Tv> {
        let ty = &self.tipo;
        if let Type::Fun(_, y) = ty {
            y.as_ref()
        } else {
            ty
        }
    }

    pub fn is_nullary(&self) -> bool {
        // these should *always* match! if not, we've found a bug
        debug_assert_eq!(self.arity.is_zero(), self.tipo.is_nullary());
        self.tipo.is_nullary()
    }
}

impl Substitutable for DataCon {
    fn ftv(&self) -> Set<Tv> {
        self.tipo.ftv()
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        DataCon {
            tag: self.tag,
            name: self.name,
            arity: self.arity,
            tipo: self.tipo.apply_once(subst),
        }
    }
}

/// Rounds up all of a data type's constructors into a vector of structures
/// holding their types as functions. Note that this returns types with type
/// variables parametrized over the type `Tv`, unlike the (more general)
/// `Variant` method.
pub fn data_decl_ty(data_decl: &DataDecl) -> (Type<Ident, Tv>, Vec<DataCon>) {
    let data_ty = Type::Con(
        data_decl.name,
        data_decl
            .poly
            .iter()
            .copied()
            .map(Tv::from_ident)
            .map(Type::Var)
            .collect(),
    );
    let ctors = data_decl
        .vnts
        .clone()
        .into_iter()
        .map(|v| v.map_t(&mut Tv::from_ident))
        .map(|variant| DataCon {
            name: variant.name,
            tag: variant.tag,
            arity: variant.arity,
            tipo: variant.fun_ty(data_ty.clone()),
        })
        .collect::<Vec<_>>();
    (data_ty, ctors)
}

#[derive(Clone, Debug)]
pub struct Envr<K, V> {
    pub store: Map<K, V>,
}

impl<K, V> Envr<K, V>
where
    K: Eq + Hash,
{
    pub fn new() -> Self {
        Self { store: Map::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            store: Map::with_capacity(capacity),
        }
    }

    pub fn contains_key(&self, name: &K) -> bool {
        self.store.contains_key(name)
    }

    pub fn keys(&self) -> hash_map::Keys<'_, K, V> {
        self.store.keys()
    }

    pub fn get(&self, k: &K) -> Option<&V> {
        self.store.get(k)
    }

    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        self.store.get_mut(k)
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.store.insert(k, v)
    }

    pub fn remove(&mut self, k: &K) -> Option<V> {
        self.store.remove(k)
    }

    pub fn find<F>(&self, predicate: F) -> Option<(&K, &V)>
    where
        F: FnMut(&(&K, &V)) -> bool,
    {
        self.store.iter().find(predicate)
    }

    pub fn find_mut<F>(&mut self, predicate: F) -> Option<(&K, &mut V)>
    where
        F: FnMut(&(&K, &mut V)) -> bool,
    {
        self.store.iter_mut().find(predicate)
    }

    pub fn without(&self, k: &K) -> Self
    where
        K: Copy,
        V: Clone,
    {
        self.store
            .iter()
            .filter_map(|(id, v)| {
                if id == k {
                    Some((*id, v.clone()))
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn without_many(&self, ks: &[K]) -> Self
    where
        K: Copy,
        V: Clone,
    {
        self.store
            .iter()
            .filter_map(|(id, v)| {
                if ks.contains(id) {
                    None
                } else {
                    Some((*id, v.clone()))
                }
            })
            .collect()
    }

    pub fn iter(&self) -> hash_map::Iter<K, V> {
        self.store.iter()
    }

    pub fn iter_mut(&mut self) -> hash_map::IterMut<K, V> {
        self.store.iter_mut()
    }

    pub fn entry(&mut self, k: K) -> hash_map::Entry<K, V> {
        self.store.entry(k)
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for Envr<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Envr {
            store: iter.into_iter().collect::<Map<_, _>>(),
        }
    }
}

#[cfg(test)]
mod tests {
    use wy_graph::{EdgeVisitor, Graph};
    use wy_syntax::visit::Visit;

    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_thing() {
        let mut map = HashMap::new();
        let mut bindings = HashMap::new();
        let mut graph = Graph::new();
        match wy_parser::parse_prelude() {
            Ok(program) => {
                program
                    .module
                    .fundefs
                    .clone()
                    .into_iter()
                    .enumerate()
                    .for_each(|(idx, fundecl)| {
                        let idx = graph.add_node(idx);
                        bindings.insert(fundecl.name, idx);
                    });
                program.module.fundefs.clone().into_iter().for_each(|decl| {
                    decl.defs.into_iter().for_each(|m| {
                        if let Some(pred) = &m.pred {
                            EdgeVisitor {
                                graph: &mut graph,
                                map: &bindings,
                                node_id: bindings[&decl.name],
                            }
                            .visit_expr(pred)
                            .unwrap();
                        }
                        EdgeVisitor {
                            graph: &mut graph,
                            map: &bindings,
                            node_id: bindings[&decl.name],
                        }
                        .visit_expr(&m.body)
                        .unwrap();
                    })
                });
                program
                    .module
                    .datatys
                    .iter()
                    .map(|decl| data_decl_ty(&decl))
                    .for_each(|(_f, g)| {
                        g.into_iter().for_each(|datacon| {
                            let vars = datacon.tipo.enumerate().collect::<HashMap<Tv, Tv>>();
                            println!("{}", datacon.tipo.clone().map_t(&mut |tv| vars[&tv]));
                            map.insert(datacon.name, datacon.tipo);
                        })
                    });

                println!("{:#?}", &map)
            }
            Err(e) => {
                println!("{}", e)
            }
        }
    }
}
