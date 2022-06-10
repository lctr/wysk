use std::{collections::HashSet as Set, hash::Hash};

use wy_syntax::{
    decl::{Arity, DataDecl, Tag, Variant},
    ident::Ident,
    tipo::{Con, Context, Tv, Type},
};

use super::{
    envr::{ClassId, TyId},
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

    fn tv(&self) -> Vec<Tv> {
        self.tipo.tv()
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
pub fn dataty_ctors(data_decl: &DataDecl) -> (Type<Ident, Tv>, Vec<DataCon>) {
    let data_ty = Type::Con(
        Con::Data(data_decl.name),
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
        .map(
            |variant @ Variant {
                 name, tag, arity, ..
             }| DataCon {
                name,
                tag,
                arity,
                tipo: variant.fun_ty(data_ty.clone()),
            },
        )
        .collect::<Vec<_>>();
    (data_ty, ctors)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Class {
    pub(crate) name: Ident,
    pub(crate) methods: Vec<(Ident, TyId)>,
    pub(crate) vars: Vec<Tv>,
    pub(crate) ctxt: Vec<Context<ClassId, Tv>>,
}

wy_common::struct_field_iters! {
    Class
    | methods => methods_iter :: (Ident, TyId)
    | vars => vars_iter :: Tv
    | ctxt => ctxt_iter :: Context<ClassId, Tv>
}

wy_common::newtype! { usize in InstId | Show AsUsize (+) [Instance] }

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Instance {
    pub(crate) class: ClassId,
    pub(crate) tyid: TyId,
}

wy_common::newtype! { usize in ConId | Show AsUsize (+) [Constructor] }

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Datum {
    pub(crate) name: Ident,
    pub(crate) tyid: TyId,
    pub(crate) tag: Tag,
    pub(crate) arity: Arity,
}

#[cfg(test)]
mod tests {
    use wy_common::pretty::Dictionary;
    use wy_graph::{EdgeVisitor, Graph, NodeId};
    use wy_syntax::{
        stmt::{Binding, Match},
        visit::Visit,
    };

    use super::*;
    use std::collections::HashMap;

    #[test]
    fn inspect_prelude_constructors() {
        let mut map = HashMap::new();
        match wy_parser::parse_prelude() {
            Ok(program) => {
                program
                    .module
                    .map_t_ref(&mut |id| Tv::from(id))
                    .datatys_iter()
                    .for_each(|decl| {
                        let mut tyn = true;
                        decl.constructor_types().into_iter().for_each(|cons| {
                            let name = cons.name;
                            let vars = cons.var_map();
                            let tipo = cons.tipo.map_t_ref(&mut |tv| vars[tv]);
                            let mut vars = vars.into_iter().map(|(_k, v)| v).collect::<Vec<_>>();
                            vars.sort();
                            println!(
                                "{id} | {con} :: {var}{ty}",
                                id = if tyn {
                                    tyn = false;
                                    decl.name.to_string()
                                } else {
                                    std::iter::repeat(' ')
                                        .take(decl.name.to_string().len())
                                        .collect::<String>()
                                },
                                con = name,
                                var = if vars.is_empty() {
                                    String::new()
                                } else {
                                    {
                                        let mut s = String::new();
                                        s.push_str("forall");
                                        for v in &vars {
                                            s.push_str(&*format!(" {}", v));
                                        }
                                        s.push_str(" . ");
                                        s
                                    }
                                },
                                ty = &tipo
                            );
                            map.insert(name, tipo);
                        })
                    });
                println!("Constructors {}", Dictionary(&map))
            }
            Err(e) => {
                println!("{}", e)
            }
        }
    }

    fn visit_match(
        graph: &mut Graph<Ident>,
        bindings: &HashMap<Ident, NodeId>,
        Match {
            args: _,
            pred,
            body,
            wher,
        }: &Match,
        decl_name: &Ident,
    ) {
        if let Some(pred) = pred {
            EdgeVisitor {
                graph,
                map: bindings,
                node_id: bindings[decl_name],
            }
            .visit_expr(pred)
            .unwrap();
        }
        for Binding { name, arms, .. } in wher {
            for arm in arms {
                visit_match(graph, bindings, arm, name)
            }
        }
        EdgeVisitor {
            graph,
            map: bindings,
            node_id: bindings[decl_name],
        }
        .visit_expr(body)
        .unwrap();
    }

    #[test]
    fn test_bindings_graph() {
        let mut bindings = HashMap::new();
        let mut graph = Graph::new();
        match wy_parser::parse_prelude() {
            Ok(program) => {
                program
                    .module
                    .fundefs
                    .clone()
                    .into_iter()
                    .for_each(|fundecl| {
                        let idx = graph.add_node(fundecl.name);
                        bindings.insert(fundecl.name, idx);
                    });
                program.module.fundefs.clone().into_iter().for_each(|decl| {
                    decl.defs
                        .into_iter()
                        .for_each(|m| visit_match(&mut graph, &bindings, &m, &decl.name))
                });
                let sccs = graph.strongly_connected_components();
                println!("sccs: {:?}", &sccs);
                println!("graph: {:?}", &graph);
                println!("bindings: {:?}", &bindings);
                let sccs = sccs
                    .into_iter()
                    .map(|scc| scc.map(|node_id| &graph[node_id]).collect::<Vec<_>>())
                    .collect::<Vec<_>>();
                println!("sccs(2): {:#?}", &sccs)
            }
            Err(e) => println!("{}", e),
        }
    }
}
