use std::{collections::HashSet as Set, hash::Hash};

use wy_name::ident::Ident;
use wy_syntax::{
    decl::{Arity, DataDecl, Tag, Variant},
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

/// Generates function types corresponding to the constructors in a data
/// declaration. Note: this function assumes that data declarations have been
/// normalized to depend on `Tv` for type variables (i.e., `Type::Var`
/// instances).
pub fn data_constructors(data_decl: &DataDecl<Ident, Tv>) -> (Type<Ident, Tv>, Vec<DataCon>) {
    let data_ty = Type::Con(
        Con::Data(data_decl.name),
        data_decl.poly_iter().map(|tv| tv.as_type()).collect(),
    );
    let ctors = data_decl
        .variants_iter()
        .map(
            |variant @ Variant {
                 name, tag, arity, ..
             }| DataCon {
                name: *name,
                tag: *tag,
                arity: *arity,
                tipo: variant.fun_ty(data_ty.clone()),
            },
        )
        .collect::<Vec<_>>();
    (data_ty, ctors)
}

/// Rounds up all of a data type's constructors into a vector of structures
/// holding their types as functions. Note that this returns types with type
/// variables parametrized over the type `Tv`, unlike the (more general)
/// `Variant` method.
///
/// For the same functionality on `DataDecl<Ident, Tv>`, use the
/// `data_constructor` function.
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

    use std::collections::HashMap;

    fn visit_match<Id: Eq + std::hash::Hash, T>(
        graph: &mut Graph<T>,
        bindings: &HashMap<Id, NodeId>,
        Match {
            args: _,
            pred,
            body,
            wher,
        }: &Match<Id, T>,
        decl_name: &Id,
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
}
