use std::hash::Hash;

use wy_common::{iter::Envr, push_if_absent, Map, Mappable, Set};
use wy_syntax::{
    decl::{
        AliasDecl, Arity, ClassDecl, DataDecl, FnDecl, InstDecl, MethodDef, NewtypeArg,
        NewtypeDecl, Tag,
    },
    ident::Ident,
    stmt::Binding,
    tipo::{Con, Context, Tv},
    Program,
};

use super::{
    constraint::{Scheme, Type},
    data::{dataty_ctors, DataCon},
    error::{Error, Inferred},
    subst::{Subst, Substitutable},
    // unify::{Unifier, Unify},
};

impl<K: Copy + Eq + Hash, V> Substitutable for Envr<K, V>
where
    V: Substitutable,
{
    fn ftv(&self) -> wy_common::Set<wy_syntax::tipo::Tv> {
        self.values().flat_map(Substitutable::ftv).collect()
    }

    fn tv(&self) -> Vec<Tv> {
        self.values()
            .flat_map(Substitutable::tv)
            .fold(vec![], push_if_absent)
    }

    fn apply_once(&self, subst: &super::subst::Subst) -> Self
    where
        Self: Sized,
    {
        self.store
            .iter()
            .map(|(k, v)| (*k, v.apply_once(subst)))
            .collect()
    }
}

wy_common::newtype! { usize in TyId | New Show AsUsize (+) [Scheme] }

wy_common::newtype! { usize in ClassId | New Show AsUsize (+) [Class] }

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Class {
    name: Ident,
    methods: Vec<(Ident, TyId)>,
    vars: Vec<Tv>,
    ctxt: Vec<Context<ClassId, Tv>>,
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
    class: ClassId,
    tyid: TyId,
}

wy_common::newtype! { usize in ConId | Show AsUsize (+) [Constructor] }

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Datum {
    name: Ident,
    tyid: TyId,
    tag: Tag,
    arity: Arity,
}

#[derive(Debug)]
pub struct Environment {
    count: usize,
    /// Storing the types we've resolved as *type schemes*
    schemes: Vec<Scheme>,
    /// Data constructors and their raw type signatures
    /// TODO: remove from Engine, add to EngineBuilder
    constructors: Vec<Datum>,
    /// Contain each identifier's corresponding `TyId`
    globals: Envr<Ident, TyId>,
    /// Local bindings; *not* persistent!
    locals: Envr<Ident, Scheme>,
    classes: Vec<Class>,
    instances: Vec<Instance>,
}

wy_common::struct_field_iters! {
    Environment
    | schemes => schemes_iter :: Scheme
    | constructors => constructors_iter :: Datum
    | classes => classes_iter :: Class
    | instances => instances_iter :: Instance
}

impl Environment {
    pub fn new() -> Environment {
        Environment {
            count: 0,
            globals: Envr::new(),
            locals: Envr::new(),
            schemes: vec![],
            constructors: vec![],
            classes: vec![],
            instances: vec![],
        }
    }
    pub fn tick(&mut self) -> Tv {
        let ct = self.count;
        debug_assert!(u32::MAX as usize > ct);
        self.count += 1;
        Tv(ct as u32)
    }
    pub fn fresh(&mut self) -> Type {
        Type::Var(self.tick())
    }
    pub fn lookup_global(&self, ident: &Ident) -> Option<&Scheme> {
        self.globals.get(ident).map(|tyid| &self[*tyid])
    }
    pub fn has_local(&self, ident: &Ident) -> bool {
        self.locals.contains_key(ident)
    }
    pub fn lookup_local(&self, ident: &Ident) -> Option<&Scheme> {
        self.locals.get(ident)
    }

    pub fn get_local(&mut self, ident: &Ident) -> Inferred<Type> {
        let found = match (if ident.is_upper() {
            self.lookup_ctor(ident)
        } else {
            self.locals.get(ident)
        })
        .cloned()
        {
            Some(x) => Some(x),
            None => self.lookup_global(ident).cloned(),
        };

        if let Some(ref scheme) = found {
            Ok(self.instantiate(scheme))
        } else {
            Err(Error::Unbound(*ident))
        }
        // .map(|ref scheme| self.instantiate(scheme))
        // .ok_or_else(|| Error::Unbound(*ident))
    }

    /// Modify the current local environment in place, removing any entry for
    /// which the predicate returns `false`.
    pub fn retain_locals(&mut self, predicate: impl FnMut(&Ident, &mut Scheme) -> bool) {
        self.locals.retain(predicate)
    }

    pub fn reset_locals(&mut self) -> Envr<Ident, Scheme> {
        std::mem::replace(&mut self.locals, Envr::new())
    }

    pub fn has_ctor(&self, ident: &Ident) -> bool {
        self.constructors.iter().any(|ctor| ctor.name == *ident)
    }

    pub fn lookup_ctor(&self, ident: &Ident) -> Option<&Scheme> {
        self.constructors
            .iter()
            .find(|con| &con.name == ident)
            .map(|con| &self.schemes[con.tyid])
    }
    pub fn lookup_method(&self, ident: &Ident) -> Option<&Class> {
        self.classes
            .iter()
            .find(|class| class.methods.iter().any(|(cl, _)| cl == ident))
    }
    pub fn lookup_class(&self, ident: &Ident) -> Option<&Class> {
        self.classes.iter().find(|class| &class.name == ident)
    }
    pub fn lookup_class_instances(&self, class_name: &Ident) -> Option<Vec<Instance>> {
        if let Some(class) = self.lookup_class(class_name) {
            self.classes.iter().position(|cl| cl == class).map(|idx| {
                self.instances
                    .iter()
                    .filter(|instance| instance.class == ClassId(idx))
                    .map(|instance| *instance)
                    .collect()
            })
        } else {
            None
        }
    }
    pub fn instantiate(&mut self, scheme: &Scheme) -> Type {
        scheme.tipo.apply(
            &scheme
                .iter_tvs()
                .map(|v| (*v, self.fresh()))
                .collect::<Subst>(),
        )
    }
    pub fn generalize_with(environment: &impl Substitutable, ty: Type) -> Scheme {
        Scheme {
            poly: ty.ftv().difference(&environment.ftv()).copied().collect(),
            tipo: ty,
            ctxt: vec![],
        }
    }

    pub fn global_ftvs(&self) -> Set<Tv> {
        self.globals
            .values()
            .flat_map(|id| self[*id].ftv())
            .collect()
    }

    pub fn local_ftvs(&self) -> Set<Tv> {
        self.locals.ftv()
    }

    pub fn generalize_globally(&self, tipo: Type) -> Scheme {
        let poly = tipo
            .ftv()
            .difference(&self.global_ftvs())
            .copied()
            .collect::<Vec<_>>();

        let ctxt = vec![];

        Scheme { poly, tipo, ctxt }
    }

    pub fn generalize_locally(&self, tipo: Type) -> Scheme {
        Scheme {
            poly: tipo.ftv().difference(&self.local_ftvs()).copied().collect(),
            tipo,
            ctxt: vec![],
        }
    }

    pub fn lookup_scheme(&self, ident: &Ident) -> Result<&Scheme, Error> {
        if ident.is_upper() {
            self.constructors
                .iter()
                .find_map(|c| {
                    if c.name == *ident {
                        Some(&self[c.tyid])
                    } else {
                        None
                    }
                })
                .ok_or_else(|| Error::Unbound(*ident))
        } else if let Some(scheme) = self.locals.get(ident) {
            Ok(scheme)
        } else if let Some(tyid) = self.globals.get(ident) {
            Ok(&self[*tyid])
        } else {
            Err(Error::Unbound(*ident))
        }
    }

    pub fn add_scheme(&mut self, scheme: Scheme) -> TyId {
        let scheme = scheme.normalize();
        if let Some(pos) = self.schemes.iter().position(|sch| sch == &scheme) {
            TyId(pos)
        } else {
            let tyid = TyId(self.schemes.len());
            self.schemes.push(scheme);
            tyid
        }
    }

    pub fn insert_local(&mut self, name: Ident, scheme: Scheme) -> Option<Scheme> {
        self.locals.insert(name, scheme)
    }

    pub fn add_global(&mut self, ident: Ident, scheme: Scheme) -> TyId {
        let scheme = scheme.normalize();
        let tyid = if let Some(pos) = self.schemes.iter().position(|sch| sch == &scheme) {
            Some(TyId(pos))
        } else {
            None
        };
        if let Some(tyid) = tyid {
            self.globals.insert(ident, tyid);
            tyid
        } else {
            let tyid = TyId(self.schemes.len());
            self.schemes.push(scheme);
            self.globals.insert(ident, tyid);
            tyid
        }
    }

    pub fn canonicalize(tipo: Type) -> Scheme {
        Self::generalize_with(&Envr::<Ident, Scheme>::new(), tipo).normalize()
    }

    pub fn canonicalize_in(environment: &impl Substitutable, tipo: Type) -> Scheme {
        Self::generalize_with(environment, tipo).normalize()
    }

    pub fn canonicalize_with_locals(&self, tipo: Type) -> Scheme {
        self.generalize_locally(tipo).normalize()
    }

    pub fn canonicalize_with_globals(&self, tipo: Type) -> Scheme {
        self.generalize_globally(tipo).normalize()
    }
}

// impl Unify for Environment {
//     fn unifier(&self) -> &Unifier {
//         &self.unifier
//     }
//     fn unifier_mut(&mut self) -> &mut Unifier {
//         &mut self.unifier
//     }
// }

impl std::ops::Index<TyId> for Environment {
    type Output = Scheme;

    fn index(&self, index: TyId) -> &Self::Output {
        &self.schemes[index]
    }
}

impl std::ops::Index<ConId> for Environment {
    type Output = Datum;

    fn index(&self, index: ConId) -> &Self::Output {
        &self.constructors[index]
    }
}

impl std::ops::Index<InstId> for Environment {
    type Output = Instance;

    fn index(&self, index: InstId) -> &Self::Output {
        &self.instances[index]
    }
}

impl std::ops::Index<ClassId> for Environment {
    type Output = Class;

    fn index(&self, index: ClassId) -> &Self::Output {
        &self.classes[index]
    }
}

pub struct Builder {
    env: Environment,
    bindings: Vec<Binding<Ident, Tv>>,
}
impl Builder {
    pub fn new() -> Self {
        Self {
            env: Environment {
                count: 0,
                schemes: vec![],
                constructors: vec![],
                globals: Envr::new(),
                locals: Envr::new(),
                classes: vec![],
                instances: vec![],
            },
            bindings: Vec::new(),
        }
    }

    pub fn with_program(program: &Program) -> Environment {
        Self::new()
            .with_data_tys(program.get_datatys())
            .with_newtypes(program.get_newtyps())
            .with_classes(program.get_classes())
            .with_instances(program.get_implems())
            .with_fundefs(program.get_fundefs())
            .build()
    }

    pub fn with_fundefs(mut self, fundefs: &[FnDecl]) -> Self {
        let mut annot = Map::new();
        fundefs.into_iter().for_each(|decl| {
            let decl = decl.map_t_ref(&mut |t| Tv::from(t));
            let name = decl.name;
            if let Some(sign) = decl.sign.clone() {
                let ctxt = sign.ctxt_iter().map(|ctx| (ctx.class, ctx.tyvar)).collect();
                let scheme = Scheme::instance(sign.tipo, ctxt);
                let tyid = self.env.add_global(name, scheme);
                annot.insert(name, tyid);
            }
            let binding = Binding {
                name,
                arms: decl.defs,
                tipo: decl.sign,
            };
            self.bindings.push(binding)
        });
        self.env.globals.extend(annot);
        self
    }

    pub fn with_data_tys(mut self, data_decls: &[DataDecl]) -> Self {
        data_decls.into_iter().for_each(|decl| {
            let (dty, ctors) = dataty_ctors(decl);
            self.env.add_scheme(Scheme::polytype(dty).normalize());
            ctors.into_iter().for_each(
                |DataCon {
                     name,
                     tipo,
                     tag,
                     arity,
                 }| {
                    let scheme = Scheme::polytype(tipo).normalize();
                    let tyid = self.env.add_global(name, scheme);
                    self.env.constructors.push(Datum {
                        name,
                        tyid,
                        tag,
                        arity,
                    });
                },
            );
        });
        self
    }

    /// TODO: how to represent type aliases? How does that affect unification?
    /// MOVE OUT INTO SEPARATE PRE-PROCESS ON THE AST
    pub fn with_aliases(mut self, aliases: &[AliasDecl]) -> Self {
        aliases.into_iter().for_each(|alias| {
            let alias = alias.map_t_ref(&mut |id| Tv::from_ident(*id));
            let scheme = Scheme {
                poly: alias.poly,
                tipo: alias.sign.tipo,
                ctxt: vec![],
            };
            self.env.schemes.push(scheme);
        });
        self
    }

    pub fn with_classes(mut self, classes: &[ClassDecl]) -> Self {
        // will need to traverse the list of classes twice
        let mut contexts = Map::new();
        for class in classes {
            let id = ClassId(self.env.classes.len());
            let class_ = Class {
                name: class.name,
                vars: class.poly_iter().map(Tv::from).collect::<Vec<_>>(),
                methods: class
                    .methods_iter()
                    .map(
                        |MethodDef {
                             name,
                             sign,
                             body: _,
                         }| {
                            let tipo = sign.tipo.map_t_ref(&mut |id| Tv::from_ident(*id));
                            let ctxt = class
                                .poly_iter()
                                .map(Tv::from)
                                .map(|tv| (class.name, tv))
                                .collect();
                            let scheme = Scheme::instance(tipo, ctxt).normalize();
                            let tyid = self.env.add_global(*name, scheme);
                            (*name, tyid)
                        },
                    )
                    .collect(),
                ctxt: vec![],
            };
            self.env.classes.push(class_);
            contexts.insert(
                class.name,
                (
                    id,
                    class
                        .context_iter()
                        .map(|Context { class, tyvar }| Context {
                            class: *class,
                            tyvar: Tv::from_ident(*tyvar),
                        })
                        .collect::<Vec<_>>(),
                ),
            );
        }

        // now that we've "indexed" all classes, we can now get their respective
        // `ClassId`s and update existing class records to contain information
        // regarding their own constraints (= contexts for the class, NOT the
        // contexts found in the implementation of a class's instance(s)).
        for class in &mut self.env.classes {
            if let Some((cid, cxs)) = contexts.get(&class.name) {
                for c in cxs {
                    class.ctxt.push(Context {
                        class: *cid,
                        tyvar: c.tyvar,
                    });
                }
            }
        }
        self
    }

    pub fn with_instances(mut self, instances: &[InstDecl]) -> Self {
        for inst in instances {
            let InstDecl {
                name,
                tipo,
                ctxt,
                defs: _,
            } = inst;
            let sch = Scheme::instance(
                tipo.map_t_ref(&mut |t| Tv::from(t)),
                ctxt.iter()
                    .map(|ctx| (ctx.class, Tv::from_ident(ctx.tyvar)))
                    .collect(),
            )
            .normalize();
            if let Some(scid) = self.env.schemes.iter().position(|s| s == &sch) {
                if let Some(idx) = self.env.classes.iter().position(|cl| cl.name == *name) {
                    self.env.instances.push(Instance {
                        class: ClassId(idx),
                        tyid: TyId(scid),
                    });
                }
            }
        }

        self
    }

    pub fn with_newtypes(mut self, newtyps: &[NewtypeDecl]) -> Self {
        for newtype in newtyps {
            let NewtypeDecl {
                name,
                poly,
                ctor,
                narg,
                with: _,
            } = newtype.map_t_ref(&mut |id| Tv::from(id));
            match narg {
                NewtypeArg::Stacked(tys) => {
                    let arity = Arity(tys.len());
                    let tag = Tag(0);
                    let tyid = if tys.is_empty() {
                        self.env.add_global(
                            ctor,
                            Scheme::polytype(Type::Con(Con::Data(name), poly.fmap(Type::Var)))
                                .normalize(),
                        )
                    } else {
                        let scheme = Scheme::polytype(
                            tys.into_iter()
                                .chain([Type::Con(Con::Data(name), poly.fmap(Type::Var))])
                                .rev()
                                .reduce(|a, c| Type::Fun(Box::new(c), Box::new(a)))
                                .unwrap(),
                        )
                        .normalize();
                        self.env.add_global(ctor, scheme)
                    };
                    self.env.constructors.push(Datum {
                        name: ctor,
                        tyid,
                        tag,
                        arity,
                    });
                }
                NewtypeArg::Record(sel, sel_sig) => {
                    let sel_ty = sel_sig.tipo;
                    let the_ty = Type::Con(Con::Data(name), poly.fmap(Type::Var));
                    let _ty_sch = Scheme::polytype(the_ty.clone());

                    let the_sel = Type::mk_fun(the_ty.clone(), sel_ty.clone());
                    let con_ty = Type::mk_fun(sel_ty.clone(), the_ty);
                    let con_sch = Scheme::polytype(con_ty).normalize();
                    let _sel_sch = Scheme::polytype(the_sel).normalize();
                    let _sel_tyid = self.env.add_global(sel, _sel_sch);
                    let con_tyid = self.env.add_global(ctor, con_sch);

                    self.env.constructors.push(Datum {
                        name: ctor,
                        tyid: con_tyid,
                        tag: Tag(0),
                        arity: Arity(1),
                    })
                }
            }
        }
        self
    }

    pub fn build(self) -> Environment {
        self.env
    }

    pub fn from_program(program: &Program) -> Environment {
        Self::new()
            .with_data_tys(program.get_datatys())
            .with_aliases(program.get_aliases())
            .with_classes(program.get_classes())
            .with_instances(program.get_implems())
            .with_fundefs(program.get_fundefs())
            .build()
    }
}

#[cfg(test)]
mod tests {
    #![allow(unused)]
    use wy_parser::error::Parsed;
    use wy_syntax::tipo::Con;

    use crate::infer::constraint::Constraint;

    use super::*;

    fn two_fun_types() -> (Type, Type) {
        let bool_ = wy_intern::BOOL;
        let int_ = wy_intern::INT;
        let concrete = Type::Fun(
            Box::new(Type::Con(Con::Data(Ident::Upper(bool_)), vec![])),
            Box::new(Type::Con(Con::Data(Ident::Upper(int_)), vec![])),
        );
        let variable = Type::Fun(Box::new(Type::Var(Tv(0))), Box::new(Type::Var(Tv(1))));
        (variable, concrete)
    }

    fn with_program() -> Parsed<Environment> {
        match wy_parser::parse_prelude() {
            Ok(program) => {
                let _ = program
                    .module
                    .fundefs_iter()
                    .map(|f| f.map_t_ref(&mut |f| Tv::from(f)))
                    .collect::<Vec<_>>();
                let mut names = Map::new();
                let _ = program.map_id_ref(&mut |n| {
                    *names.entry(*n).or_insert(0) += 1;
                });
                println!("{:#?}", names);
                // println!("Ast: {:#?}", &program);
                let env = Builder::new()
                    .with_data_tys(program.get_datatys())
                    .with_aliases(program.get_aliases())
                    .with_classes(program.get_classes())
                    .with_instances(program.get_implems())
                    .build();
                Ok(env)
            }
            Err(err) => Err(err),
        }
    }
}
