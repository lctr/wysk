use serde::{Deserialize, Serialize};
use wy_common::{Mappable, Set};
use wy_name::ident::Ident;

use crate::{decl::Arity, expr::Expression, pattern::Pattern, tipo::Signature};

/// ```wysk
///     fn foo :: Int -> Int -> Bool
/// ~~> Match[0]
/// ~~|  `args`
/// ~~|   vvv
///     | x y if x > y = True
/// ~~:       ^^^^^^^^   ^^^^
/// ~~:        `pred`   `body`
/// ~~> Match[1]
/// ~~|  `args`
/// ~~|   vvv
///     | x y = False && u where u = x + y > 0
/// ~~:   ^^^   ^^^^^^^^^^ ^^^^^^^^^^^^^^^^^^^
/// ~~: `args`    `body`         `wher[0]`
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Match<Id, T> {
    pub args: Vec<Pattern<Id, T>>,
    pub pred: Option<Expression<Id, T>>,
    pub body: Expression<Id, T>,
    pub wher: Vec<Binding<Id, T>>,
}

pub type RawMatch = Match<Ident, Ident>;

wy_common::struct_field_iters! {
    |Id, T| Match<Id, T>
    | args => args_iter :: Pattern<Id, T>
    | wher => wher_iter :: Binding<Id, T>
}

impl<Id, T> Match<Id, T> {
    /// A trivial match consists of only an expression, with the `args` and
    /// `where` fields empty vectors and `pred` a default `None`.
    pub fn trivial(body: Expression<Id, T>) -> Self {
        Self {
            args: vec![],
            pred: None,
            body,
            wher: vec![],
        }
    }
    pub fn caf(body: Expression<Id, T>, wher: Vec<Binding<Id, T>>) -> Self {
        Self {
            args: vec![],
            pred: None,
            body,
            wher,
        }
    }
    pub fn arity(&self) -> Arity {
        Arity(self.args.len())
    }

    pub fn pred_iter(&self) -> std::option::Iter<Expression<Id, T>> {
        self.pred.iter()
    }

    pub fn bound_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        let mut ids = Set::new();
        self.args_iter().for_each(|pat| ids.extend(pat.binders()));
        self.pred_iter().for_each(|x| ids.extend(x.bound_vars()));
        ids.extend(self.body.bound_vars());
        self.wher_iter().for_each(|b| ids.extend(b.bound_vars()));
        ids
    }

    pub fn free_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        let mut vars = Set::new();
        vars.extend(self.body.free_vars());
        if let Some(pred) = &self.pred {
            vars.extend(pred.free_vars());
        }
        self.wher_iter().for_each(|binding| {
            vars.extend(binding.free_vars());
        });
        self.args_iter().for_each(|pat| {
            pat.idents().into_iter().for_each(|id| {
                vars.remove(id);
            })
        });
        vars
    }
    pub fn map_id<X>(self, f: &mut impl FnMut(Id) -> X) -> Match<X, T> {
        Match {
            args: self.args.fmap(|pat| pat.map_id(f)),
            pred: self.pred.map(|ex| ex.map_id(f)),
            body: self.body.map_id(f),
            wher: self.wher.fmap(|bnd| bnd.map_id(f)),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> Match<X, T>
    where
        T: Copy,
    {
        Match {
            args: self.args.iter().map(|pat| pat.map_id_ref(f)).collect(),
            pred: self.pred.as_ref().map(|x| x.map_id_ref(f)),
            body: self.body.map_id_ref(f),
            wher: self.wher.iter().map(|bnd| bnd.map_id_ref(f)).collect(),
        }
    }

    pub fn map_t<U>(self, f: &mut impl FnMut(T) -> U) -> Match<Id, U> {
        fn iters<A>(vec: &mut Vec<A>, f: impl FnOnce() -> A) {
            let it = f();
            vec.push(it);
        }
        Match {
            args: {
                let mut args = vec![];
                for a in self.args {
                    iters(&mut args, || a.map_t(f));
                }
                args
            },
            pred: match self.pred {
                None => None,
                Some(x) => {
                    let mut it = vec![];
                    iters(&mut it, || x.map_t(f));
                    it.pop()
                }
            },
            body: {
                let mut it = vec![];
                iters(&mut it, || self.body.map_t(f));
                it.pop().unwrap()
            },
            wher: {
                let mut args = vec![];
                for Binding {
                    name,
                    arms: arms_,
                    tipo,
                } in self.wher
                {
                    let mut arms = vec![];
                    for arm in arms_ {
                        iters(&mut arms, || arm.map_t(f));
                    }
                    args.push(Binding {
                        name,
                        arms,
                        tipo: tipo.map(|s| s.map_t(f)),
                    });
                }
                args
            },
        }
    }
    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Match<Id, U>
    where
        Id: Copy,
    {
        Match {
            args: self.args_iter().map(|a| a.map_t_ref(f)).collect(),
            pred: if let Some(p) = &self.pred {
                Some(p.map_t_ref(f))
            } else {
                None
            },
            body: self.body.map_t_ref(f),
            wher: self.wher_iter().map(|w| w.map_t_ref(f)).collect(),
        }
    }
}

/// Pattern matching over a function definition
/// ```wysk
/// fn null :: [a] -> Bool
/// | [] = True
/// | _ = False;
/// ```
/// can be simplified to a `case` expression
/// ```wysk
/// fn null :: [a] -> Bool
/// | xs = case xs of
/// ~~> Alternative[0]
/// ~~|  `pat`
/// ~~|   vv
///     | [] -> True
/// ~~> Alternative[1]
/// ~~|  `pat`
/// ~~|   |  `pred`      `body`
/// ~~|   v vvvvvvvvv    vvvvv
///     | _ if t || u -> False
///         where t = True;
/// ~~:           ^^^^^^^^ `wher[0]`
///               u = False;
/// ~~:           ^^^^^^^^^ `wher[1]`
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Alternative<Id, T> {
    pub pat: Pattern<Id, T>,
    pub pred: Option<Expression<Id, T>>,
    pub body: Expression<Id, T>,
    pub wher: Vec<Binding<Id, T>>,
}

pub type RawAlternative = Alternative<Ident, Ident>;

wy_common::struct_field_iters! {
    |Id, T| Alternative<Id, T>
    | wher => wher_iter :: Binding<Id, T>
}

impl<Id, T> Alternative<Id, T> {
    pub fn pred_iter(&self) -> std::option::Iter<Expression<Id, T>> {
        self.pred.iter()
    }

    pub fn where_binder_names(&self) -> impl Iterator<Item = &Id> + '_ {
        self.wher_iter().map(|b| b.get_name())
    }

    /// Returns a vector of references to all the newly bound identifiers
    /// introduced in the match arm patterns
    pub fn binders(&self) -> Vec<&Id>
    where
        Id: PartialEq,
    {
        self.pat.binders()
    }

    pub fn idents(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        self.pat
            .idents()
            .into_iter()
            .chain(self.pred.as_ref().into_iter().flat_map(Expression::idents))
            .chain(self.body.idents())
            .chain(self.wher_iter().flat_map(Binding::idents))
            .collect()
    }

    pub fn free_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        let mut vars = self.body.free_vars();
        if let Some(pred) = &self.pred {
            vars.extend(pred.free_vars());
        }
        self.wher_iter().for_each(|binding| {
            vars.insert(binding.get_name());
            vars.extend(binding.free_vars())
        });
        self.pat.idents().into_iter().for_each(|id| {
            vars.remove(id);
        });
        vars
    }

    pub fn map_id<X>(self, f: &mut impl FnMut(Id) -> X) -> Alternative<X, T> {
        let Alternative {
            pat,
            pred,
            body,
            wher,
        } = self;
        Alternative {
            pat: pat.map_id(f),
            pred: pred.map(|x| x.map_id(f)),
            body: body.map_id(f),
            wher: wher.into_iter().map(|b| b.map_id(f)).collect(),
        }
    }

    pub fn map_id_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> Alternative<U, T>
    where
        T: Copy,
    {
        Alternative {
            pat: self.pat.map_id_ref(f),
            pred: self.pred.as_ref().map(|ex| ex.map_id_ref(f)),
            body: self.body.map_id_ref(f),
            wher: self.wher_iter().map(|w| w.map_id_ref(f)).collect(),
        }
    }

    pub fn map_t<F, U>(self, mut f: F) -> Alternative<Id, U>
    where
        F: FnMut(T) -> U,
        Id: Copy,
    {
        let Alternative {
            pat,
            pred,
            body,
            wher,
        } = self;
        let pat = pat.map_t(&mut f);
        let pred = pred.map(|x| x.map_t(&mut |t| f(t)));
        let body = body.map_t(&mut |t| f(t));
        let wher = wher.into_iter().map(|b| b.map_t(&mut f)).collect();
        Alternative {
            pat,
            pred,
            body,
            wher,
        }
    }

    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Alternative<Id, U>
    where
        Id: Copy,
    {
        Alternative {
            pat: self.pat.map_t_ref(f),
            pred: if let Some(pred) = &self.pred {
                Some(pred.map_t_ref(f))
            } else {
                None
            },
            body: self.body.map_t_ref(f),
            wher: self.wher.iter().map(|b| b.map_t_ref(f)).collect(),
        }
    }
}

/// ```wysk
/// ~{
///       `name`
///         |          `tipo`   
///         v     vvvvvvvvvvvvvvvv
/// }~  fn foo :: a -> b -> (a, b)
///     | x y = (x, y);
/// ~~: ^^^^^^^^^^^^^^ `arms[0]`
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Binding<Id, T> {
    pub name: Id,
    pub arms: Vec<Match<Id, T>>,
    pub tipo: Option<Signature<Id, T>>,
}

pub type RawBinding = Binding<Ident, Ident>;

wy_common::struct_field_iters! {
    |Id, T| Binding<Id, T>
    | arms => arms_iter :: Match<Id, T>
}

impl<Id, T> Binding<Id, T> {
    /// Returns a reference to the `name` of the binding.
    pub fn get_name(&self) -> &Id {
        &self.name
    }

    /// A simple binding is one with a single 0-arity `Match` arm (i.e, no
    /// argument patterns).
    /// Note that it is an error for a `Binding` to have more than one
    /// zero-arity match arms!
    pub fn is_simple(&self) -> bool {
        self.arms.len() == 1 && self.arms[0].arity().is_zero()
    }

    /// Returns the arity of a binding if all of its match arms contain the same
    /// number of patterns.
    ///
    /// Every match arm should contain the SAME number of OUTER patterns. For
    /// example, the following function declaration has 3 match arms, each with
    /// 2 *outer* patterns and thus would satisfy what this method checks for.
    ///
    /// ```wysk
    /// fn filter :: (a -> Bool) -> [a] -> [a]
    /// | f [] = []
    /// ~~ pattern match and apply predicate to head
    /// ~~ notice that we have TWO external patterns
    /// ~~ the 2nd pattern has 2 subpatterns and that's fine
    /// | f (x:xs) if f x = x : filter f xs
    /// ~~ otherwise we know `f x` is `False` so we move on
    /// | f (_:xs) = filter f xs
    /// ```
    ///
    /// The following has match arms with varying outer patterns. This is
    /// treated as a syntax -- and hence compile-time -- error.
    pub fn maybe_arity(&self) -> Option<Arity> {
        // all bindings must have at least *one* match arm! the parser *should*
        // reject empty bindings, but we add this assertion here anyway.
        assert!(self.arms.len() > 0, "binding has no match arms");
        // since we **must** have a non-zero number of arms, calling reduce
        // should always return a `Some` variant!
        self.arms_iter()
            .map(|m| Some(m.arity()))
            .reduce(|acc, curr| {
                acc.and_then(|a| curr.and_then(|c| if a == c { Some(a) } else { None }))
            })
            .unwrap()
    }

    /// Returns a vector of references to the identifiers bound by the binding's
    /// argument patterns, i.e., the flattened collection of all identifiers
    /// introduced within the `args` field of each contained `Match` in the
    /// `Binding`'s `arms` field.
    pub fn binders(&self) -> Vec<&Id>
    where
        Id: PartialEq,
    {
        let mut vars = vec![];
        self.arms_iter().for_each(|m| {
            m.args_iter().for_each(|p| {
                p.binders().into_iter().for_each(|id| {
                    if vars.contains(&id) {
                        vars.push(id);
                    }
                })
            })
        });
        vars
    }

    pub fn idents(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        let mut idents = Set::new();
        idents.insert(self.get_name());
        self.arms_iter().for_each(|m| {
            m.args_iter().for_each(|pat| idents.extend(pat.idents()));
            if let Some(pred) = &m.pred {
                idents.extend(pred.idents())
            }
            idents.extend(m.body.idents());
            m.wher_iter().for_each(|b| idents.extend(b.idents()))
        });
        idents
    }

    pub fn bound_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        [self.get_name()]
            .into_iter()
            .chain(self.arms_iter().flat_map(|m| m.bound_vars()))
            .collect()
    }

    pub fn free_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        let mut vars = Set::new();
        self.arms_iter().for_each(|m| {
            let mut fvs = m.body.free_vars();
            if let Some(pred) = &m.pred {
                fvs.extend(pred.free_vars());
            }
            m.args_iter().for_each(|pat| {
                pat.idents().iter().for_each(|id| {
                    fvs.remove(id);
                })
            });
            vars.extend(fvs)
        });
        vars.remove(&self.name);
        vars
    }
    pub fn map_id<X>(self, f: &mut impl FnMut(Id) -> X) -> Binding<X, T> {
        let Binding { name, arms, tipo } = self;
        Binding {
            name: f(name),
            arms: arms.into_iter().map(|m| m.map_id(f)).collect(),
            tipo: tipo.map(|sig| sig.map_id(|id| f(id))),
        }
    }

    pub fn map_id_ref<X>(&self, f: &mut impl FnMut(&Id) -> X) -> Binding<X, T>
    where
        T: Copy,
    {
        Binding {
            name: f(&self.name),
            arms: self.arms_iter().map(|m| m.map_id_ref(f)).collect(),
            tipo: self.tipo.as_ref().map(|s| s.map_id_ref(f)),
        }
    }

    pub fn map_t<U>(self, f: &mut impl FnMut(T) -> U) -> Binding<Id, U> {
        let mut arms = vec![];
        for arm in self.arms {
            arms.push(arm.map_t(f))
        }
        Binding {
            name: self.name,
            arms,
            tipo: self.tipo.map(|sig| sig.map_t(f)),
        }
    }

    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Binding<Id, U>
    where
        Id: Copy,
    {
        fn iters<A>(vec: &mut Vec<A>, f: &mut impl FnMut() -> A) {
            let it = f();
            vec.push(it);
        }

        let mut arms = vec![];
        for arm in &self.arms[..] {
            iters(&mut arms, &mut || arm.map_t_ref(f));
        }
        Binding {
            name: self.name,
            arms,
            tipo: if let Some(sig) = &self.tipo {
                Some(sig.map_t_ref(f))
            } else {
                None
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Statement<Id, T> {
    // <PAT> <- <EXPR>
    Generator(Pattern<Id, T>, Expression<Id, T>),
    // <EXPR>
    Predicate(Expression<Id, T>),
    // `let` without the `in`;
    // let (<ID> <PAT>* = <EXPR>)+
    JustLet(Vec<Binding<Id, T>>),
}

pub type RawStatement = Statement<Ident, Ident>;

impl<Id, T> Statement<Id, T> {
    /// Returns a set of references to all the identifiers referenced within the
    /// statement.
    pub fn idents(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        match self {
            Statement::Generator(p, x) => p.idents().into_iter().chain(x.idents()).collect(),
            Statement::Predicate(x) => x.idents(),
            Statement::JustLet(bs) => bs.into_iter().flat_map(Binding::idents).collect(),
        }
    }

    /// Returns a set of references to identifiers bound *outside* of the
    /// statement.
    pub fn free_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        match self {
            Statement::Generator(p, x) => x
                .free_vars()
                .difference(&p.idents())
                .map(|id| *id)
                .collect(),
            Statement::Predicate(x) => x.free_vars(),
            Statement::JustLet(bs) => bs.into_iter().flat_map(Binding::free_vars).collect(),
        }
    }

    /// Returns a set of references to identifiers bound *within* the statement.
    ///               
    /// | BINDING                 | BOUND    | FREE                 |
    /// |:------------------------|:---------|:---------------------|
    /// |`((x, y):z) <- foo a 1`  | x, y, z  | foo, a               |
    /// |`let  a = \x -> (x, x)`  | x        | a*                   |
    /// |`..., b = 2`             | --       | --                   |
    /// |`..., c = a b`           | --       | a, b, c*             |
    /// |`..., d = f print 0`;    | --       | f, print             |
    ///  
    pub fn bound_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        match self {
            Statement::Generator(p, _) => p.idents(),
            Statement::Predicate(x) => x.bound_vars(),
            Statement::JustLet(bindings) => {
                bindings.into_iter().flat_map(Binding::binders).collect()
            }
        }
    }

    pub fn map_id<X>(self, f: &mut impl FnMut(Id) -> X) -> Statement<X, T> {
        match self {
            Statement::Generator(p, x) => Statement::Generator(p.map_id(f), x.map_id(f)),
            Statement::Predicate(x) => Statement::Predicate(x.map_id(f)),
            Statement::JustLet(bns) => {
                Statement::JustLet(bns.into_iter().map(|b| b.map_id(f)).collect())
            }
        }
    }
    pub fn map_id_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> Statement<U, T>
    where
        T: Copy,
    {
        match self {
            Statement::Generator(p, x) => Statement::Generator(p.map_id_ref(f), x.map_id_ref(f)),
            Statement::Predicate(x) => Statement::Predicate(x.map_id_ref(f)),
            Statement::JustLet(bns) => {
                Statement::JustLet(bns.into_iter().map(|b| b.map_id_ref(f)).collect())
            }
        }
    }
    pub fn map_t<U>(self, f: &mut impl FnMut(T) -> U) -> Statement<Id, U> {
        match self {
            Statement::Generator(pat, expr) => Statement::Generator(pat.map_t(f), expr.map_t(f)),
            Statement::Predicate(expr) => Statement::Predicate(expr.map_t(f)),
            Statement::JustLet(_binds) => {
                todo!()
            }
        }
    }
    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Statement<Id, U>
    where
        Id: Copy,
    {
        match self {
            Statement::Generator(pat, expr) => {
                Statement::Generator(pat.map_t_ref(f), expr.map_t_ref(f))
            }
            Statement::Predicate(expr) => Statement::Predicate(expr.map_t_ref(f)),
            Statement::JustLet(_binds) => {
                todo!()
            }
        }
    }
}
