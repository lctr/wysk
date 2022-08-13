use serde::{Deserialize, Serialize};
use wy_common::{
    functor::{MapFst, MapSnd},
    Set,
};

use crate::{expr::Expression, pattern::Pattern, tipo::Signature, SpannedIdent};

/// ```wysk
///     fn foo :: Int -> Int -> Bool
/// ~~> Arm[0]
/// ~~|  `args`
/// ~~|   vvv
///     | x y if x > y = True
/// ~~:       ^^^^^^^^   ^^^^
/// ~~:        `cond`   `body`
/// ~~> Arm[1]
/// ~~|  `args`
/// ~~|   vvv
///     | x y = False && u where u = x + y > 0
/// ~~:   ^^^   ^^^^^^^^^^ ^^^^^^^^^^^^^^^^^^^
/// ~~: `args`    `body`         `wher[0]`
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Arm<Id, V> {
    pub args: Vec<Pattern<Id, V>>,
    pub cond: Option<Expression<Id, V>>,
    pub body: Expression<Id, V>,
    pub wher: Vec<Binding<Id, V>>,
}

pub type RawArm = Arm<SpannedIdent, SpannedIdent>;

wy_common::struct_field_iters! {
    |Id, V| Arm<Id, V>
    | args => args_iter :: Pattern<Id, V>
    | wher => wher_iter :: Binding<Id, V>
}

impl<Id, V> Arm<Id, V> {
    /// A trivial match consists of only an expression, with the `args` and
    /// `where` fields empty vectors and `cond` a default `None`.
    pub fn trivial(body: Expression<Id, V>) -> Self {
        Self {
            args: vec![],
            cond: None,
            body,
            wher: vec![],
        }
    }
    pub fn caf(body: Expression<Id, V>, wher: Vec<Binding<Id, V>>) -> Self {
        Self {
            args: vec![],
            cond: None,
            body,
            wher,
        }
    }

    pub fn cond_iter(&self) -> std::option::Iter<Expression<Id, V>> {
        self.cond.iter()
    }

    pub fn bound_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        let mut ids = Set::new();
        self.args_iter().for_each(|pat| ids.extend(pat.binders()));
        self.cond_iter().for_each(|x| ids.extend(x.bound_vars()));
        ids.extend(self.body.bound_vars());
        self.wher_iter().for_each(|b| ids.extend(b.bound_vars()));
        ids
    }
}

impl<Id, V, X> MapFst<Id, X> for Arm<Id, V> {
    type WrapFst = Arm<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let Arm {
            args,
            cond,
            body,
            wher,
        } = self;
        let args = args.map_fst(f);
        let cond = cond.map_fst(f);
        let body = body.map_fst(f);
        let wher = wher.map_fst(f);
        Arm {
            args,
            cond,
            body,
            wher,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Arm<Id, V> {
    type WrapSnd = Arm<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let Arm {
            args,
            cond,
            body,
            wher,
        } = self;
        let args = args.map_snd(f);
        let cond = cond.map_snd(f);
        let body = body.map_snd(f);
        let wher = wher.map_snd(f);
        Arm {
            args,
            cond,
            body,
            wher,
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
/// ~~|   |  `cond`      `body`
/// ~~|   v vvvvvvvvv    vvvvv
///     | _ if t || u -> False
///         where t = True;
/// ~~:           ^^^^^^^^ `wher[0]`
///               u = False;
/// ~~:           ^^^^^^^^^ `wher[1]`
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Alternative<Id, V> {
    pub pat: Pattern<Id, V>,
    pub cond: Option<Expression<Id, V>>,
    pub body: Expression<Id, V>,
    pub wher: Vec<Binding<Id, V>>,
}

pub type RawAlternative = Alternative<SpannedIdent, SpannedIdent>;

wy_common::struct_field_iters! {
    |Id, V| Alternative<Id, V>
    | wher => wher_iter :: Binding<Id, V>
}

impl<Id, V> Alternative<Id, V> {
    pub fn cond_iter(&self) -> std::option::Iter<Expression<Id, V>> {
        self.cond.iter()
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
            .chain(self.cond.as_ref().into_iter().flat_map(Expression::idents))
            .chain(self.body.idents())
            .chain(self.wher_iter().flat_map(Binding::idents))
            .collect()
    }

    pub fn free_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        let mut vars = self.body.free_vars();
        if let Some(cond) = &self.cond {
            vars.extend(cond.free_vars());
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
}

impl<Id, V, X> MapFst<Id, X> for Alternative<Id, V> {
    type WrapFst = Alternative<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let Alternative {
            pat,
            cond,
            body,
            wher,
        } = self;
        let pat = pat.map_fst(f);
        let cond = cond.map_fst(f);
        let body = body.map_fst(f);
        let wher = wher.map_fst(f);
        Alternative {
            pat,
            cond,
            body,
            wher,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Alternative<Id, V> {
    type WrapSnd = Alternative<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let Alternative {
            pat,
            cond,
            body,
            wher,
        } = self;
        let pat = pat.map_snd(f);
        let cond = cond.map_snd(f);
        let body = body.map_snd(f);
        let wher = wher.map_snd(f);
        Alternative {
            pat,
            cond,
            body,
            wher,
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
pub struct Binding<Id, V> {
    pub name: Id,
    pub tsig: Signature<Id, V>,
    pub arms: Vec<Arm<Id, V>>,
}

pub type RawBinding = Binding<SpannedIdent, SpannedIdent>;

wy_common::struct_field_iters! {
    |Id, V| Binding<Id, V>
    | arms => arms_iter :: Arm<Id, V>
}

impl<Id, V> Binding<Id, V> {
    /// Returns a reference to the `name` of the binding.
    pub fn get_name(&self) -> &Id {
        &self.name
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
            if let Some(cond) = &m.cond {
                idents.extend(cond.idents())
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
            if let Some(cond) = &m.cond {
                fvs.extend(cond.free_vars());
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
}

impl<Id, V, X> MapFst<Id, X> for Binding<Id, V> {
    type WrapFst = Binding<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let Binding { name, tsig, arms } = self;
        let name = f.apply(name);
        let tsig = tsig.map_fst(f);
        let arms = arms.map_fst(f);
        Binding { name, arms, tsig }
    }
}

impl<Id, V, X> MapSnd<V, X> for Binding<Id, V> {
    type WrapSnd = Binding<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let Binding { name, tsig, arms } = self;
        let tsig = tsig.map_snd(f);
        let arms = arms.map_snd(f);
        Binding { name, arms, tsig }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Statement<Id, V> {
    // <PAT> <- <EXPR>
    Generator(Pattern<Id, V>, Expression<Id, V>),
    // <EXPR>
    Predicate(Expression<Id, V>),
    // `let` without the `in`;
    // let (<ID> <PAT>* = <EXPR>)+
    JustLet(Vec<Binding<Id, V>>),
}

pub type RawStatement = Statement<SpannedIdent, SpannedIdent>;

impl<Id, V> Statement<Id, V> {
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
}

impl<Id, V, X> MapFst<Id, X> for Statement<Id, V> {
    type WrapFst = Statement<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Statement::Generator(pat, ex) => Statement::Generator(pat.map_fst(f), ex.map_fst(f)),
            Statement::Predicate(ex) => Statement::Predicate(ex.map_fst(f)),
            Statement::JustLet(binds) => Statement::JustLet(binds.map_fst(f)),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Statement<Id, V> {
    type WrapSnd = Statement<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Statement::Generator(pat, ex) => Statement::Generator(pat.map_snd(f), ex.map_snd(f)),
            Statement::Predicate(ex) => Statement::Predicate(ex.map_snd(f)),
            Statement::JustLet(binds) => Statement::JustLet(binds.map_snd(f)),
        }
    }
}
