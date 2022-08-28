use serde::{Deserialize, Serialize};
use wy_common::Set;

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
    pub wher: Vec<LocalDef<Id, V>>,
}

pub type RawArm = Arm<SpannedIdent, SpannedIdent>;

wy_common::struct_field_iters! {
    |Id, V| Arm<Id, V>
    | args => args_iter :: Pattern<Id, V>
    | wher => wher_iter :: LocalDef<Id, V>
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
    pub fn caf(body: Expression<Id, V>, wher: Vec<LocalDef<Id, V>>) -> Self {
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

    pub fn idents(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        self.bound_vars()
    }

    pub fn binders(&self) -> Vec<&Id>
    where
        Id: PartialEq,
    {
        self.args_iter().flat_map(Pattern::binders).collect()
    }

    pub fn free_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        self.body
            .free_vars()
            .union(&self.wher.iter().flat_map(LocalDef::free_vars).collect())
            .cloned()
            .collect::<Set<_>>()
            .difference(
                &self
                    .args_iter()
                    .flat_map(Pattern::binders)
                    .collect::<Set<_>>(),
            )
            .cloned()
            .collect()
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
    pub wher: Vec<LocalDef<Id, V>>,
}

pub type RawAlternative = Alternative<SpannedIdent, SpannedIdent>;

wy_common::struct_field_iters! {
    |Id, V| Alternative<Id, V>
    | wher => wher_iter :: LocalDef<Id, V>
}

impl<Id, V> Alternative<Id, V> {
    pub fn cond_iter(&self) -> std::option::Iter<Expression<Id, V>> {
        self.cond.iter()
    }

    pub fn where_binder_names(&self) -> impl Iterator<Item = &Id> + '_ {
        self.wher_iter().filter_map(|b| match b {
            LocalDef::Binder(binder) => Some(binder.get_name()),
            LocalDef::Match(_) => None,
        })
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
            .chain(self.wher_iter().flat_map(LocalDef::idents))
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
        self.wher_iter().for_each(|localdef| {
            if let LocalDef::Binder(b) = localdef {
                vars.insert(b.get_name());
            }
            vars.extend(localdef.free_vars())
        });
        self.pat.idents().into_iter().for_each(|id| {
            vars.remove(id);
        });
        vars
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
                    fvs.shift_remove(id);
                })
            });
            vars.extend(fvs)
        });
        vars.shift_remove(&self.name);
        vars
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
    JustLet(Vec<LocalDef<Id, V>>),
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
            Statement::JustLet(bs) => bs.into_iter().flat_map(LocalDef::idents).collect(),
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
            Statement::JustLet(bs) => bs.into_iter().flat_map(LocalDef::free_vars).collect(),
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
                bindings.into_iter().flat_map(LocalDef::binders).collect()
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LocalDef<Id, V> {
    Binder(Binding<Id, V>),
    Match(Arm<Id, V>),
}

pub type RawLocalDef = LocalDef<SpannedIdent, SpannedIdent>;

wy_common::variant_preds! {
    |Id, V| LocalDef[Id, V]
    | is_binder => Binder(_)
    | is_match => Match(_)
}

impl<Id, V> LocalDef<Id, V> {
    pub fn binders(&self) -> Vec<&Id>
    where
        Id: PartialEq,
    {
        match self {
            LocalDef::Binder(b) => b.binders(),
            LocalDef::Match(a) => a.binders(),
        }
    }

    pub fn idents(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        match self {
            LocalDef::Binder(b) => b.idents(),
            LocalDef::Match(a) => a.idents(),
        }
    }

    pub fn free_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        match self {
            LocalDef::Binder(b) => b.free_vars(),
            LocalDef::Match(a) => a.free_vars(),
        }
    }

    pub fn bound_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        match self {
            LocalDef::Binder(b) => b.bound_vars(),
            LocalDef::Match(a) => a.bound_vars(),
        }
    }
}
