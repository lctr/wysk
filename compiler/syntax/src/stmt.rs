use serde::{Deserialize, Serialize};
use wy_common::Set;
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
}
