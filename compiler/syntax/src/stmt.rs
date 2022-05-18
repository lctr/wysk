use crate::{expr::Expression, ident::Ident, pattern::Pattern, tipo::Signature};

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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Match<Id = Ident, T = Ident> {
    pub args: Vec<Pattern<Id, T>>,
    pub pred: Option<Expression<Id, T>>,
    pub body: Expression<Id, T>,
    pub wher: Vec<Binding<Id, T>>,
}

impl<Id, T> Match<Id, T> {
    pub fn map_id<F, X>(self, mut f: F) -> Match<X, T>
    where
        F: FnMut(Id) -> X,
    {
        let Match {
            args,
            pred,
            body,
            wher,
        } = self;
        Match {
            args: args.into_iter().map(|pat| pat.map_id(|id| f(id))).collect(),
            pred: pred.map(|ex| ex.map_id(|id| f(id))),
            body: body.map_id(|id| f(id)),
            wher: wher.into_iter().map(|bnd| bnd.map_id(|id| f(id))).collect(),
        }
    }
    pub fn map_t<F, U>(self, mut f: F) -> Match<Id, U>
    where
        F: FnMut(T) -> U,
    {
        let Match {
            args,
            pred,
            body,
            wher,
        } = self;
        let args = args.into_iter().map(|p| p.map_t(|t| f(t))).collect();
        let pred = pred.map(|px| px.map_t(|t| f(t)));
        let body = body.map_t(|t| f(t));
        let wher = wher.into_iter().map(|b| b.map_t(|t| f(t))).collect();
        Match {
            args,
            pred,
            body,
            wher,
        }
    }
}

/// Associated namespace for match related checks, etc
pub struct MatchArms;
impl MatchArms {
    /// This function checks whether all the match arms provided contain the
    /// same number of argument patterns and is equivalent to checking for
    /// consistency in a given (function or binding)'s arity.
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
    pub fn arities_equal<I, T>(arms: &[Match<I, T>]) -> bool {
        match arms {
            [] | [_] => true,
            [head, rest @ ..] => {
                let arity = head.args.len();
                rest.iter().all(|m| m.args.len() == arity)
            }
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alternative<Id = Ident, T = Ident> {
    pub pat: Pattern<Id, T>,
    pub pred: Option<Expression<Id, T>>,
    pub body: Expression<Id, T>,
    pub wher: Vec<Binding<Id, T>>,
}

impl<Id, T> Alternative<Id, T> {
    pub fn map_id<F, X>(self, mut f: F) -> Alternative<X, T>
    where
        F: FnMut(Id) -> X,
    {
        let Alternative {
            pat,
            pred,
            body,
            wher,
        } = self;
        Alternative {
            pat: pat.map_id(|id| f(id)),
            pred: pred.map(|x| x.map_id(|id| f(id))),
            body: body.map_id(|id| f(id)),
            wher: wher.into_iter().map(|b| b.map_id(|id| f(id))).collect(),
        }
    }

    pub fn map_t<F, U>(self, mut f: F) -> Alternative<Id, U>
    where
        F: FnMut(T) -> U,
    {
        let Alternative {
            pat,
            pred,
            body,
            wher,
        } = self;
        let pat = pat.map_t(|t| f(t));
        let pred = pred.map(|x| x.map_t(|t| f(t)));
        let body = body.map_t(|t| f(t));
        let wher = wher.into_iter().map(|b| b.map_t(|t| f(t))).collect();
        Alternative {
            pat,
            pred,
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding<Id = Ident, T = Ident> {
    pub name: Id,
    pub arms: Vec<Match<Id, T>>,
    pub tipo: Option<Signature<Id, T>>,
}

impl<Id, T> Binding<Id, T> {
    pub fn map_id<F, X>(self, mut f: F) -> Binding<X, T>
    where
        F: FnMut(Id) -> X,
    {
        let Binding { name, arms, tipo } = self;
        Binding {
            name: f(name),
            arms: arms.into_iter().map(|m| m.map_id(|id| f(id))).collect(),
            tipo: tipo.map(|sig| sig.map_id(|id| f(id))),
        }
    }
    pub fn map_t<F, U>(self, mut f: F) -> Binding<Id, U>
    where
        F: FnMut(T) -> U,
    {
        let Binding { name, arms, tipo } = self;
        let arms = arms.into_iter().map(|m| m.map_t(|t| f(t))).collect();
        let tipo = if let Some(t) = tipo {
            Some(t.map_t(|t| f(t)))
        } else {
            None
        };
        Binding { name, arms, tipo }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement<Id = Ident, T = Ident> {
    // <PAT> <- <EXPR>
    Generator(Pattern<Id, T>, Expression<Id, T>),
    // <EXPR>
    Predicate(Expression<Id, T>),
    // `let` without the `in`;
    // let (<ID> <PAT>* = <EXPR>)+
    JustLet(Vec<Binding<Id, T>>),
}

impl<Id, T> Statement<Id, T> {
    pub fn map_id<F, X>(self, mut f: F) -> Statement<X, T>
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Statement::Generator(p, x) => {
                Statement::Generator(p.map_id(|id| f(id)), x.map_id(|id| f(id)))
            }
            Statement::Predicate(x) => Statement::Predicate(x.map_id(|id| f(id))),
            Statement::JustLet(bns) => {
                Statement::JustLet(bns.into_iter().map(|b| b.map_id(|id| f(id))).collect())
            }
        }
    }

    pub fn map_t<F, U>(self, mut f: F) -> Statement<Id, U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Statement::Generator(pat, expr) => {
                Statement::Generator(pat.map_t(|t| f(t)), expr.map_t(|t| f(t)))
            }
            Statement::Predicate(expr) => Statement::Predicate(expr.map_t(|t| f(t))),
            Statement::JustLet(binds) => {
                Statement::JustLet(binds.into_iter().map(|b| b.map_t(|t| f(t))).collect())
            }
        }
    }
}
