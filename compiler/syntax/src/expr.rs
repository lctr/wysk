use wy_lexer::Literal;

use crate::{
    ident::Ident,
    stmt::Alternative,
    tipo::{Record, Type},
    Binding,
};

use super::{Pattern, Statement};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expression<Id = Ident, T = Ident> {
    /// Identifier expressions; these can contain either *lowercase*-initial
    /// identifiers (corresponding to values), *uppercase*-initial identifiers
    /// (correstpondingo constructors), OR infix identifiers (corresponding to
    /// infixes used in non-infix nodes).
    ///
    /// Note that *qualified* identifiers are parsed as `Path`s! This is because
    /// `.` has record selection semantics, and namespaces are treated as
    /// records. Thus, the expression `f x` contains two `Ident` nodes, while
    /// the expression `F.x` contains a single `Path` node.
    Ident(Id),
    /// A combination of identifiers. The first identifier, coined the `root` is
    /// held separately from the rest, and it is *impossible* for a node of this
    /// variety to have an empty vector of identifiers (called the `tail`).
    ///
    /// A path `A.b.c` is represented as `Path::(A, [b, c])`, where the `tail`
    /// contains identifiers implicitly prefixed with a `.`.
    ///
    /// Path nodes are ultimately resolved to identifiers, and currently have
    /// two semantic uses:
    /// * identifier qualification; if a module `M` is
    /// imported and qualified as `N`, and `f` is exported from `M`, then `M.f`
    /// and `N.f` correspond to the same thing.
    /// * record selection; if a record `r` has field `f`, then `r.f` is
    ///   equivalent to the call `r f`
    Path(Id, Vec<Id>),
    Lit(Literal),
    Neg(Box<Expression<Id, T>>),
    Infix {
        infix: Id,
        left: Box<Expression<Id, T>>,
        right: Box<Expression<Id, T>>,
    },
    Tuple(Vec<Expression<Id, T>>),
    Array(Vec<Expression<Id, T>>),
    /// List comprehensions contain an expression and a list of statements
    /// consisting of *generators* and *predicates*.
    ///
    /// For example, if we suppose `f :: Int -> Int` is some integer-valued
    /// function, and `even :: Int -> Bool` is some integer-valued predicate
    /// testing for integer parity, then the following list expression would
    /// generate a list of the results of applying `f` to each even integer
    /// between `0` and `10` (not-inclusive).
    /// ```wysk
    ///     [ f x | x <- [0..10], even x ]
    /// ```
    /// In fact, the above expression would be equivalent to
    /// ```wysk
    ///     map f (filter even [0..10])
    /// ```
    /// and can be generalized to the following (inefficient) `let` expression,
    /// where we use `f`
    /// ```wysk
    /// let f :: a -> b
    ///     | a' = ...
    ///     g :: a -> Bool
    ///     | a'' = ...
    ///     h :: [a] -> [b]
    ///     | [] = []
    ///     | (a:as) if g a -> f a : h as
    ///     | (a:as) -> h as
    /// in ...
    /// ```
    List(Box<Expression<Id, T>>, Vec<Statement<Id, T>>),
    Dict(Record<Expression<Id, T>, Id>),
    Lambda(Pattern<Id, T>, Box<Expression<Id, T>>),
    Let(Vec<Binding<Id, T>>, Box<Expression<Id, T>>),
    App(Box<Expression<Id, T>>, Box<Expression<Id, T>>),
    Cond(Box<[Expression<Id, T>; 3]>),
    Case(Box<Expression<Id, T>>, Vec<Alternative<Id, T>>),
    Cast(Box<Expression<Id, T>>, Type<Id, T>),
    Do(Vec<Statement<Id, T>>, Box<Expression<Id, T>>),
    Range(Box<Expression<Id, T>>, Option<Box<Expression<Id, T>>>),
    Group(Box<Expression<Id, T>>),
}

impl<Id, T> Expression<Id, T> {
    pub const UNIT: Self = Self::Tuple(vec![]);
    pub const NULL: Self = Self::Array(vec![]);
    pub const VOID: Self = Self::Dict(Record::Anon(vec![]));

    pub fn is_unit(&self) -> bool {
        matches!(self, Self::Tuple(vs) if vs.is_empty())
    }
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Array(vs) if vs.is_empty())
    }
    pub fn is_void(&self) -> bool {
        matches!(self, Self::Dict(Record::Anon(vs)) if vs.is_empty())
    }
    pub fn is_empty_record(&self) -> bool {
        matches!(self, Self::Dict(Record::Anon(fs)|Record::Data(_, fs)) if fs.is_empty() )
    }

    /// If an expression is a `Group` variant, return the inner node.
    /// Otherwise, returns `Self`.
    pub fn ungroup(self) -> Self {
        match self {
            Expression::Group(expr) => *expr,
            expr => expr,
        }
    }

    /// If an expression is a `Group` variant, return a reference to the inner
    /// node. Otherwise, return a reference to `Self`.
    pub fn ungroup_ref(&self) -> &Self {
        match self {
            Expression::Group(expr) => expr.as_ref(),
            expr => expr,
        }
    }

    pub fn mk_app(head: Self, tail: Self) -> Self {
        Self::App(Box::new(head), Box::new(tail))
    }

    pub fn map_id<F, X>(self, mut f: F) -> Expression<X, T>
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Expression::Ident(id) => Expression::Ident(f(id)),
            Expression::Path(p, rs) => {
                Expression::Path(f(p), rs.into_iter().map(|id| f(id)).collect())
            }
            Expression::Lit(l) => Expression::Lit(l),
            Expression::Neg(x) => Expression::Neg(Box::new(x.map_id(|id| f(id)))),
            Expression::Infix { infix, left, right } => Expression::Infix {
                infix: f(infix),
                left: Box::new(left.map_id(|id| f(id))),
                right: Box::new(right.map_id(|id| f(id))),
            },
            Expression::Tuple(ts) => {
                Expression::Tuple(ts.into_iter().map(|x| x.map_id(|id| f(id))).collect())
            }
            Expression::Array(ts) => {
                Expression::Array(ts.into_iter().map(|x| x.map_id(|id| f(id))).collect())
            }
            Expression::List(x, stms) => Expression::List(
                Box::new(x.map_id(|id| f(id))),
                stms.into_iter().map(|s| s.map_id(|id| f(id))).collect(),
            ),
            Expression::Dict(rec) => {
                Expression::Dict(rec.map_t(|x| x.map_id(|id| f(id))).map_id(|id| f(id)))
            }
            Expression::Lambda(p, x) => {
                Expression::Lambda(p.map_id(|id| f(id)), Box::new(x.map_id(|id| f(id))))
            }
            Expression::Let(bs, x) => Expression::Let(
                bs.into_iter().map(|b| b.map_id(|id| f(id))).collect(),
                Box::new(x.map_id(|id| f(id))),
            ),
            Expression::App(x, y) => Expression::App(
                Box::new(x.map_id(|id| f(id))),
                Box::new(y.map_id(|id| f(id))),
            ),
            Expression::Cond(xyz) => {
                let [x, y, z] = *xyz;
                Expression::Cond(Box::new([
                    x.map_id(|id| f(id)),
                    y.map_id(|id| f(id)),
                    z.map_id(|id| f(id)),
                ]))
            }
            Expression::Case(scrut, arms) => Expression::Case(
                Box::new(scrut.map_id(|id| f(id))),
                arms.into_iter().map(|a| a.map_id(|id| f(id))).collect(),
            ),
            Expression::Cast(x, ty) => {
                Expression::Cast(Box::new(x.map_id(|id| f(id))), ty.map_id(&mut f))
            }
            Expression::Do(sts, x) => Expression::Do(
                sts.into_iter().map(|s| s.map_id(|id| f(id))).collect(),
                Box::new(x.map_id(|id| f(id))),
            ),
            Expression::Range(a, b) => Expression::Range(
                Box::new(a.map_id(|id| f(id))),
                b.map(|x| Box::new(x.map_id(|id| f(id)))),
            ),
            Expression::Group(ex) => Expression::Group(Box::new(ex.map_id(|id| f(id)))),
        }
    }
}

impl<T> Expression<Ident, T> {
    pub fn map_t<F, U>(self, f: &mut F) -> Expression<Ident, U>
    where
        F: FnMut(T) -> U,
        T: Copy,
    {
        fn iters<A>(vec: &mut Vec<A>, f: &mut impl FnMut() -> A) {
            vec.push((*f)())
        }
        match self {
            Expression::Ident(id) => Expression::Ident(id),
            Expression::Path(a, bs) => Expression::Path(a, bs),
            Expression::Lit(l) => Expression::Lit(l),
            Expression::Neg(e) => todo!(),
            Expression::Infix { infix, left, right } => {
                let left = Box::new(left.map_t(f));
                let right = Box::new(right.map_t(f));
                Expression::Infix { infix, left, right }
            }
            Expression::Tuple(ts) => {
                let mut xs = vec![];
                for t in ts {
                    iters(&mut xs, &mut || t.clone().map_t(f));
                }
                Expression::Tuple(xs)
            }
            Expression::Array(ts) => {
                let mut xs = vec![];
                for t in ts {
                    iters(&mut xs, &mut || t.clone().map_t(f));
                }
                Expression::Array(xs)
            }
            Expression::List(head, stmts) => {
                let h = Box::new(head.map_t(f));
                let mut sts = vec![];
                for s in stmts {
                    iters(&mut sts, &mut || s.clone().map_t(f));
                }
                Expression::List(h, sts)
            }
            Expression::Dict(_) => todo!(),
            Expression::Lambda(_, _) => todo!(),
            Expression::Let(_, _) => todo!(),
            Expression::App(_, _) => todo!(),
            Expression::Cond(_) => todo!(),
            Expression::Case(_, _) => todo!(),
            Expression::Cast(_, _) => todo!(),
            Expression::Do(_, _) => todo!(),
            Expression::Range(_, _) => todo!(),
            Expression::Group(_) => todo!(),
        }
    }
}
