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

    pub fn map_t<F, U>(self, mut f: F) -> Expression<Id, U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Expression::Ident(id) => Expression::Ident(id),
            Expression::Path(head, tail) => Expression::Path(head, tail),
            Expression::Lit(lit) => Expression::Lit(lit),
            Expression::Neg(x) => Expression::Neg(Box::new(x.map_t(|t| f(t)))),
            Expression::Infix { infix, left, right } => Expression::Infix {
                infix,
                left: Box::new(left.map_t(|t| f(t))),
                right: Box::new(right.map_t(|t| f(t))),
            },
            Expression::Tuple(xs) => {
                Expression::Tuple(xs.into_iter().map(|ex| ex.map_t(|t| f(t))).collect())
            }
            Expression::Array(xs) => {
                Expression::Array(xs.into_iter().map(|x| x.map_t(|t| f(t))).collect())
            }
            Expression::List(head, stmts) => Expression::List(
                Box::new(head.map_t(|t| f(t))),
                stmts.into_iter().map(|s| s.map_t(|t| f(t))).collect(),
            ),
            Expression::Dict(rec) => Expression::Dict(rec.map_t(|x| x.map_t(|t| f(t)))),
            Expression::Lambda(arg, body) => {
                Expression::Lambda(arg.map_t(|t| f(t)), Box::new(body.map_t(|t| f(t))))
            }
            Expression::Let(bs, body) => Expression::Let(
                bs.into_iter().map(|b| b.map_t(|t| f(t))).collect(),
                Box::new(body.map_t(|t| f(t))),
            ),
            Expression::App(x, y) => {
                Expression::App(Box::new(x.map_t(|t| f(t))), Box::new(y.map_t(|t| f(t))))
            }
            Expression::Cond(xs) => {
                let [x, y, z] = *xs;
                Expression::Cond(Box::new([
                    x.map_t(|t| f(t)),
                    y.map_t(|t| f(t)),
                    z.map_t(|t| f(t)),
                ]))
            }
            Expression::Case(scrut, alts) => Expression::Case(
                Box::new(scrut.map_t(|t| f(t))),
                alts.into_iter().map(|a| a.map_t(|t| f(t))).collect(),
            ),
            Expression::Cast(x, ty) => {
                Expression::Cast(Box::new(x.map_t(|t| f(t))), ty.map_t(&mut f))
            }
            Expression::Do(stmts, ex) => Expression::Do(
                stmts.into_iter().map(|s| s.map_t(|t| f(t))).collect(),
                Box::new(ex.map_t(|t| f(t))),
            ),
            Expression::Range(x, y) => Expression::Range(
                Box::new(x.map_t(|t| f(t))),
                y.map(|x| Box::new(x.map_t(|t| f(t)))),
            ),
            Expression::Group(ex) => Expression::Group(Box::new(ex.map_t(|t| f(t)))),
        }
    }
}
