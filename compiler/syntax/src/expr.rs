use serde::{Deserialize, Serialize};
use wy_common::{
    deque,
    functor::{Functor, MapFst, MapSnd},
    variant_preds, Deque, Set,
};
use wy_lexer::Literal;
use wy_name::ident::{Ident, Identifier};

use crate::{decl::Arity, record::Record, stmt::Alternative, tipo::Type, Binding};

use super::{Pattern, Statement};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Section<Id = Ident, V = Id> {
    Prefix {
        prefix: Id,
        right: Box<Expression<Id, V>>,
    },
    Suffix {
        left: Box<Expression<Id, V>>,
        suffix: Id,
    },
}

variant_preds! {
    |Id, V| Section[Id, V]
    | is_prefix => Prefix {..}
    | is_suffix => Suffix {..}
}

impl<Id, V> Section<Id, V> {
    /// Given a prefix, returns a closure expecting an Expression with which it
    /// will construct a `Section::Prefix` variant.
    #[inline]
    pub fn with_prefix(prefix: Id) -> impl FnMut(Expression<Id, V>) -> Self
    where
        Id: Copy,
    {
        move |right| Self::Prefix {
            prefix,
            right: Box::new(right),
        }
    }

    /// Given a suffix, returns a closure expecting an Expression with which it
    /// will construct a `Section::Suffix` variant.
    #[inline]
    pub fn with_suffix(suffix: Id) -> impl FnMut(Expression<Id, V>) -> Self
    where
        Id: Copy,
    {
        move |left| Self::Suffix {
            left: Box::new(left),
            suffix,
        }
    }

    pub fn as_lambda(self, fresh_var: Id) -> (Pattern<Id, V>, Expression<Id, V>)
    where
        Id: Copy,
    {
        let var = Pattern::Var(fresh_var);
        let expr = match self {
            Section::Prefix { prefix, right } => Expression::Infix {
                infix: prefix,
                right,
                left: Box::new(Expression::Ident(fresh_var)),
            },
            Section::Suffix { left, suffix } => Expression::Infix {
                infix: suffix,
                left,
                right: Box::new(Expression::Ident(fresh_var)),
            },
        };
        (var, expr)
    }
    pub fn contains_affix(&self, affix: &Id) -> bool
    where
        Id: PartialEq<Id>,
    {
        match self {
            Section::Prefix { prefix: id, .. } | Section::Suffix { suffix: id, .. } => affix == id,
        }
    }
    pub fn as_tuple(self) -> (Id, Expression<Id, V>) {
        match self {
            Section::Prefix { prefix, right } => (prefix, *right),
            Section::Suffix { left, suffix } => (suffix, *left),
        }
    }
    pub fn as_tuple_ref(&self) -> (&Id, &Expression<Id, V>) {
        match self {
            Section::Prefix { prefix, right } => (prefix, right.as_ref()),
            Section::Suffix { left, suffix } => (suffix, left.as_ref()),
        }
    }
    #[inline]
    pub fn into_expression(self) -> Expression<Id, V> {
        Expression::Section(self)
    }
    pub fn expr(&self) -> &Expression<Id, V> {
        match self {
            Section::Prefix { right: expr, .. } | Section::Suffix { left: expr, .. } => {
                expr.as_ref()
            }
        }
    }
    pub fn expr_mut(&mut self) -> &mut Expression<Id, V> {
        match self {
            Section::Prefix { right: expr, .. } | Section::Suffix { left: expr, .. } => {
                expr.as_mut()
            }
        }
    }
    pub fn expression(self) -> Expression<Id, V> {
        match self {
            Section::Prefix { right: expr, .. } | Section::Suffix { left: expr, .. } => *expr,
        }
    }

    pub fn idents(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        std::iter::once(self.affix())
            .chain(self.expr().idents())
            .collect()
    }

    pub fn affix(&self) -> &Id {
        match self {
            Section::Prefix { prefix: affix, .. } | Section::Suffix { suffix: affix, .. } => affix,
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Section<Id, V> {
    type WrapFst = Section<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Section::Prefix { prefix, right } => Section::Prefix {
                prefix: f.apply(prefix),
                right: Box::new(right.map_fst(f)),
            },
            Section::Suffix { left, suffix } => Section::Suffix {
                suffix: f.apply(suffix),
                left: Box::new(left.map_fst(f)),
            },
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Section<Id, V> {
    type WrapSnd = Section<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Section::Prefix { prefix, right } => Section::Prefix {
                prefix,
                right: Box::new(right.map_snd(f)),
            },
            Section::Suffix { left, suffix } => Section::Suffix {
                suffix,
                left: Box::new(left.map_snd(f)),
            },
        }
    }
}

pub type RawExpression = Expression<Ident, Ident>;
pub type Expr<V> = Expression<Ident, V>;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Expression<Id, V> {
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
    Neg(Box<Expression<Id, V>>),
    Infix {
        infix: Id,
        left: Box<Expression<Id, V>>,
        right: Box<Expression<Id, V>>,
    },
    Section(Section<Id, V>),
    Tuple(Vec<Expression<Id, V>>),
    Array(Vec<Expression<Id, V>>),
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
    List(Box<Expression<Id, V>>, Vec<Statement<Id, V>>),
    Dict(Record<Id, Expression<Id, V>>),
    Lambda(Pattern<Id, V>, Box<Expression<Id, V>>),
    Let(Vec<Binding<Id, V>>, Box<Expression<Id, V>>),
    App(Box<Expression<Id, V>>, Box<Expression<Id, V>>),
    Cond(Box<[Expression<Id, V>; 3]>),
    Case(Box<Expression<Id, V>>, Vec<Alternative<Id, V>>),
    Cast(Box<Expression<Id, V>>, Type<Id, V>),
    Do(Vec<Statement<Id, V>>, Box<Expression<Id, V>>),
    Range(Box<Expression<Id, V>>, Option<Box<Expression<Id, V>>>),
    Group(Box<Expression<Id, V>>),
}

variant_preds! {
    |Id, V| Expression[Id, V]
    | is_unit => Tuple (vs) [if vs.is_empty()]
    | is_nil => Array (vs) [if vs.is_empty()]
    | is_void => Dict (Record::Anon(fls)
                      | Record::Data(_, fls)
                      ) [if fls.is_empty()]
    | is_lit => Lit (_)
    | is_ident => Ident (_)
    | is_path => Path (..)
    | is_neg => Neg (_)
    | is_infix => Infix {..}
    | is_suffix_section => Section (Section::Suffix {..})
    | is_prefix_section => Section (Section::Prefix {..})
    | is_tuple => Tuple (..)
    | is_array => Array (..)
    | is_list => List (..)
    | is_app => App (..)
    | is_let => Let (..)
    | is_case => Case (..)
    | is_cond => Cond (..)
    | is_lambda => Lambda (..)
    | is_lambda_wild => Lambda (Pattern::Wild, ..)
    | is_lambda_var => Lambda (Pattern::Var(_), _)
    | is_lambda_unit => Lambda (Pattern::Tup(ts), _) [if ts.is_empty()]
    | is_lambda_tup => Lambda (Pattern::Tup(_), _)
    | is_lambda_vec => Lambda (Pattern::Vec(_), _)
    | is_lambda_lnk => Lambda (Pattern::Lnk(..), _)
    | is_group => Group (_)
    | is_cast => Cast (..)
    | is_range => Range (..)
    | is_open_range => Range(_, None)
    | is_closed_range => Range(_, Some(_))
    | is_do => Do (..)
    | is_simple_do => Do (stmts, _) [if stmts.is_empty()]
}

variant_preds! { |V| Expression[Ident, V]
    | is_list_cons => Infix { infix, ..} [if infix.is_cons_sign()]

}

impl<Id, V, X> MapFst<Id, X> for Expression<Id, V> {
    type WrapFst = Expression<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Expression::Ident(id) => Expression::Ident(f.apply(id)),
            Expression::Path(head, tail) => Expression::Path(f.apply(head), Functor::fmap(tail, f)),
            Expression::Lit(lit) => Expression::Lit(lit),
            Expression::Neg(exp) => Expression::Neg(Box::new(exp.map_fst(f))),
            Expression::Infix { infix, left, right } => Expression::Infix {
                infix: f.apply(infix),
                left: Box::new(left.map_fst(f)),
                right: Box::new(right.map_fst(f)),
            },
            Expression::Section(sec) => Expression::Section(sec.map_fst(f)),
            Expression::Tuple(xs) => Expression::Tuple(xs.map_fst(f)),
            Expression::Array(xs) => Expression::Tuple(xs.map_fst(f)),
            Expression::List(x, stmts) => {
                Expression::List(Box::new(x.map_fst(f)), stmts.map_fst(f))
            }
            Expression::Dict(rec) => Expression::Dict(rec.map_fst(f)),
            Expression::Lambda(pat, body) => {
                Expression::Lambda(pat.map_fst(f), Box::new(body.map_fst(f)))
            }
            Expression::Let(bs, body) => Expression::Let(bs.map_fst(f), Box::new(body.map_fst(f))),
            Expression::App(fun, arg) => {
                Expression::App(Box::new(fun.map_fst(f)), Box::new(arg.map_fst(f)))
            }
            Expression::Cond(xyz) => {
                let [x, y, z] = *xyz;
                let x = x.map_fst(f);
                let y = y.map_fst(f);
                let z = z.map_fst(f);
                Expression::Cond(Box::new([x, y, z]))
            }
            Expression::Case(e, a) => Expression::Case(Box::new(e.map_fst(f)), a.map_fst(f)),
            Expression::Cast(e, ty) => Expression::Cast(Box::new(e.map_fst(f)), ty.map_fst(f)),
            Expression::Do(stmts, e) => Expression::Do(stmts.map_fst(f), Box::new(e.map_fst(f))),
            Expression::Range(a, b) => {
                Expression::Range(Box::new(a.map_fst(f)), b.map(|x| Box::new(x.map_fst(f))))
            }
            Expression::Group(e) => Expression::Group(Box::new(e.map_fst(f))),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Expression<Id, V> {
    type WrapSnd = Expression<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Expression::Ident(id) => Expression::Ident(id),
            Expression::Path(head, tail) => Expression::Path(head, tail),
            Expression::Lit(lit) => Expression::Lit(lit),
            Expression::Neg(exp) => Expression::Neg(Box::new(exp.map_snd(f))),
            Expression::Infix { infix, left, right } => Expression::Infix {
                infix,
                left: Box::new(left.map_snd(f)),
                right: Box::new(right.map_snd(f)),
            },
            Expression::Section(sec) => Expression::Section(sec.map_snd(f)),
            Expression::Tuple(xs) => Expression::Tuple(xs.map_snd(f)),
            Expression::Array(xs) => Expression::Tuple(xs.map_snd(f)),
            Expression::List(x, stmts) => {
                Expression::List(Box::new(x.map_snd(f)), stmts.map_snd(f))
            }
            Expression::Dict(rec) => Expression::Dict(rec.map_snd(f)),
            Expression::Lambda(pat, body) => {
                Expression::Lambda(pat.map_snd(f), Box::new(body.map_snd(f)))
            }
            Expression::Let(bs, body) => Expression::Let(bs.map_snd(f), Box::new(body.map_snd(f))),
            Expression::App(fun, arg) => {
                Expression::App(Box::new(fun.map_snd(f)), Box::new(arg.map_snd(f)))
            }
            Expression::Cond(xyz) => {
                let [x, y, z] = *xyz;
                let x = x.map_snd(f);
                let y = y.map_snd(f);
                let z = z.map_snd(f);
                Expression::Cond(Box::new([x, y, z]))
            }
            Expression::Case(e, a) => Expression::Case(Box::new(e.map_snd(f)), a.map_snd(f)),
            Expression::Cast(e, ty) => Expression::Cast(Box::new(e.map_snd(f)), ty.map_snd(f)),
            Expression::Do(stmts, e) => Expression::Do(stmts.map_snd(f), Box::new(e.map_snd(f))),
            Expression::Range(a, b) => {
                Expression::Range(Box::new(a.map_snd(f)), b.map(|x| Box::new(x.map_snd(f))))
            }
            Expression::Group(e) => Expression::Group(Box::new(e.map_snd(f))),
        }
    }
}

impl<Id, V> Expression<Id, V> {
    pub const UNIT: Self = Self::Tuple(vec![]);
    pub const NULL: Self = Self::Array(vec![]);

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

    pub fn get_lambda_arg(&self) -> Option<&Pattern<Id, V>> {
        match self {
            Self::Lambda(pat, _) => Some(pat),
            _ => None,
        }
    }

    pub fn get_lambda_args(&self) -> impl Iterator<Item = &Pattern<Id, V>> + '_ {
        let mut tmp = self;
        std::iter::from_fn(move || match tmp {
            Self::Lambda(pat, rhs) => {
                tmp = rhs.as_ref();
                Some(pat)
            }
            _ => None,
        })
    }

    /// If the expression is a lambda expression, this method will return the
    /// `Arity` value, wrapped within a `Some` variant, corresponding to the
    /// number of arguments it takes; otherwise, this returns `None`.
    pub fn lambda_arity(&self) -> Option<Arity> {
        let mut arity = 0;
        let mut exp = self;
        while let Self::Lambda(_pat, body) = exp {
            arity += 1;
            exp = body.as_ref();
        }
        if arity == 0 {
            None
        } else {
            Some(Arity(arity))
        }
    }

    #[inline]
    pub fn is_upper_ident(&self) -> bool
    where
        Id: Identifier,
    {
        matches!(self, Self::Ident(id) if id.is_upper())
    }

    #[inline]
    pub fn is_infix_ident(&self) -> bool
    where
        Id: Identifier,
    {
        matches!(self, Self::Ident(id) if id.is_infix())
    }

    /// If the given expression is an `App` expression, then this method will
    /// unfold it into a flat `VecDeque` of references to each subexpression,
    /// where the first element is the inner-most left-most expression.
    ///
    /// Note: an *argument* that happens to be an `App` expression *will not* be
    /// flattened! Only the left-most `App` sub-expressions will iteratively
    /// unfold. Thus, an expression like `(a (b c) d)` will return the deque
    /// corresponding to `[a, (b c), d]`.
    ///
    /// If the expression is not an application, then the resulting `VecDeque`
    /// will only contain a single expression.
    pub fn flatten_app(&self) -> Deque<&Self> {
        let mut sub_exprs = deque![];
        let mut tmp = self;
        while let Self::App(x, y) = tmp {
            sub_exprs.push_front(y.as_ref());
            tmp = x.as_ref();
        }
        sub_exprs.push_front(tmp);
        sub_exprs
    }

    /// If the expression is an `App` expression, the left-hand-side is
    /// continually unfolded until either a constructor is encountered *or* the
    /// left-hand side is no longer an application. If a constructor is found,
    /// then `true` is returned; otherwise, `false` is returned.
    ///
    /// For example, the expression corresponding to `(A b c d) = (((A b) c) d)`
    /// returns `true` because
    /// ```txt
    ///     (((A b) c) d) -> ((A b) c) -> (A b)
    /// ```
    ///
    /// Note that this only takes into account *literal* constructor
    /// applications -- this does not take into account for example applications
    /// where the innermost expression is a non-constructor identifier bound to
    /// a constructor. Thus, if we had `foo = Bar`, the expression `(foo 5)`
    /// would return *false*.
    #[inline]
    pub fn is_simple_ctor_app(&self) -> bool
    where
        Id: Identifier,
    {
        let mut expr = self;
        while let Self::App(left, _) = expr {
            match left.as_ref() {
                Self::Ident(id) => return id.is_upper(),
                Self::Path(_, ids) => {
                    return matches!(ids.into_iter().last().map(|id| id.is_upper()), Some(true))
                }
                Self::App(x, _) => {
                    let ex = x.as_ref();
                    if matches!(ex, Self::Ident(id) if id.is_upper()) {
                        return true;
                    }
                    expr = x.as_ref();
                    continue;
                }
                Self::Group(exp) => return exp.is_simple_ctor_app(),
                _ => return false,
            }
        }
        false
    }

    pub fn mk_group(expr: Self) -> Self {
        Self::Group(Box::new(expr))
    }

    pub fn mk_app(head: Self, tail: Self) -> Self {
        Self::App(Box::new(head), Box::new(tail))
    }

    /// Checks whether an expression can be directly reinterpreted as a pattern
    /// in a binding
    pub fn valid_pat(&self) -> bool
    where
        Id: Identifier,
    {
        match self {
            Expression::Ident(_) | Expression::Lit(_) => true,
            Expression::Neg(x) | Expression::Group(x) => x.valid_pat(),
            Expression::Path(_, _)
            | Expression::Section(_)
            | Expression::Lambda(_, _)
            | Expression::Let(_, _)
            | Expression::Cond(_)
            | Expression::Do(_, _)
            | Expression::Case(_, _)
            | Expression::List(_, _)
            | Expression::Infix { .. } => false,
            Expression::Tuple(ts) | Expression::Array(ts) => ts.into_iter().all(|x| x.valid_pat()),
            Expression::Dict(rec) => rec.fields().into_iter().all(|field| {
                !field.is_rest()
                    && field
                        .get_value()
                        .map(|ex| ex.valid_pat())
                        .unwrap_or_else(|| false)
            }),
            Expression::App(left, right) => {
                right.valid_pat() && {
                    let mut tmp = left.as_ref();
                    loop {
                        match tmp {
                            Expression::Ident(id) => {
                                if id.is_upper() {
                                    break true;
                                }
                            }
                            Expression::App(x, y) => {
                                if y.valid_pat() {
                                    tmp = x.as_ref();
                                    continue;
                                } else {
                                    break false;
                                }
                            }
                            ex => {
                                break ex.valid_pat();
                            }
                        }
                    }
                }
            }
            Expression::Cast(x, _) => x.valid_pat(),
            Expression::Range(a, b) => {
                let va = a.valid_pat();
                if let Some(vb) = b {
                    va && vb.valid_pat()
                } else {
                    va
                }
            }
        }
    }

    pub fn idents(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        let mut idents = Set::new();
        match self {
            Expression::Ident(id) => {
                idents.insert(id);
            }
            Expression::Path(h, t) => {
                idents.insert(h);
                idents.extend(t);
            }
            Expression::Lit(_) => (),
            Expression::Neg(x) | Expression::Group(x) | Expression::Cast(x, _) => {
                idents.extend(x.idents())
            }
            Expression::Infix { infix, left, right } => idents.extend(
                std::iter::once(infix)
                    .chain(left.idents())
                    .chain(right.idents()),
            ),
            Expression::Section(s) => {
                let (a, b) = s.as_tuple_ref();
                idents.insert(a);
                idents.extend(b.idents())
            }
            Expression::Tuple(xs) | Expression::Array(xs) => {
                idents.extend(xs.into_iter().flat_map(Self::idents))
            }
            Expression::List(x, s) => idents.extend(
                x.idents()
                    .into_iter()
                    .chain(s.into_iter().flat_map(|s| s.idents())),
            ),
            Expression::Dict(r) => {
                idents.extend(
                    r.ctor()
                        .into_iter()
                        .chain(r.keys())
                        .chain(r.values().into_iter().flat_map(|x| x.idents())),
                );
            }
            Expression::Lambda(p, x) => {
                idents.extend(p.idents());
                idents.extend(x.idents());
            }
            Expression::Let(bs, x) => bs.into_iter().for_each(|b| {
                idents.extend(b.idents());
                idents.extend(x.idents());
            }),
            Expression::App(x, y) => {
                idents.extend(x.idents());
                idents.extend(y.idents());
            }
            Expression::Cond(xyz) => xyz
                .as_ref()
                .into_iter()
                .for_each(|x| idents.extend(x.idents())),
            Expression::Case(x, alts) => {
                idents.extend(x.idents());
                alts.into_iter().for_each(|alt| idents.extend(alt.idents()))
            }
            Expression::Do(stmts, x) => {
                idents.extend(stmts.into_iter().flat_map(|s| s.idents()).chain(x.idents()))
            }
            Expression::Range(a, b) => {
                idents.extend(
                    a.idents()
                        .into_iter()
                        .chain(b.into_iter().flat_map(|x| x.idents())),
                );
            }
        };
        idents
    }

    /// Returns a set of references to identifiers bound within the expression,
    /// including those bound in contained subexpressions. Equivalent to the set
    /// of all identifiers in an expression with its free variables removed,
    /// i.e., `all_idents - free_vars`.
    pub fn bound_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        self.idents()
            .difference(&self.free_vars())
            .copied()
            .collect()
    }

    pub fn free_vars(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        let mut vars = Set::new();
        match self {
            Expression::Ident(id) => {
                vars.insert(id);
            }
            Expression::Path(_, _) => (),
            Expression::Lit(_) => (),
            Expression::Infix { infix, left, right } => {
                vars.insert(infix);
                vars.extend(left.free_vars());
                vars.extend(right.free_vars());
            }
            Expression::Section(sec) => {
                vars.insert(sec.affix());
                vars.extend(sec.expr().free_vars());
            }
            Expression::Tuple(xs) | Expression::Array(xs) => {
                xs.into_iter().for_each(|x| vars.extend(x.free_vars()))
            }
            Expression::List(head, quals) => {
                let mut fvs = head.free_vars();
                quals.into_iter().for_each(|s| match s {
                    Statement::Generator(pat, exp) => {
                        fvs.extend(exp.free_vars().difference(&pat.idents()).copied())
                    }
                    Statement::Predicate(ex) => fvs.extend(ex.free_vars()),
                    Statement::JustLet(binds) => binds
                        .into_iter()
                        .for_each(|bind| fvs.extend(bind.free_vars())),
                });
                vars.extend(fvs);
            }
            Expression::Dict(r) => {
                // currently ignoring record keys -- should they be considered
                // free variables or ??
                vars.extend(
                    r.ctor()
                        .into_iter()
                        .chain(r.values().into_iter().flat_map(Self::free_vars)),
                )
            }
            Expression::Lambda(arg, body) => {
                vars.extend(body.free_vars().difference(&arg.idents()).copied())
            }
            Expression::Let(bs, x) => {
                bs.into_iter().for_each(|b| vars.extend(b.free_vars()));
                vars.extend(x.free_vars());
            }
            Expression::App(x, y) => {
                vars.extend(x.free_vars());
                vars.extend(y.free_vars());
            }
            Expression::Cond(xyz) => {
                vars.extend(xyz.as_ref().into_iter().flat_map(Self::free_vars))
            }
            Expression::Case(scrut, arms) => {
                vars.extend(scrut.free_vars());
                arms.into_iter()
                    .for_each(|alt| vars.extend(alt.free_vars()));
            }
            Expression::Do(stmts, x) => {
                stmts.into_iter().for_each(|s| vars.extend(s.free_vars()));
                vars.extend(x.idents());
            }
            Expression::Range(x, y) => {
                vars.extend(x.free_vars());
                if let Some(y) = y {
                    vars.extend(y.free_vars())
                }
            }
            Expression::Cast(x, _) | Expression::Neg(x) | Expression::Group(x) => {
                vars.extend(x.free_vars())
            }
        };
        vars
    }

    pub fn app_iter(&self) -> impl Iterator<Item = &Expression<Id, V>> + '_ {
        let mut tmp = self;
        std::iter::from_fn(move || {
            if let Self::App(x, y) = tmp {
                tmp = x.as_ref();
                Some(y.as_ref())
            } else {
                None
            }
        })
    }

    pub fn iter_lambda_args(&self) -> impl Iterator<Item = &Pattern<Id, V>> + '_ {
        let mut tmp = self;
        std::iter::from_fn(move || {
            if let Self::Lambda(arg, body) = tmp {
                tmp = body.as_ref();
                Some(arg)
            } else {
                None
            }
        })
    }
}

pub fn try_expr_into_pat<Id: Identifier, V>(expr: Expression<Id, V>) -> Option<Pattern<Id, V>> {
    fn iters<A: Identifier, B>(exprs: Vec<Expression<A, B>>) -> Option<Vec<Pattern<A, B>>> {
        exprs.into_iter().fold(Some(vec![]), |a, c| match a {
            Some(mut acc) => try_expr_into_pat(c).map(|pat| {
                acc.push(pat);
                acc
            }),
            None => None,
        })
    }
    match expr {
        Expression::Ident(id) => Some(Pattern::Var(id)),
        Expression::Path(_, _)
        | Expression::Infix { .. }
        | Expression::Lambda(_, _)
        | Expression::Let(_, _)
        | Expression::Section(_)
        | Expression::List(_, _)
        | Expression::Cond(_)
        | Expression::Case(_, _)
        | Expression::Do(_, _) => None,
        Expression::Lit(lit) => Some(Pattern::Lit(lit)),
        Expression::Neg(_) => todo!(),
        Expression::Tuple(ts) => iters(ts).map(Pattern::Tup),
        Expression::Array(ts) => iters(ts).map(Pattern::Vec),
        Expression::Dict(rec) => Some(Pattern::Rec(rec.map(|(con, fields)| {
            let mut flds = vec![];
            for field in fields {
                let f = field.map(|(id, expr)| (id, expr.and_then(try_expr_into_pat)));
                flds.push(f);
            }
            (con, flds)
        }))),
        Expression::App(x, y) => {
            let mut left = *x;
            let mut right = *y;
            let mut args = vec![];
            loop {
                if let Some(py) = try_expr_into_pat(right) {
                    args.push(py);
                    match left {
                        Expression::App(x2, y2) => {
                            left = *x2;
                            right = *y2;
                            continue;
                        }
                        Expression::Ident(id) if id.is_upper() => break Some(id),
                        _ => break None,
                    }
                }
                break None;
            }
            .map(|id| {
                Pattern::Dat(id, {
                    args.reverse();
                    args
                })
            })
        }
        Expression::Cast(x, ty) => {
            try_expr_into_pat(*x).map(|pat| Pattern::Cast(Box::new(pat), ty))
        }
        Expression::Range(a, Some(b)) => match (try_expr_into_pat(*a), try_expr_into_pat(*b)) {
            (Some(x), Some(y)) => Some(Pattern::Rng(Box::new(x), Some(Box::new(y)))),
            _ => None,
        },
        Expression::Range(a, None) => {
            try_expr_into_pat(*a).map(|p| Pattern::Rng(Box::new(p), None))
        }
        Expression::Group(x) => try_expr_into_pat(*x),
    }
}

impl<V> Expression<Ident, V> {
    pub fn max_fresh_val(&self) -> Option<u32> {
        wy_name::ident::max_fresh_value(self.idents().into_iter())
    }

    pub fn fresh_ident(&self) -> Ident {
        Ident::Fresh(self.max_fresh_val().map(|u| u + 1).unwrap_or_else(|| 0))
    }
}

#[cfg(test)]
mod tests {
    // use wy_common::Mappable;
    use wy_intern::symbol;

    use super::*;

    #[test]
    fn test_flatten_app() {
        let [f, g, h]: [RawExpression; 3] =
            symbol::intern_many_with(["f", "g", "h"], |sym| Expression::Ident(Ident::Lower(sym)));
        let lit = |n| Expression::Lit(Literal::Int(n));
        let [one, three, four]: [RawExpression; 3] = [lit(1), lit(3), lit(4)];

        // (((f (g 1)) h) 3) 4)
        let app = Expression::mk_app(
            Expression::mk_app(
                Expression::mk_app(Expression::mk_app(f, Expression::mk_app(g, one)), h),
                three,
            ),
            four,
        );

        println!(
            "app iter collected: {:?}",
            app.app_iter().collect::<Vec<_>>()
        );

        let deque = app.flatten_app();
        assert_eq!(deque.len(), 5);
        let re_app = deque
            .into_iter()
            .cloned()
            .reduce(|a, c| Expression::App(Box::new(a), Box::new(c)));
        assert_eq!(Some(app), re_app)
    }
}
