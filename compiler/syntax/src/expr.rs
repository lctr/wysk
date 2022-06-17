use wy_common::{deque, variant_preds, Deque, Mappable, Set};
use wy_lexer::Literal;
use wy_name::ident::{Ident, Identifier};

use crate::{
    decl::Arity,
    stmt::Alternative,
    tipo::{Record, Type},
    Binding,
};

use super::{Pattern, Statement};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Section<Id = Ident, T = Id> {
    Prefix {
        prefix: Id,
        right: Box<Expression<Id, T>>,
    },
    Suffix {
        left: Box<Expression<Id, T>>,
        suffix: Id,
    },
}

variant_preds! {
    |Id, T| Section[Id, T]
    | is_prefix => Prefix {..}
    | is_suffix => Suffix {..}
}

impl<Id, T> Section<Id, T> {
    pub fn as_lambda(self, fresh_var: Id) -> (Pattern<Id, T>, Expression<Id, T>)
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
    pub fn as_tuple(self) -> (Id, Expression<Id, T>) {
        match self {
            Section::Prefix { prefix, right } => (prefix, *right),
            Section::Suffix { left, suffix } => (suffix, *left),
        }
    }
    pub fn expr(&self) -> &Expression<Id, T> {
        match self {
            Section::Prefix { right: expr, .. } | Section::Suffix { left: expr, .. } => {
                expr.as_ref()
            }
        }
    }
    pub fn expr_mut(&mut self) -> &mut Expression<Id, T> {
        match self {
            Section::Prefix { right: expr, .. } | Section::Suffix { left: expr, .. } => {
                expr.as_mut()
            }
        }
    }
    pub fn expression(self) -> Expression<Id, T> {
        match self {
            Section::Prefix { right: expr, .. } | Section::Suffix { left: expr, .. } => *expr,
        }
    }

    pub fn affix(&self) -> &Id {
        match self {
            Section::Prefix { prefix: affix, .. } | Section::Suffix { suffix: affix, .. } => affix,
        }
    }
    pub fn map_id<U>(self, mut f: impl FnMut(Id) -> U) -> Section<U, T> {
        match self {
            Section::Prefix { prefix, right } => Section::Prefix {
                prefix: f(prefix),
                right: Box::new(right.map_id(|id| f(id))),
            },
            Section::Suffix { left, suffix } => Section::Suffix {
                suffix: f(suffix),
                left: Box::new(left.map_id(|id| f(id))),
            },
        }
    }

    pub fn map_id_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> Section<U, T>
    where
        T: Copy,
    {
        match self {
            Section::Prefix { prefix, right } => Section::Prefix {
                prefix: f(prefix),
                right: Box::new(right.map_id_ref(f)),
            },
            Section::Suffix { left, suffix } => Section::Suffix {
                suffix: f(suffix),
                left: Box::new(left.map_id_ref(f)),
            },
        }
    }

    pub fn map_t<U>(self, f: &mut impl FnMut(T) -> U) -> Section<Id, U> {
        match self {
            Section::Prefix { prefix, right } => Section::Prefix {
                prefix,
                right: Box::new(right.map_t(f)),
            },
            Section::Suffix { left, suffix } => Section::Suffix {
                suffix,
                left: Box::new(left.map_t(f)),
            },
        }
    }
    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Section<Id, U>
    where
        Id: Copy,
    {
        match self {
            Section::Prefix { prefix, right } => Section::Prefix {
                prefix: *prefix,
                right: Box::new(right.map_t_ref(f)),
            },
            Section::Suffix { left, suffix } => Section::Suffix {
                left: Box::new(left.map_t_ref(f)),
                suffix: *suffix,
            },
        }
    }
}

pub type RawExpression = Expression<Ident, Ident>;
pub type Expr<T> = Expression<Ident, T>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expression<Id, T> {
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
    Section(Section<Id, T>),
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
    Dict(Record<Id, Expression<Id, T>>),
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

variant_preds! {
    |Id, T| Expression[Id, T]
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
    | is_do => Do (..)
    | is_simple_do => Do (stmts, _) [if stmts.is_empty()]
}

variant_preds! { |T| Expression[Ident, T]
    | is_list_cons => Infix { infix, ..} [if infix.is_cons_sign()]

}

impl<Id, T> Expression<Id, T> {
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

    pub fn get_lambda_arg(&self) -> Option<&Pattern<Id, T>> {
        match self {
            Self::Lambda(pat, _) => Some(pat),
            _ => None,
        }
    }

    pub fn get_lambda_args(&self) -> impl Iterator<Item = &Pattern<Id, T>> + '_ {
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

    /// Identifies whether the expression is a `Range` expression with no endpoint
    #[inline]
    pub fn is_open_range(&self) -> bool {
        matches!(self, Self::Range(_, None))
    }

    /// Identifies whether ther expression is a `Range` expression with a start
    /// and an end. **Note** this may not *necessarily* imply the range is
    /// *finite*, as the endpoint may be an expression that resolves to a
    /// non-finite number
    #[inline]
    pub fn is_closed_range(&self) -> bool {
        matches!(self, Self::Range(_, Some(_)))
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
            Expression::Range(_, _) => todo!(),
        }
    }

    pub fn free_vars(&self) -> Set<Id>
    where
        Id: Copy + Eq + std::hash::Hash,
    {
        let mut vars = Set::new();
        match self {
            Expression::Ident(id) => {
                vars.insert(*id);
            }
            Expression::Path(_, _) => {}
            Expression::Lit(_) => {}
            Expression::Infix { infix, left, right } => {
                vars.insert(*infix);
                vars.extend(left.free_vars());
                vars.extend(right.free_vars());
            }
            Expression::Section(sec) => {
                vars.insert(*sec.affix());
                vars.extend(sec.expr().free_vars());
            }
            Expression::Tuple(xs) | Expression::Array(xs) => {
                xs.into_iter().for_each(|x| vars.extend(x.free_vars()))
            }
            Expression::List(head, quals) => {
                let mut fvs = head.free_vars();
                quals.into_iter().for_each(|s| match s {
                    Statement::Generator(pat, exp) => {
                        fvs.extend(exp.free_vars().difference(&pat.vars()).copied())
                    }
                    Statement::Predicate(ex) => fvs.extend(ex.free_vars()),
                    Statement::JustLet(binds) => binds
                        .into_iter()
                        .for_each(|bind| fvs.extend(bind.free_vars())),
                });
                vars.extend(fvs);
            }
            Expression::Dict(_) => todo!(),
            Expression::Lambda(arg, body) => {
                vars.extend(body.free_vars().difference(&arg.vars()).copied())
            }
            Expression::Let(_, _) => todo!(),
            Expression::App(x, y) => {
                vars.extend(x.free_vars());
                vars.extend(y.free_vars());
            }
            Expression::Cond(xyz) => {
                for e in xyz.as_ref() {
                    vars.extend(e.free_vars());
                }
            }
            Expression::Case(scrut, arms) => {
                vars.extend(scrut.free_vars());
                arms.into_iter()
                    .for_each(|alt| vars.extend(alt.free_vars()));
            }
            Expression::Do(_, _) => todo!(),
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

    pub fn app_iter(&self) -> impl Iterator<Item = &Expression<Id, T>> + '_ {
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

    pub fn iter_lambda_args(&self) -> impl Iterator<Item = &Pattern<Id, T>> + '_ {
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

    pub fn map_id<X>(self, mut f: impl FnMut(Id) -> X) -> Expression<X, T> {
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
            Expression::Section(sec) => Expression::Section(sec.map_id(f)),
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

    pub fn map_id_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> Expression<U, T>
    where
        T: Copy,
    {
        match self {
            Expression::Ident(id) => Expression::Ident(f(id)),
            Expression::Path(x, y) => {
                Expression::Path(f(x), y.into_iter().map(|id| f(id)).collect())
            }
            Expression::Lit(l) => Expression::Lit(*l),
            Expression::Neg(ex) => Expression::Neg(Box::new(ex.map_id_ref(f))),
            Expression::Infix { infix, left, right } => Expression::Infix {
                infix: f(infix),
                left: Box::new(left.map_id_ref(f)),
                right: Box::new(right.map_id_ref(f)),
            },
            Expression::Section(section) => Expression::Section(section.map_id_ref(f)),
            Expression::Tuple(ts) => {
                Expression::Tuple(ts.into_iter().map(|ex| ex.map_id_ref(f)).collect())
            }
            Expression::Array(ts) => {
                Expression::Array(ts.into_iter().map(|ex| ex.map_id_ref(f)).collect())
            }
            Expression::List(ex, stms) => Expression::List(
                Box::new(ex.map_id_ref(f)),
                stms.into_iter().map(|st| st.map_id_ref(f)).collect(),
            ),
            Expression::Dict(rec) => Expression::Dict(rec.map_ref(&mut |a, b| {
                let con = a.map(|id| f(id));
                let es = b
                    .into_iter()
                    .map(|field| {
                        field.map_ref(&mut |(x, y)| (f(x), y.map(|rhs| rhs.map_id_ref(f))))
                    })
                    .collect();
                (con, es)
            })),
            Expression::Lambda(p, x) => {
                Expression::Lambda(p.map_id_ref(f), Box::new(x.map_id_ref(f)))
            }
            Expression::Let(bs, x) => Expression::Let(
                bs.into_iter().map(|b| b.map_id_ref(f)).collect(),
                Box::new(x.map_id_ref(f)),
            ),
            Expression::App(x, y) => {
                Expression::App(Box::new(x.map_id_ref(f)), Box::new(y.map_id_ref(f)))
            }
            Expression::Cond(xyz) => {
                let [x, y, z] = xyz.as_ref();
                Expression::Cond(Box::new([
                    x.map_id_ref(f),
                    y.map_id_ref(f),
                    z.map_id_ref(f),
                ]))
            }
            Expression::Case(scrut, arms) => Expression::Case(
                Box::new(scrut.map_id_ref(f)),
                arms.into_iter().map(|a| a.map_id_ref(f)).collect(),
            ),
            Expression::Cast(x, ty) => {
                Expression::Cast(Box::new(x.map_id_ref(f)), ty.map_id_ref(f))
            }
            Expression::Do(sts, x) => Expression::Do(
                sts.into_iter().map(|s| s.map_id_ref(f)).collect(),
                Box::new(x.map_id_ref(f)),
            ),
            Expression::Range(a, b) => Expression::Range(
                Box::new(a.map_id_ref(f)),
                b.as_ref().map(|x| Box::new(x.map_id_ref(f))),
            ),
            Expression::Group(ex) => Expression::Group(Box::new(ex.map_id_ref(f))),
        }
    }

    pub fn map_t<U>(self, f: &mut impl FnMut(T) -> U) -> Expression<Id, U> {
        match self {
            Expression::Ident(id) => Expression::Ident(id),
            Expression::Path(a, bs) => Expression::Path(a, bs),
            Expression::Lit(l) => Expression::Lit(l),
            Expression::Neg(e) => Expression::Neg(Box::new(e.map_t(f))),
            Expression::Infix { infix, left, right } => {
                let left = Box::new(left.map_t(f));
                let right = Box::new(right.map_t(f));
                Expression::Infix { infix, left, right }
            }
            Expression::Section(section) => Expression::Section(section.map_t(f)),
            Expression::Tuple(ts) => {
                let mut xs = vec![];
                for t in ts {
                    xs.push(t.map_t(f))
                }
                Expression::Tuple(xs)
            }
            Expression::Array(ts) => {
                let mut xs = vec![];
                for t in ts {
                    xs.push(t.map_t(f))
                }
                Expression::Array(xs)
            }
            Expression::List(head, stmts) => {
                let h = Box::new(head.map_t(f));
                let mut sts = vec![];
                for s in stmts {
                    sts.push(s.map_t(f));
                }
                Expression::List(h, sts)
            }
            Expression::Dict(rec) => Expression::Dict(rec.map_t(|ex| ex.map_t(f))),
            Expression::Lambda(arg, body) => {
                Expression::Lambda(arg.map_t(f), Box::new(body.map_t(f)))
            }
            Expression::Let(arms, body) => {
                let body = Box::new(body.map_t(f));
                let mut binds = vec![];
                for b in arms {
                    binds.push(b.map_t(f));
                }
                Expression::Let(binds, body)
            }
            Expression::App(x, y) => Expression::App(Box::new(x.map_t(f)), Box::new(y.map_t(f))),
            Expression::Cond(xyz) => {
                let [x, y, z] = *xyz;
                Expression::Cond(Box::new([x.map_t(f), y.map_t(f), z.map_t(f)]))
            }
            Expression::Case(x, arms) => Expression::Case(
                Box::new(x.map_t(f)),
                arms.into_iter()
                    .map(
                        |Alternative {
                             body,
                             pat,
                             pred,
                             wher,
                         }| Alternative {
                            pat: pat.map_t(f),
                            pred: if let Some(pred) = pred {
                                Some(pred.map_t(f))
                            } else {
                                None
                            },
                            body: body.map_t(f),
                            wher: wher.into_iter().map(|b| b.map_t(f)).collect(),
                        },
                    )
                    .collect(),
            ),
            Expression::Cast(x, t) => Expression::Cast(Box::new(x.map_t(f)), t.map_t(f)),
            Expression::Do(stmts, expr) => {
                Expression::Do(stmts.fmap(|s| s.map_t(f)), Box::new(expr.map_t(f)))
            }
            Expression::Range(a, b) => Expression::Range(
                Box::new(a.map_t(f)),
                if let Some(b) = b {
                    Some(Box::new(b.map_t(f)))
                } else {
                    None
                },
            ),
            Expression::Group(x) => Expression::Group(Box::new(x.map_t(f))),
        }
    }
    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Expression<Id, U>
    where
        Id: Copy,
    {
        fn iters<A>(vec: &mut Vec<A>, f: &mut impl FnMut() -> A) {
            vec.push((*f)())
        }
        match self {
            Expression::Ident(id) => Expression::Ident(*id),
            Expression::Path(a, bs) => Expression::Path(*a, bs.clone()),
            Expression::Lit(l) => Expression::Lit(*l),
            Expression::Neg(e) => {
                let mut x = vec![];
                iters(&mut x, &mut || e.map_t_ref(f));
                Expression::Neg(Box::new(x.pop().unwrap()))
            }
            Expression::Infix { infix, left, right } => {
                let left = Box::new(left.map_t_ref(f));
                let right = Box::new(right.map_t_ref(f));
                Expression::Infix {
                    infix: *infix,
                    left,
                    right,
                }
            }
            Expression::Section(section) => Expression::Section(section.map_t_ref(f)),
            Expression::Tuple(ts) => {
                let mut xs = vec![];
                for t in ts {
                    iters(&mut xs, &mut || t.map_t_ref(f));
                }
                Expression::Tuple(xs)
            }
            Expression::Array(ts) => {
                let mut xs = vec![];
                for t in ts {
                    iters(&mut xs, &mut || t.map_t_ref(f));
                }
                Expression::Array(xs)
            }
            Expression::List(head, stmts) => {
                let h = Box::new(head.map_t_ref(f));
                let mut sts = vec![];
                for s in stmts {
                    iters(&mut sts, &mut || s.map_t_ref(f));
                }
                Expression::List(h, sts)
            }
            Expression::Dict(_) => todo!(),
            Expression::Lambda(arg, body) => {
                Expression::Lambda(arg.map_t_ref(f), Box::new(body.map_t_ref(f)))
            }
            Expression::Let(arms, body) => {
                let h = Box::new(body.map_t_ref(f));
                let mut binds = vec![];
                for b in arms {
                    iters(&mut binds, &mut || b.map_t_ref(f))
                }
                Expression::Let(binds, h)
            }
            Expression::App(x, y) => {
                Expression::App(Box::new(x.map_t_ref(f)), Box::new(y.map_t_ref(f)))
            }
            Expression::Cond(xyz) => {
                let [x, y, z] = xyz.as_ref();
                Expression::Cond(Box::new([x.map_t_ref(f), y.map_t_ref(f), z.map_t_ref(f)]))
            }
            Expression::Case(ex, arms) => Expression::Case(
                Box::new(ex.map_t_ref(f)),
                arms.into_iter()
                    .map(
                        |Alternative {
                             body,
                             pat,
                             pred,
                             wher,
                         }| Alternative {
                            pat: pat.map_t_ref(f),
                            pred: if let Some(pred) = pred {
                                Some(pred.map_t_ref(f))
                            } else {
                                None
                            },
                            body: body.map_t_ref(f),
                            wher: wher.into_iter().map(|b| b.map_t_ref(f)).collect(),
                        },
                    )
                    .collect(),
            ),
            Expression::Cast(x, ty) => Expression::Cast(Box::new(x.map_t_ref(f)), ty.map_t_ref(f)),
            Expression::Do(stmts, last) => Expression::Do(
                stmts.into_iter().map(|stmt| stmt.map_t_ref(f)).collect(),
                Box::new(last.map_t_ref(f)),
            ),
            Expression::Range(a, b) => Expression::Range(
                Box::new(a.map_t_ref(f)),
                if let Some(end) = b {
                    Some(Box::new(end.map_t_ref(f)))
                } else {
                    None
                },
            ),
            Expression::Group(x) => Expression::Group(Box::new(x.map_t_ref(f))),
        }
    }
}

pub fn try_expr_into_pat<Id: Identifier, T>(expr: Expression<Id, T>) -> Option<Pattern<Id, T>> {
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
        Expression::Range(_, _) => todo!(),
        Expression::Group(x) => try_expr_into_pat(*x),
    }
}

#[cfg(test)]
mod tests {
    use wy_common::Mappable;
    use wy_intern::symbol;

    use super::*;

    #[test]
    fn test_flatten_app() {
        let [f, g, h]: [RawExpression; 3] =
            symbol::intern_many(["f", "g", "h"]).fmap(|sym| Expression::Ident(Ident::Lower(sym)));
        let [one, three, four]: [RawExpression; 3] =
            [1, 3, 4].fmap(|n| Expression::Lit(Literal::Int(n)));

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
