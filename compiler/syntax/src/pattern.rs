use crate::tipo::{Con, Field, Record, Type};
use serde::{Deserialize, Serialize};
use wy_common::{variant_preds, Mappable, Set};
use wy_lexer::literal::Literal;
use wy_name::ident::Ident;

variant_preds! { |Id, T| Pattern[Id, T]
    | is_wild => Wild
    | is_var => Var (_)
    | is_unit => Tup (vs) [if vs.is_empty()]
    | is_nil => Vec (vs) [if vs.is_empty()]
    | is_data => Dat (..)
    | is_nullary_data => Dat (_, vs) [if vs.is_empty()]
    | is_void => Rec (Record::Anon(entries)) [if entries.is_empty()]
    | is_partial_record => Rec (rec) [if rec.has_rest()]
    | is_lit => Lit (_)

}

pub type RawPattern = Pattern<Ident, Ident>;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Pattern<Id, T> {
    /// Describes the wildcard pattern and is written `_`. Since it is a
    /// wildcard pattern, it matches against *any* pattern.
    Wild,
    /// Describes a named wildxard pattern and syntactically corresponds to *any
    /// lowercase-initial identifier*. The pattern `a` is a `Var` pattern and
    /// can be rewritten as the `At` pattern `a @ _`, so it follows that this
    /// pattern matches against *any* pattern, but *also* introduces a
    /// *binding* between the identifier and the element being matched on.
    Var(Id),
    /// Describes a literal as a pattern and is the one variant of patterns with
    /// specific restrictions.
    Lit(Literal),
    /// Describes the pattern formed by a data constructor and its arguments
    /// (data). In particular, the data constructor *must* be an
    /// uppercase-initial identifier.
    Dat(Id, Vec<Pattern<Id, T>>),
    Tup(Vec<Pattern<Id, T>>),
    /// Describes a list formed with array-like bracket syntax, e.g.,
    /// `[a, b, c]`. Syntactic sugar for lists.
    Vec(Vec<Pattern<Id, T>>),
    /// Describes a list formed with cons operator infix syntax, e.g.,
    /// `(a:b:c)`. Note that *as a pattern*, this *must* occur within
    /// parentheses, as *operator fixities are not observed in patterns*.
    Lnk(Box<Pattern<Id, T>>, Box<Pattern<Id, T>>),
    At(Id, Box<Pattern<Id, T>>),
    Or(Vec<Pattern<Id, T>>),
    Rec(Record<Id, Pattern<Id, T>>),
    Cast(Box<Pattern<Id, T>>, Type<Id, T>),
    Rng(Box<Pattern<Id, T>>, Option<Box<Pattern<Id, T>>>),
}

impl<Id, T> Pattern<Id, T> {
    pub const UNIT: Self = Self::Tup(vec![]);
    pub const NULL: Self = Self::Vec(vec![]);

    /// Checks whether a pattern is a valid lambda argument pattern. A valid
    /// lambda pattern is an irrefutable pattern, i.e., a pattern that is
    /// guaranteed to match the scrutinee.
    ///
    /// Rejected patterns include `or` patterns, `literal` patterns, constructor
    /// patterns (since this particular method doesn't have access to the list
    /// of all constructors of a data type), list-like patterns, range patterns
    /// (since they are syntactic sugar for list-like patterns) and record
    /// patterns.
    ///
    /// This check exists since lambdas *may not* be partial functions.
    pub fn is_valid_lambda_pat(&self) -> bool {
        match self {
            Pattern::Wild | Pattern::Var(_) => true,
            Pattern::Tup(ps) => ps.into_iter().all(Self::is_valid_lambda_pat),
            Pattern::At(_, p) | Pattern::Cast(p, _) => p.is_valid_lambda_pat(),
            Pattern::Lit(_)
            | Pattern::Dat(_, _)
            | Pattern::Vec(_)
            | Pattern::Lnk(_, _)
            | Pattern::Or(_)
            | Pattern::Rec(_)
            | Pattern::Rng(_, _) => false,
        }
    }

    /// Checks whether all variable binders introduced by a pattern (and its
    /// subpatterns) are NOT repeated; note that the only variant for which
    /// repeated binders are valid is for `or` patterns, where all alternatives
    /// *must* contain the same variable binders, unlike the other variants.
    pub fn has_repeated_binders(&self) -> bool
    where
        Id: Eq + std::hash::Hash,
    {
        let mut set = Set::new();
        let mut dupe = false;
        fn check<'a, A: Eq + std::hash::Hash, B>(
            set: &mut Set<&'a A>,
            p: &'a Pattern<A, B>,
            dupe: &mut bool,
        ) {
            for a in p.binders() {
                if *dupe {
                    break;
                } else {
                    *dupe = !set.insert(a);
                }
            }
        }
        match self {
            Pattern::Wild | Pattern::Var(_) | Pattern::Lit(_) => (),
            Pattern::Dat(k, ps) => {
                if set.contains(k) {
                    dupe = true
                } else {
                    for p in ps {
                        if dupe {
                            break;
                        } else {
                            check(&mut set, p, &mut dupe)
                        }
                    }
                }
            }
            Pattern::Tup(ps) | Pattern::Vec(ps) => {
                for p in ps {
                    if dupe {
                        break;
                    } else {
                        check(&mut set, p, &mut dupe)
                    }
                }
            }
            Pattern::Lnk(pa, pb) => {
                check(&mut set, pa.as_ref(), &mut dupe);
                if !dupe {
                    check(&mut set, pb.as_ref(), &mut dupe)
                }
            }
            Pattern::At(id, p) => {
                if set.contains(id) {
                    dupe = true
                } else {
                    check(&mut set, p.as_ref(), &mut dupe)
                }
            }
            Pattern::Or(ps) => dupe = ps.into_iter().any(Self::has_repeated_binders),
            Pattern::Rec(rec) => {
                if let Some(k) = rec.ctor() {
                    if set.contains(k) {
                        dupe = true;
                    } else {
                        set.insert(k);
                    }
                }
                for fld in rec.fields() {
                    if dupe {
                        break;
                    } else {
                        if let Some(k) = fld.get_key() {
                            if set.contains(k) {
                                dupe = true;
                                break;
                            } else {
                                set.insert(k);
                            }
                        }
                        if let Some(p) = fld.get_value() {
                            check(&mut set, p, &mut dupe)
                        }
                    }
                }
            }
            Pattern::Cast(p, _) => check(&mut set, p.as_ref(), &mut dupe),
            Pattern::Rng(pa, pb) => {
                check(&mut set, pa.as_ref(), &mut dupe);
                if !dupe {
                    if let Some(p) = pb {
                        check(&mut set, p.as_ref(), &mut dupe)
                    }
                }
            }
        };
        dupe
    }

    /// Recursively checks whether all the sub-patterns in an `or` pattern bind
    /// the same identifiers. If a given pattern is not an `or` pattern, then
    /// this checks any subpatterns for `or` patterns to which this method will
    /// be applied.
    pub fn uniformly_bound_ors(&self) -> bool
    where
        Id: Eq + Copy + std::hash::Hash,
    {
        match self {
            Self::Or(alts) => match &alts[..] {
                [] => true,
                [first, rest @ ..] => {
                    let vars = first.vars();
                    for pat in rest {
                        if vars != pat.vars() {
                            return false;
                        }
                    }
                    true
                }
            },
            Self::At(id, pat) => pat.uniformly_bound_ors() && !pat.vars().contains(id),
            Self::Tup(pats) | Self::Vec(pats) | Self::Dat(_, pats) => {
                pats.into_iter().all(|pat| pat.uniformly_bound_ors())
            }
            Self::Cast(pat, _) => pat.uniformly_bound_ors(),
            Self::Lnk(a, b) => a.uniformly_bound_ors() && b.uniformly_bound_ors(),
            Self::Rec(rec) => rec.fields().into_iter().all(|field| {
                field
                    .get_value()
                    .map_or_else(|| true, Self::uniformly_bound_ors)
            }),
            Self::Rng(a, None) => a.uniformly_bound_ors(),
            Self::Rng(a, Some(b)) => a.uniformly_bound_ors() && b.uniformly_bound_ors(),
            Self::Wild | Self::Var(_) | Self::Lit(_) => true,
        }
    }

    pub fn is_empty_record(&self) -> bool {
        matches!(self, Self::Rec(Record::Anon(fs)|Record::Data(_, fs)) if fs.is_empty() )
    }

    /// Returns a hashset containing all variable identifiers bound within a
    /// pattern. Since this method returns a hashset, it is not suitable for
    /// checking for duplicates or variable identifier order: use the `binders`
    /// method instead, which returns a vector of variable identifiers
    /// potentially containing duplicates.
    pub fn vars(&self) -> Set<Id>
    where
        Id: Copy + Eq + std::hash::Hash,
    {
        let mut vars = Set::new();
        match self {
            Pattern::Wild | Pattern::Lit(_) => (),
            Pattern::Var(id) => {
                vars.insert(*id);
            }
            Pattern::Dat(_, ps) | Pattern::Tup(ps) | Pattern::Vec(ps) | Pattern::Or(ps) => {
                for p in ps {
                    vars.extend(p.vars())
                }
            }
            Pattern::Lnk(x, y) => {
                vars.extend(x.vars());
                vars.extend(y.vars());
            }
            Pattern::At(x, y) => {
                vars.insert(*x);
                vars.extend(y.vars());
            }
            Pattern::Rec(rec) => rec.fields().into_iter().for_each(|field| {
                if let Some(key) = field.get_key() {
                    vars.insert(*key);
                }
                if let Some(val) = field.get_value() {
                    vars.extend(val.vars())
                }
            }),
            Pattern::Cast(p, _) => {
                vars.extend(p.vars());
            }
            Pattern::Rng(a, b) => {
                vars.extend(a.vars());
                if let Some(c) = b {
                    vars.extend(c.vars())
                }
            }
        };
        vars
    }

    /// Returns a list of references to all the variable binders introduced by a
    /// pattern, including duplicates.
    pub fn binders(&self) -> Vec<&Id>
    where
        Id: PartialEq,
    {
        let mut vars = Vec::new();
        match self {
            Pattern::Wild | Pattern::Lit(_) => (),
            Pattern::Var(id) => {
                vars.push(id);
            }
            Pattern::Dat(_, ps) | Pattern::Tup(ps) | Pattern::Vec(ps) | Pattern::Or(ps) => {
                for p in ps {
                    vars.extend(p.binders())
                }
            }
            Pattern::Lnk(x, y) => {
                vars.extend(x.binders());
                vars.extend(y.binders());
            }
            Pattern::At(x, y) => {
                vars.push(x);
                vars.extend(y.binders());
            }
            Pattern::Rec(rec) => rec.fields().into_iter().for_each(|field| {
                if let Some(key) = field.get_key() {
                    vars.push(key);
                }
                if let Some(val) = field.get_value() {
                    vars.extend(val.binders())
                }
            }),
            Pattern::Cast(p, _) => {
                vars.extend(p.binders());
            }
            Pattern::Rng(a, b) => {
                vars.extend(a.binders());
                if let Some(c) = b {
                    vars.extend(c.binders())
                }
            }
        };
        vars
    }

    /// Checks whether a given pattern is able to be directly re-interpreted as
    /// an expression
    pub fn valid_expr(&self) -> bool {
        match self {
            Pattern::Wild | Pattern::At(_, _) | Pattern::Or(_) => false,
            Pattern::Var(_) | Pattern::Lit(_) => true,
            Pattern::Dat(_, xs) | Pattern::Tup(xs) | Pattern::Vec(xs) => {
                xs.into_iter().all(|pat| pat.valid_expr())
            }
            Pattern::Lnk(x, y) => x.valid_expr() && y.valid_expr(),
            Pattern::Rec(rec) => rec.fields().into_iter().all(|field| {
                field
                    .get_value()
                    .map(|pat| pat.valid_expr())
                    .unwrap_or_else(|| false)
            }),
            Pattern::Cast(pat, _) => pat.valid_expr(),
            Pattern::Rng(a, b) => {
                a.valid_expr() && b.as_ref().map(|p| p.valid_expr()).unwrap_or_else(|| true)
            }
        }
    }

    pub fn map_id<X>(self, f: &mut impl FnMut(Id) -> X) -> Pattern<X, T> {
        match self {
            Pattern::Wild => Pattern::Wild,
            Pattern::Var(id) => Pattern::Var(f(id)),
            Pattern::Lit(k) => Pattern::Lit(k),
            Pattern::Dat(id, tail) => {
                Pattern::Dat(f(id), tail.into_iter().map(|p| p.map_id(f)).collect())
            }
            Pattern::Tup(ts) => Pattern::Tup(ts.into_iter().map(|p| p.map_id(f)).collect()),
            Pattern::Vec(ts) => Pattern::Vec(ts.into_iter().map(|p| p.map_id(f)).collect()),
            Pattern::Lnk(x, y) => Pattern::Lnk(Box::new(x.map_id(f)), Box::new(y.map_id(f))),
            Pattern::At(id, p) => Pattern::At(f(id), Box::new(p.map_id(f))),
            Pattern::Or(ps) => Pattern::Or(ps.into_iter().map(|p| p.map_id(f)).collect()),
            Pattern::Rec(rec) => Pattern::Rec(rec.map_id(|id| f(id)).map_t(|pat| pat.map_id(f))),
            Pattern::Cast(pat, ty) => Pattern::Cast(Box::new(pat.map_id(f)), ty.map_id(f)),
            Pattern::Rng(a, None) => Pattern::Rng(Box::new(a.map_id(f)), None),
            Pattern::Rng(a, Some(b)) => {
                let x = a.map_id(f);
                let y = b.map_id(f);
                Pattern::Rng(Box::new(x), Some(Box::new(y)))
            }
        }
    }
    pub fn map_id_ref<U>(&self, f: &mut impl FnMut(&Id) -> U) -> Pattern<U, T>
    where
        T: Copy,
    {
        match self {
            Pattern::Wild => Pattern::Wild,
            Pattern::Var(id) => Pattern::Var(f(id)),
            Pattern::Lit(k) => Pattern::Lit(*k),
            Pattern::Dat(id, tail) => {
                Pattern::Dat(f(id), tail.into_iter().map(|p| p.map_id_ref(f)).collect())
            }
            Pattern::Tup(ts) => Pattern::Tup(ts.into_iter().map(|p| p.map_id_ref(f)).collect()),
            Pattern::Vec(ts) => Pattern::Vec(ts.into_iter().map(|p| p.map_id_ref(f)).collect()),
            Pattern::Lnk(x, y) => {
                Pattern::Lnk(Box::new(x.map_id_ref(f)), Box::new(y.map_id_ref(f)))
            }
            Pattern::At(id, p) => Pattern::At(f(id), Box::new(p.map_id_ref(f))),
            Pattern::Or(ps) => Pattern::Or(ps.into_iter().map(|p| p.map_id_ref(f)).collect()),
            Pattern::Rec(rec) => Pattern::Rec(rec.map_ref(&mut |con, fields| {
                (
                    con.as_ref().map(|id| f(id)),
                    fields
                        .into_iter()
                        .map(|field| {
                            field.map_ref(&mut |(lhs, rhs)| {
                                (f(&lhs), rhs.as_ref().map(|pat| pat.map_id_ref(f)))
                            })
                        })
                        .collect(),
                )
            })),
            Pattern::Cast(pat, ty) => Pattern::Cast(Box::new(pat.map_id_ref(f)), ty.map_id_ref(f)),
            Pattern::Rng(a, b) => Pattern::Rng(
                Box::new(a.as_ref().map_id_ref(f)),
                b.as_ref().map(|c| Box::new(c.map_id_ref(f))),
            ),
        }
    }
    pub fn map_t<F, U>(self, f: &mut F) -> Pattern<Id, U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Pattern::Wild => Pattern::Wild,
            Pattern::Var(t) => Pattern::Var(t),
            Pattern::Lit(lit) => Pattern::Lit(lit),
            Pattern::Dat(con, args) => {
                let mut pargs = vec![];
                for arg in args {
                    pargs.push(arg.map_t(f));
                }
                Pattern::Dat(con, pargs)
            }
            Pattern::Tup(ts) => {
                if ts.is_empty() {
                    Pattern::UNIT
                } else {
                    Pattern::Tup(ts.fmap(|p| p.map_t(f)))
                }
            }
            Pattern::Vec(ts) => {
                if ts.is_empty() {
                    Pattern::NULL
                } else {
                    Pattern::Vec(ts.fmap(|p| p.map_t(f)))
                }
            }
            Pattern::Lnk(x, y) => {
                let x = Box::new(x.map_t(f));
                let y = Box::new(y.map_t(f));
                Pattern::Lnk(x, y)
            }
            Pattern::At(id, ps) => Pattern::At(id, Box::new(ps.map_t(f))),
            Pattern::Or(ps) => Pattern::Or(ps.fmap(|p| p.map_t(f))),
            Pattern::Rec(rec) => {
                let (cted, fields) = match rec {
                    Record::Anon(fs) => (None, fs),
                    Record::Data(con, fs) => (Some(con), fs),
                };
                let fields = fields.fmap(|field| match field {
                    Field::Rest => Field::Rest,
                    Field::Key(k) => Field::Key(k),
                    Field::Entry(k, v) => Field::Entry(k, v.map_t(f)),
                });
                let record = match cted {
                    Some(k) => Record::Data(k, fields),
                    None => Record::Anon(fields),
                };
                Pattern::Rec(record)
            }
            Pattern::Cast(pat, ty) => {
                fn map_ty<A, B, C>(ty: Type<A, B>, f: &mut impl FnMut(B) -> C) -> Type<A, C> {
                    match ty {
                        Type::Var(v) => Type::Var(f(v)),
                        Type::Con(id, args) => {
                            Type::Con(id.map_t(|b| f(b)), args.fmap(|ty| map_ty(ty, f)))
                        }
                        Type::Fun(x, y) => {
                            Type::Fun(Box::new(map_ty(*x, f)), Box::new(map_ty(*y, f)))
                        }
                        Type::Tup(ts) => Type::Tup(ts.fmap(|ty| map_ty(ty, f))),
                        Type::Vec(t) => Type::Vec(Box::new(map_ty(*t, f))),
                        Type::Rec(recs) => {
                            let (k, fs) = match recs {
                                Record::Anon(fs) => (None, fs),
                                Record::Data(k, fs) => (Some(k), fs),
                            };
                            let fields = fs.fmap(|field| match field {
                                Field::Rest => Field::Rest,
                                Field::Key(k) => Field::Key(k),
                                Field::Entry(k, v) => Field::Entry(k, map_ty(v, f)),
                            });
                            Type::Rec(if let Some(k) = k {
                                Record::Data(k, fields)
                            } else {
                                Record::Anon(fields)
                            })
                        }
                    }
                }

                let pat = Box::new(pat.map_t(f));
                let tipo = map_ty(ty, f);
                Pattern::Cast(pat, tipo)
            }
            Pattern::Rng(a, b) => {
                Pattern::Rng(a.fmap(|p| p.map_t(f)), b.fmap(|bp| bp.fmap(|p| p.map_t(f))))
            }
        }
    }

    pub fn map_t_ref<U>(&self, f: &mut impl FnMut(&T) -> U) -> Pattern<Id, U>
    where
        Id: Copy,
    {
        match self {
            Pattern::Wild => Pattern::Wild,
            Pattern::Var(t) => Pattern::Var(*t),
            Pattern::Lit(lit) => Pattern::Lit(*lit),
            Pattern::Dat(id, args) => {
                Pattern::Dat(*id, args.into_iter().map(|pat| pat.map_t_ref(f)).collect())
            }
            Pattern::Tup(ts) => {
                if ts.is_empty() {
                    Pattern::UNIT
                } else {
                    Pattern::Tup(ts.into_iter().map(|p| p.map_t_ref(f)).collect())
                }
            }
            Pattern::Vec(ts) => {
                if ts.is_empty() {
                    Pattern::NULL
                } else {
                    Pattern::Vec(ts.into_iter().map(|p| p.map_t_ref(f)).collect())
                }
            }
            Pattern::Lnk(x, y) => {
                let x = Box::new(x.map_t_ref(f));
                let y = Box::new(y.map_t_ref(f));
                Pattern::Lnk(x, y)
            }
            Pattern::At(id, ps) => Pattern::At(*id, Box::new(ps.map_t_ref(f))),
            Pattern::Or(ps) => Pattern::Or(ps.into_iter().map(|p| p.map_t_ref(f)).collect()),
            Pattern::Rec(rec) => {
                let (cted, fields) = match rec {
                    Record::Anon(fs) => (None, fs),
                    Record::Data(con, fs) => (Some(*con), fs),
                };
                let fields = fields
                    .into_iter()
                    .map(|field| match field {
                        Field::Rest => Field::Rest,
                        Field::Key(k) => Field::Key(*k),
                        Field::Entry(k, v) => Field::Entry(*k, v.map_t_ref(f)),
                    })
                    .collect();
                let record = match cted {
                    Some(k) => Record::Data(k, fields),
                    None => Record::Anon(fields),
                };
                Pattern::Rec(record)
            }
            Pattern::Cast(pat, ty) => {
                fn map_ty<A: Copy, B, C>(
                    ty: &Type<A, B>,
                    f: &mut impl FnMut(&B) -> C,
                ) -> Type<A, C> {
                    match ty {
                        Type::Var(v) => Type::Var(f(v)),
                        Type::Con(id, args) => Type::Con(
                            match id {
                                Con::List => Con::List,
                                Con::Tuple(n) => Con::Tuple(*n),
                                Con::Arrow => Con::Arrow,
                                Con::Data(d) => Con::Data(*d),
                                Con::Free(t) => Con::Free(f(t)),
                                Con::Alias(id) => Con::Alias(*id),
                            },
                            args.into_iter().map(|ty| map_ty(ty, f)).collect(),
                        ),
                        Type::Fun(x, y) => Type::Fun(
                            Box::new(map_ty(x.as_ref(), f)),
                            Box::new(map_ty(y.as_ref(), f)),
                        ),
                        Type::Tup(ts) => {
                            Type::Tup(ts.into_iter().map(|ty| map_ty(ty, f)).collect())
                        }
                        Type::Vec(t) => Type::Vec(Box::new(map_ty(t, f))),
                        Type::Rec(recs) => {
                            let (k, fs) = match recs {
                                Record::Anon(fs) => (None, fs),
                                Record::Data(k, fs) => (Some(*k), fs),
                            };
                            let fields = fs
                                .into_iter()
                                .map(|field| match field {
                                    Field::Rest => Field::Rest,
                                    Field::Key(k) => Field::Key(*k),
                                    Field::Entry(k, v) => Field::Entry(*k, map_ty(v, f)),
                                })
                                .collect();
                            Type::Rec(if let Some(k) = k {
                                Record::Data(k, fields)
                            } else {
                                Record::Anon(fields)
                            })
                        }
                    }
                }

                let pat = Box::new(pat.map_t_ref(f));
                let tipo = map_ty(ty, f);
                Pattern::Cast(pat, tipo)
            }
            Pattern::Rng(_, _) => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use wy_name::ident::*;

    #[test]
    fn test_map_id() {
        let [a, b, c] = wy_intern::intern_many_with(["a", "b", "c"], wy_name::ident::Ident::Lower);
        let pat: Pattern<Ident, ()> = Pattern::Rng(Box::new(Pattern::Var(a)), None);
        let pat2 = pat.map_id(&mut |id| Chain::from((b, [c, id])));
        println!("{:?}", pat2)
    }

    #[test]
    fn test_pat_dupe_binders() {
        use crate::Tv;
        use crate::Type;
        use wy_name::ident::Ident::{self, Lower};
        use Pattern::*;
        let [a, b, c, d, e, f, g] =
            wy_intern::intern_many_with(["a", "b", "c", "d", "e", "f", "g"], Lower);
        let pat_with_dupe_vars = Tup(vec![
            Var(a),
            Var(b),
            Tup(vec![
                Var(c),
                Lnk(
                    Box::new(Var(d)),
                    Box::new(Vec(vec![
                        Var(e),
                        Var(f),
                        Wild,
                        Rng(Box::new(Var(f)), Some(Box::new(Var(a)))),
                    ])),
                ),
            ]),
            Cast(Box::new(Var(c)), Type::Var(Tv(0))),
        ]);
        let pat_without_dupe_vars = Tup(vec![
            Var(a),
            Var(b),
            Tup(vec![
                Var(c),
                Lnk(
                    Box::new(Var(d)),
                    Box::new(Tup(vec![
                        Var(e),
                        Var(f),
                        Wild,
                        Vec(vec![Var(g), Cast(Box::new(Wild), Type::Var(Tv(0)))]),
                    ])),
                ),
            ]),
        ]);
        let p_w_dupes = pat_with_dupe_vars.has_repeated_binders();
        let p_wo_dupes = pat_without_dupe_vars.has_repeated_binders();
        println!(
            "\
            unit has dupes: {}\n\
            pat_with_dupe_vars has dupes: {}\n\
            pat_without_dupe_vars has dupes: {}\n\
            ",
            Pattern::<Ident, Tv>::UNIT.has_repeated_binders(),
            p_w_dupes,
            p_wo_dupes
        );
    }
}
