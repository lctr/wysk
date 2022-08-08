use super::tipo::Type;
use crate::record::Record;
use serde::{Deserialize, Serialize};
use wy_common::{
    functor::{MapFst, MapSnd},
    variant_preds, Set,
};
use wy_lexer::literal::Literal;
use wy_name::ident::Ident;

variant_preds! { |Id, V| Pattern[Id, V]
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
pub enum Pattern<Id, V> {
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
    Dat(Id, Vec<Pattern<Id, V>>),
    Tup(Vec<Pattern<Id, V>>),
    /// Describes a list formed with array-like bracket syntax, e.g.,
    /// `[a, b, c]`. Syntactic sugar for lists.
    Vec(Vec<Pattern<Id, V>>),
    /// Describes a list formed with cons operator infix syntax, e.g.,
    /// `(a:b:c)`. Note that *as a pattern*, this *must* occur within
    /// parentheses, as *operator fixities are not observed in patterns*.
    Lnk(Box<Pattern<Id, V>>, Box<Pattern<Id, V>>),
    At(Id, Box<Pattern<Id, V>>),
    Or(Vec<Pattern<Id, V>>),
    Rec(Record<Id, Pattern<Id, V>>),
    Cast(Box<Pattern<Id, V>>, Type<Id, V>),
    Rng(Box<Pattern<Id, V>>, Option<Box<Pattern<Id, V>>>),
}

impl<Id, V> Pattern<Id, V> {
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
                    let vars = first.idents();
                    for pat in rest {
                        if vars != pat.idents() {
                            return false;
                        }
                    }
                    true
                }
            },
            Self::At(id, pat) => pat.uniformly_bound_ors() && !pat.idents().contains(id),
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
    pub fn idents(&self) -> Set<&Id>
    where
        Id: Eq + std::hash::Hash,
    {
        let mut vars = Set::new();
        match self {
            Pattern::Wild | Pattern::Lit(_) => (),
            Pattern::Var(id) => {
                vars.insert(id);
            }
            Pattern::Dat(_, ps) | Pattern::Tup(ps) | Pattern::Vec(ps) | Pattern::Or(ps) => {
                for p in ps {
                    vars.extend(p.idents())
                }
            }
            Pattern::Lnk(x, y) => {
                vars.extend(x.idents());
                vars.extend(y.idents());
            }
            Pattern::At(x, y) => {
                vars.insert(x);
                vars.extend(y.idents());
            }
            Pattern::Rec(rec) => rec.fields().into_iter().for_each(|field| {
                if let Some(key) = field.get_key() {
                    vars.insert(key);
                }
                if let Some(val) = field.get_value() {
                    vars.extend(val.idents())
                }
            }),
            Pattern::Cast(p, _) => {
                vars.extend(p.idents());
            }
            Pattern::Rng(a, b) => {
                vars.extend(a.idents());
                if let Some(c) = b {
                    vars.extend(c.idents())
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
}

impl<Id, V, X> MapFst<Id, X> for Pattern<Id, V> {
    type WrapFst = Pattern<X, V>;

    fn map_fst<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Pattern::Wild => Pattern::Wild,
            Pattern::Var(id) => Pattern::Var(f.apply(id)),
            Pattern::Lit(lit) => Pattern::Lit(lit),
            Pattern::Dat(id, args) => Pattern::Dat(f.apply(id), args.map_fst(f)),
            Pattern::Tup(pats) => Pattern::Tup(pats.map_fst(f)),
            Pattern::Vec(pats) => Pattern::Vec(pats.map_fst(f)),
            Pattern::Lnk(head, tail) => {
                let head = head.map_fst(f);
                let tail = tail.map_fst(f);
                Pattern::Lnk(Box::new(head), Box::new(tail))
            }
            Pattern::At(id, pat) => {
                let id = f.apply(id);
                let pat = pat.map_fst(f);
                Pattern::At(id, Box::new(pat))
            }
            Pattern::Or(pats) => Pattern::Or(pats.map_fst(f)),
            Pattern::Rec(rec) => Pattern::Rec(rec.map_fst(f)),
            Pattern::Cast(pat, ty) => Pattern::Cast(Box::new(pat.map_fst(f)), ty.map_fst(f)),
            Pattern::Rng(a, b) => {
                let a = Box::new(a.map_fst(f));
                let b = b.map(|p| Box::new(p.map_fst(f)));
                Pattern::Rng(a, b)
            }
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Pattern<Id, V> {
    type WrapSnd = Pattern<Id, X>;

    fn map_snd<F>(self, f: &mut wy_common::functor::Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Pattern::Wild => Pattern::Wild,
            Pattern::Var(id) => Pattern::Var(id),
            Pattern::Lit(lit) => Pattern::Lit(lit),
            Pattern::Dat(id, args) => Pattern::Dat(id, args.map_snd(f)),
            Pattern::Tup(pats) => Pattern::Tup(pats.map_snd(f)),
            Pattern::Vec(pats) => Pattern::Vec(pats.map_snd(f)),
            Pattern::Lnk(head, tail) => {
                let head = head.map_snd(f);
                let tail = tail.map_snd(f);
                Pattern::Lnk(Box::new(head), Box::new(tail))
            }
            Pattern::At(id, pat) => Pattern::At(id, Box::new(pat.map_snd(f))),
            Pattern::Or(pats) => Pattern::Or(pats.map_snd(f)),
            Pattern::Rec(rec) => Pattern::Rec(rec.map_snd(f)),
            Pattern::Cast(pat, ty) => Pattern::Cast(Box::new(pat.map_snd(f)), ty.map_snd(f)),
            Pattern::Rng(a, b) => {
                let a = Box::new(a.map_snd(f));
                let b = b.map(|p| Box::new(p.map_snd(f)));
                Pattern::Rng(a, b)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use wy_intern::Symbol;

    use super::*;

    #[test]
    fn test_pat_dupe_binders() {
        use crate::Tv;
        use crate::Type;
        use wy_name::ident::Ident::{self, Lower};
        use Pattern::*;
        let [a, b, c, d, e, f, g] =
            Symbol::intern_many_with(["a", "b", "c", "d", "e", "f", "g"], Lower);
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
