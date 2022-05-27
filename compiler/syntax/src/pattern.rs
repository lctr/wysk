use wy_common::{functor::Bifunctor, Mappable, Set};
use wy_lexer::Literal;

use crate::{
    ident::Ident,
    tipo::{Con, Field, Record, Type},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern<Id = Ident, T = Ident> {
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
    Rec(Record<Pattern<Id, T>, Id>),
    Cast(Box<Pattern<Id, T>>, Type<Id, T>),
}

impl<Id, T> Pattern<Id, T> {
    pub const UNIT: Self = Self::Tup(vec![]);
    pub const NIL: Self = Self::Vec(vec![]);
    pub const VOID: Self = Self::Rec(Record::VOID);
    pub fn is_unit(&self) -> bool {
        matches!(self, Self::Tup(vs) if vs.is_empty())
    }
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Vec(vs) if vs.is_empty())
    }
    pub fn is_void(&self) -> bool {
        matches!(self, Self::Rec(Record::Anon(vs)) if vs.is_empty())
    }
    pub fn is_empty_record(&self) -> bool {
        matches!(self, Self::Rec(Record::Anon(fs)|Record::Data(_, fs)) if fs.is_empty() )
    }
    pub fn vars(&self) -> Set<Id>
    where
        Id: Copy + Eq + std::hash::Hash,
    {
        let mut vars = Set::new();
        match self {
            Pattern::Wild => todo!(),
            Pattern::Var(id) => {
                vars.insert(*id);
            }
            Pattern::Lit(_) => todo!(),
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
        };
        vars
    }

    pub fn map_id<F, X>(self, mut f: F) -> Pattern<X, T>
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Pattern::Wild => Pattern::Wild,
            Pattern::Var(id) => Pattern::Var(f(id)),
            Pattern::Lit(k) => Pattern::Lit(k),
            Pattern::Dat(id, tail) => Pattern::Dat(
                f(id),
                tail.into_iter().map(|p| p.map_id(|id| f(id))).collect(),
            ),
            Pattern::Tup(ts) => {
                Pattern::Tup(ts.into_iter().map(|p| p.map_id(|id| f(id))).collect())
            }
            Pattern::Vec(ts) => {
                Pattern::Vec(ts.into_iter().map(|p| p.map_id(|id| f(id))).collect())
            }
            Pattern::Lnk(x, y) => Pattern::Lnk(
                Box::new(x.map_id(|id| f(id))),
                Box::new(y.map_id(|id| f(id))),
            ),
            Pattern::At(id, p) => Pattern::At(f(id), Box::new(p.map_id(|id| f(id)))),
            Pattern::Or(ps) => Pattern::Or(ps.into_iter().map(|p| p.map_id(|id| f(id))).collect()),
            Pattern::Rec(rec) => {
                Pattern::Rec(rec.map_id(|id| f(id)).map_t(|pat| pat.map_id(|id| f(id))))
            }
            Pattern::Cast(pat, ty) => {
                Pattern::Cast(Box::new(pat.map_id(|id| f(id))), ty.map_id(&mut f))
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
            Pattern::Dat(_, _) => todo!(),
            Pattern::Tup(ts) => {
                if ts.is_empty() {
                    Pattern::UNIT
                } else {
                    Pattern::Tup(ts.fmap(|p| p.map_t(f)))
                }
            }
            Pattern::Vec(ts) => {
                if ts.is_empty() {
                    Pattern::NIL
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
                    Pattern::NIL
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
        }
    }
}
