use wy_lexer::Literal;

use crate::{
    ident::Ident,
    tipo::{Record, Type},
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
    pub fn map_t<F, U>(self, mut f: F) -> Pattern<Id, U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Pattern::Wild => Pattern::Wild,
            Pattern::Var(t) => Pattern::Var(t),
            Pattern::Lit(lit) => Pattern::Lit(lit),
            Pattern::Dat(a, bs) => {
                Pattern::Dat(a, bs.into_iter().map(|p| p.map_t(|t| f(t))).collect())
            }
            Pattern::Tup(ps) => Pattern::Tup(ps.into_iter().map(|t| t.map_t(|t| f(t))).collect()),
            Pattern::Vec(ps) => Pattern::Vec(ps.into_iter().map(|t| t.map_t(|t| f(t))).collect()),
            Pattern::Lnk(x, y) => {
                Pattern::Lnk(Box::new(x.map_t(|t| f(t))), Box::new(y.map_t(|t| f(t))))
            }
            Pattern::At(id, pat) => Pattern::At(id, Box::new(pat.map_t(|t| f(t)))),
            Pattern::Or(ps) => Pattern::Or(ps.into_iter().map(|p| p.map_t(|t| f(t))).collect()),
            Pattern::Rec(rec) => Pattern::Rec(rec.map_t(|pat| pat.map_t(|t| f(t)))),
            Pattern::Cast(pat, ty) => {
                Pattern::Cast(Box::new(pat.map_t(|t| f(t))), ty.map_t(&mut f))
            }
        }
    }
}
