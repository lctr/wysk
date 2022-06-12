use wy_common::{push_if_absent, Deque, Map, Set};
use wy_syntax::{
    ident::Ident,
    tipo::{Con, Tv, Type as Type_, Var},
};

use super::subst::{Subst, Substitutable};

pub type Type = Type_<Ident, Tv>;
pub type TyCon = Con<Ident, Tv>;

wy_common::newtype! {
    /// Index newtype representing *constrained type variables*, used to index
    /// into a vector of type variables `Tv`. This is used to keep a `Scheme`'s
    /// type variables in one location while describing which type variables are
    /// class instances.
    usize in Ctv | New Show AsUsize [Tv]
}

#[derive(Clone, PartialEq, Eq)]
/// A `Scheme` represents a *sigma* type or a *type scheme*. It carries a `Type`
/// ("tau") value as well as a list of *type variables*, and represents a type
/// that is potentially quantified over its outermost type variables.
///
/// ---
/// * a __monotype__ `mu` is a type containing no type variables
/// * a __type scheme__ `sigma` may be interpreted in the following
///   syntactically distinct (but semantically equivalent) forms:
///     - `forall a_1 . forall a_2 ... forall a_n tau`
///     - `forall a_1 ... a_n . tau`
///   where `tau` is a *type* and the `a_i`s are *generic type variables*
/// * if `S` is a substitution of types for type variables, written
///   `[tau_1/alpha_1, ..., tau_n/alpha_n]` or simply `[tau_i/alpha_i]_i` and
///   `sigma` is a type-scheme, then `S sigma` is the type-scheme obtained by
///   replacing each *free occurence* of `alpha_i` in `sigma` by `tau_i`,
///   renaming the generic variables of `sigma` if necessary, THEN `S sigma` is
///   called an __instance__ of `sigma`.
/// * a type scheme `sigma = forall a_1 ... a_n . tau` has a __generic
///   instance__ of `sigma' = forall b_1 ... b_n . tau'` if `tau' =
///   [tau_i/a_i] tau` for some types `tau_1, ..., tau_n` and the `b_j` are not
///   free in `sigma` and we write `sigma > sigma'`
///     - *instantiation* acts on __free__ variables
///     - *generic instantiation* acts on __bound__ variables
/// * `sigma > sigma'` implies `S sigma > S sigma'`
/// * free type variables in an assertion are *implicitly* quantified over the
///   whole assertion, while __explicit quantification__ has restricted scope
///
/// TODO: handle recursion using the polymorphic fixed-point operator `fix ::
/// forall a . (a -> a) -> a
pub struct Scheme {
    pub tipo: Type,
    pub poly: Vec<Tv>,
    pub ctxt: Vec<(Ident, Ctv)>,
}

impl Scheme {
    pub fn monotype(tipo: Type) -> Self {
        Self {
            poly: vec![],
            tipo,
            ctxt: vec![],
        }
    }
    pub fn polytype(tipo: Type) -> Self {
        Self {
            poly: tipo.fv(),
            tipo,
            ctxt: vec![],
        }
    }
    pub fn poly_contexts(&self) -> Vec<(Ident, Tv)> {
        self.iter_ctxts()
            .map(|(class, idx)| (*class, *&self.poly[*idx]))
            .collect()
    }
    pub fn instance(tipo: Type, ctxts: Vec<(Ident, Tv)>) -> Self {
        let poly = tipo.fv();
        let ctxt = ctxts
            .into_iter()
            .filter_map(|(id, tv)| {
                if poly.contains(&tv) {
                    poly.iter().position(|var| var == &tv).map(|u| (id, Ctv(u)))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        Self { poly, tipo, ctxt }
    }
    pub fn normalize(&self) -> Self {
        let varord = self
            .tipo
            .enumerate()
            .map(Var::as_pair)
            .collect::<Map<Tv, Tv>>();
        let tipo = self.tipo.map_t_ref(&mut |t| varord[t]);
        let poly = self.poly.iter().map(|tv| varord[tv]).collect::<Vec<_>>();
        let ctxt = self.ctxt.clone();
        Scheme { poly, tipo, ctxt }
    }
    pub fn generalize(&self, tipo: Type) -> Self {
        let poly = tipo
            .ftv()
            .difference(&self.ftv())
            .copied()
            .collect::<Vec<_>>();
        let ctxt = self
            .iter_ctxts()
            .filter(|(_, ctv)| poly.contains(&self.poly[*ctv]))
            .copied()
            .collect();
        Scheme { poly, tipo, ctxt }
    }
    pub fn iter_tvs(&self) -> std::slice::Iter<'_, Tv> {
        self.poly.iter()
    }
    pub fn iter_ctxts(&self) -> std::slice::Iter<'_, (Ident, Ctv)> {
        self.ctxt.iter()
    }
    pub fn has_class(&self, name: &Ident) -> bool {
        self.iter_ctxts().any(|(c, _)| c == name)
    }
    pub fn has_var(&self, tv: &Tv) -> bool {
        self.poly.contains(tv)
    }
    pub fn class_vars<'a>(&'a self, class: &'a Ident) -> impl Iterator<Item = Ctv> + 'a {
        self.iter_ctxts()
            .filter_map(move |(id, var)| if class == id { Some(*var) } else { None })
    }
    pub fn var_classes<'a>(&'a self, var: &'a Tv) -> impl Iterator<Item = Ident> + 'a {
        self.iter_ctxts().filter_map(move |(id, ctv)| {
            if var == &self.poly[*ctv] {
                Some(*id)
            } else {
                None
            }
        })
    }
}

/// Will convert a `Type` into a `Scheme` *without* any qualifying predicates or
/// quantified variables. Identical to calling `Scheme::monotype`.
impl From<Type> for Scheme {
    fn from(ty: Type) -> Self {
        Scheme {
            poly: vec![],
            tipo: ty,
            ctxt: vec![],
        }
    }
}

impl Substitutable for Scheme {
    fn ftv(&self) -> Set<Tv> {
        self.tipo
            .ftv()
            .difference(&self.poly.iter().copied().collect())
            .copied()
            .collect()
    }

    fn tv(&self) -> Vec<Tv> {
        self.tipo
            .tv()
            .into_iter()
            .filter(|tv| !self.poly.contains(tv))
            .collect()
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        let tipo = self
            .tipo
            .apply_once(&subst.clone().remove_many(self.poly.as_slice()));
        let poly = tipo.fv();
        let ctxt = self
            .ctxt
            .clone()
            .into_iter()
            .filter_map(|(id, i)| {
                poly.iter()
                    .position(|tv| tv == &self.poly[i])
                    .map(|u| (id, Ctv(u)))
            })
            .collect();
        Self { poly, tipo, ctxt }
    }
}

impl std::fmt::Debug for Scheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self)
    }
}

impl std::fmt::Display for Scheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.poly.is_empty() {
            write!(f, "{}", &self.tipo)
        } else {
            write!(f, "forall ")?;
            for tv in &self.poly {
                write!(f, "{} ", tv)?;
            }
            match &self.ctxt[..] {
                [] => {
                    write!(f, ". ")?;
                }
                [(c, i), rest @ ..] => {
                    write!(f, ". |{} {}", c, &self.poly[*i])?;
                    for (ci, ix) in rest {
                        write!(f, ", {} {}", ci, &self.poly[*ix])?;
                    }
                    write!(f, "| ")?;
                }
            };
            write!(f, "{}", &self.tipo)
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Constraint {
    Join(Type, Type),
    Class { class_name: Ident, instance: Type },
}

wy_common::variant_preds! {
    Constraint
    | is_join => Join(..)
    | is_class => Class {..}
    | is_simple_join => Join(x, y) [if x.is_var() || y.is_var()]
    | is_var_join => Join(x, y) [if x.is_var() && y.is_var()]
}

impl Substitutable for Constraint {
    fn ftv(&self) -> wy_common::Set<Tv> {
        match self {
            Constraint::Join(t1, t2) => t1.ftv().union(&t2.ftv()).copied().collect(),
            Constraint::Class {
                class_name: _,
                instance,
            } => instance.ftv(),
        }
    }

    fn tv(&self) -> Vec<Tv> {
        match self {
            Constraint::Join(t1, t2) => t2.tv().into_iter().fold(t1.tv(), push_if_absent),
            Constraint::Class {
                class_name: _,
                instance,
            } => instance.tv(),
        }
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        match self {
            Constraint::Join(t1, t2) => {
                Constraint::Join(t1.apply_once(subst), t2.apply_once(subst))
            }
            Constraint::Class {
                class_name,
                instance,
            } => Constraint::Class {
                class_name: *class_name,
                instance: instance.apply_once(subst),
            },
        }
    }
}

impl std::fmt::Debug for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self)
    }
}

impl std::fmt::Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constraint::Join(t1, t2) => {
                write!(f, "{} {} {}", t1, wy_pretty::color! {fg Red "~"}, t2)
            }
            Constraint::Class {
                class_name,
                instance,
            } => {
                let fvs = instance.fv();
                match &fvs[..] {
                    [] => {
                        write!(f, "|{} {}| {}", class_name, instance, instance)
                    }
                    [a, bs @ ..] => {
                        write!(f, "|{} {}", class_name, a)?;
                        for b in bs {
                            write!(f, ", {} {}", class_name, b)?;
                        }
                        write!(f, "| ")?;
                        write!(f, "{}", instance)
                    }
                }
            }
        }
    }
}

/// An interface for types that contain an extensible and deduplicatable backing
/// store. The implementor is able to accept any domain type `D` from which
/// elements of type `Self::Image` may be extracted and added to `Self`, which
/// may or may not be of type `D`.
pub trait Injection<D> {
    type Image: Clone + PartialEq;
    fn dedupe(&mut self);
    fn inject(&mut self, domain: D);
    fn to_vec(self) -> Vec<Self::Image>;
    fn deduped(mut self) -> Self
    where
        Self: Sized,
    {
        self.dedupe();
        self
    }
    fn inject_mapped<A>(&mut self, domain: A, mut f: impl FnMut(A) -> D) -> &mut Self {
        self.inject(f(domain));
        self
    }
    fn surject(self, onto: &mut impl Injection<D>)
    where
        Self: Sized + IntoIterator<Item = D>,
    {
        for x in self {
            onto.inject(x)
        }
    }
}

impl<X: PartialEq + Clone> Injection<X> for Vec<X> {
    type Image = X;

    fn dedupe(&mut self) {
        *self = self.into_iter().fold(vec![], |mut a, c| {
            let c = c.clone();
            if !a.contains(&c) {
                a.push(c);
            }
            a
        })
    }

    fn inject(&mut self, domain: X) {
        if !self.contains(&domain) {
            self.push(domain)
        }
    }

    fn to_vec(self) -> Vec<Self::Image> {
        self
    }
}

impl<X: PartialEq + Clone> Injection<X> for Deque<X> {
    type Image = X;

    fn dedupe(&mut self) {
        *self = self.into_iter().fold(Deque::new(), |mut a, c| {
            let c = c.clone();
            if !a.contains(&c) {
                a.push_back(c);
            }
            a
        })
    }

    fn inject(&mut self, domain: X) {
        if !self.contains(&domain) {
            self.push_back(domain)
        }
    }

    fn to_vec(self) -> Vec<Self::Image> {
        self.into_iter().collect()
    }
}

impl<X: std::hash::Hash + Eq + Clone> Injection<X> for Set<X> {
    type Image = X;

    fn dedupe(&mut self) {
        // no-op since hash-sets don't contain duplicates
    }

    fn inject(&mut self, domain: X) {
        self.insert(domain);
    }

    fn to_vec(self) -> Vec<Self::Image> {
        self.into_iter().collect()
    }
}

impl Injection<(Type, Type)> for ConstraintBuilder {
    type Image = Constraint;

    fn dedupe(&mut self) {
        self.buf.dedupe()
    }

    fn inject(&mut self, domain: (Type, Type)) {
        if !self.buf.contains(&domain) {
            self.buf.push(domain);
        }
    }

    fn to_vec(self) -> Vec<Self::Image> {
        self.build()
    }
}

pub struct ConstraintBuilder {
    buf: Vec<(Type, Type)>,
    cur: Option<Type>,
}

impl ConstraintBuilder {
    pub fn new() -> Self {
        ConstraintBuilder {
            buf: vec![],
            cur: None,
        }
    }

    pub fn anchor(mut self, ty: Type) -> Self {
        self.cur = Some(ty);
        self
    }

    pub fn spread(mut self, tys: impl IntoIterator<Item = Type>) -> Self {
        if let Some(ref c) = self.cur {
            for ty in tys {
                self.buf.push((c.clone(), ty))
            }
        }
        self
    }

    pub fn doesnt_have(&self, left: &Type, right: &Type) -> bool {
        self.buf.iter().any(|(tx, ty)| tx == left && ty == right)
    }

    pub fn add_join(mut self, left: Type, right: Type) -> Self {
        if self.doesnt_have(&left, &right) {
            self.buf.push((left, right));
        }
        self
    }

    pub fn add_many_joins(mut self, joins: impl IntoIterator<Item = (Type, Type)>) -> Self {
        for (tx, ty) in joins {
            self = self.add_join(tx, ty);
        }
        self
    }

    pub fn add_is_list_of(self, left: Type, list_of: Type) -> Self {
        self.add_join(left, Type::mk_list(list_of))
    }

    pub fn add_is_tuple_of(self, left: Type, tuple_of: impl IntoIterator<Item = Type>) -> Self {
        self.add_join(left, Type::mk_tuple(tuple_of))
    }

    pub fn remove_dupes(mut self) -> Self {
        self.buf = self.buf.into_iter().fold(vec![], |mut a, (cx, cy)| {
            let pair = (cx, cy);
            if a.contains(&pair) {
                a.push(pair);
            }
            a
        });
        self
    }

    pub fn build_iter(self) -> impl Iterator<Item = Constraint> {
        self.buf
            .into_iter()
            .map(|(ta, tb)| Constraint::Join(ta, tb))
    }

    pub fn build(self) -> Vec<Constraint> {
        self.build_iter().collect()
    }
}

#[cfg(test)]
mod test {
    use wy_common::Mappable;

    use super::*;

    #[test]
    fn test_constraint_builder() {
        let [ty0, ty1, ty2, ty3, ty4, ty5] = [
            Type::mk_fun(Type::Var(Tv(0)), Type::Var(Tv(1))),
            Type::mk_fun(Type::BOOL, Type::BOOL),
            Type::Var(Tv(2)),
            Type::mk_list(Type::INT),
            Type::Var(Tv(3)),
            Type::mk_tuple([Type::CHAR, Type::NAT, Type::BYTE]),
        ];
        let cb = ConstraintBuilder::new()
            .anchor(Type::mk_fun(Type::Var(Tv(0)), Type::Var(Tv(1))))
            .spread([Type::mk_fun(Type::BOOL, Type::BOOL)])
            .add_is_list_of(Type::Var(Tv(2)), Type::INT)
            .add_is_tuple_of(Type::Var(Tv(3)), [Type::CHAR, Type::NAT, Type::BYTE])
            .build();
        let expected =
            vec![(ty0, ty1), (ty2, ty3), (ty4, ty5)].fmap(|(x, y)| Constraint::Join(x, y));
        assert_eq!(cb, expected)
    }
}
