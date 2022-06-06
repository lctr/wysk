use wy_common::Set;
use wy_syntax::{
    expr::Expression,
    ident::Ident,
    stmt::Binding,
    tipo::{Con, Tv},
    Literal,
};

use super::{
    constraint::{Constraint, Injection, Scheme, Type},
    envr::Environment,
    error::{Error, Inferred},
    subst::{Subst, Substitutable},
    unify::{Unifier, Unify},
};

pub type Bind = Binding<Ident, Tv>;
wy_common::newtype! { usize in BindId | Show AsUsize AsRef [Bind] }

type Expr = Expression<Ident, Tv>;
type Constraints = Vec<Constraint>;

pub struct Inference {
    inferred_ty: Type,
    constraints: Constraints,
}

impl Inference {
    pub fn new(inferred_ty: Type) -> Self {
        Self {
            inferred_ty,
            constraints: vec![],
        }
    }
    pub fn with_constraints(inferred_ty: Type, constraints: Constraints) -> Self {
        Self {
            inferred_ty,
            constraints,
        }
    }

    /// Returns the number of constraints stored, i.e., the length of the inner
    /// vector holding the constraints.
    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    /// Resets this inference instance with a fresh inference instance
    /// containing only the given type (and an empty list of constraints) and
    /// returns the previously held type and constraints
    pub fn reset_with(&mut self, ty: Type) -> Self {
        std::mem::replace(self, Self::new(ty))
    }

    pub fn parts(self) -> (Type, Constraints) {
        (self.inferred_ty, self.constraints)
    }

    pub fn ok(self) -> Inferred<Self> {
        Ok(self)
    }

    /// Replaces the inferred type with the provided value, returning the old
    /// value.
    pub fn set_inferred(&mut self, inferred_ty: Type) -> Type {
        std::mem::replace(&mut self.inferred_ty, inferred_ty)
    }

    pub fn inferred(&self) -> &Type {
        &self.inferred_ty
    }
    pub fn inferred_mut(&mut self) -> &mut Type {
        &mut self.inferred_ty
    }
    pub fn inferred_cloned(&self) -> Type {
        self.inferred_ty.clone()
    }
    pub fn constraints(&self) -> &Constraints {
        &self.constraints
    }
    pub fn constraints_mut(&mut self) -> &mut Constraints {
        &mut self.constraints
    }
    pub fn constraints_iter(&self) -> std::slice::Iter<'_, Constraint> {
        self.constraints.iter()
    }
    pub fn constraints_iter_mut(&mut self) -> std::slice::IterMut<'_, Constraint> {
        self.constraints.iter_mut()
    }
    pub fn constraint_slices(&self) -> &[Constraint] {
        self.constraints.as_slice()
    }
    pub fn has_constraint(&self, constraint: &Constraint) -> bool {
        self.constraints.contains(constraint)
    }
    pub fn find_constraint(
        &self,
        predicate: impl FnMut(&&Constraint) -> bool,
    ) -> Option<&Constraint> {
        self.constraints_iter().find(predicate)
    }

    /// Checks whether a `Join` constraint consisting of both types (in either
    /// order) already exists
    pub fn has_join(&self, (left, right): (&Type, &Type)) -> bool {
        self.constraints_iter().any(|c| {
            matches!(c, Constraint::Join(x, y) if
                    (left, right) == (x, y) || (left, right) == (y, x)
            )
        })
    }

    /// Returns an iterator of constraints for a type consisting of a single
    /// type variable, i.e., `Type::Var` variants, e.g., `a ~ [(Foo, Bar)]` and
    /// `m a -> m b ~ c` are simple joins due to the single type variable on
    /// either side of the equation.
    pub fn simple_joins(&self) -> impl Iterator<Item = &Constraint> + '_ {
        self.constraints_iter().filter(|c| c.is_simple_join())
    }

    /// Checks whether a `Class` constraint consisting of both the class name
    /// and type (as the instance) already exists
    pub fn has_context(&self, (class_name, instance): (&Ident, &Type)) -> bool {
        self.constraints_iter().any(|c| matches!(c, Constraint::Class { class_name: x, instance: y} if x == class_name && y == instance))
    }

    pub fn has_constraint_for(&self, which_ty: &Type) -> bool {
        self.constraints_iter().any(|constraint| match constraint {
            Constraint::Join(a, b) => which_ty == a || which_ty == b,
            Constraint::Class {
                class_name: _,
                instance,
            } => which_ty == instance,
        })
    }

    pub fn add_join(mut self, left: Type, right: Type) -> Self {
        if !self.has_join((&left, &right)) {
            self.constraints.push(Constraint::Join(left, right))
        };
        self
    }

    /// Identical to `add_join`, but doesn't take ownership of `Self`.
    pub fn insert_join(&mut self, left: Type, right: Type) -> &mut Self {
        if !self.has_join((&left, &right)) {
            self.constraints.push(Constraint::Join(left, right))
        }
        self
    }

    /// Generates a `Join` constraint for the given type for the *left* and the
    /// `inferred` type on the *right* and stores it.
    pub fn join_left(self, left: Type) -> Self {
        let right = self.inferred_cloned();
        self.add_join(left, right)
    }

    /// Identical to `join_left`, but doesn't take ownership of `Self`.
    pub fn join_left_mut(&mut self, left: Type) -> &mut Self {
        let right = self.inferred_cloned();
        self.insert_join(left, right)
    }

    /// Identical to `join_right`, but doesn't take ownership of `Self`.
    pub fn join_right_mut(&mut self, right: Type) -> &mut Self {
        let left = self.inferred_cloned();
        self.insert_join(left, right)
    }

    /// Generates a `Join` constraint for the given type for the *right* and the
    /// `inferred` type on the *left* and stores it.
    pub fn join_right(self, right: Type) -> Self {
        let left = self.inferred_cloned();
        self.add_join(left, right)
    }

    pub fn add_joins(mut self, joins: impl IntoIterator<Item = (Type, Type)>) -> Self {
        for (left, right) in joins {
            self = self.add_join(left, right);
        }
        self
    }

    /// Identical to `add_joins`, but doesn't take ownership of `Self`.
    pub fn insert_joins(&mut self, joins: impl IntoIterator<Item = (Type, Type)>) -> &mut Self {
        for (left, right) in joins {
            self.insert_join(left, right);
        }
        self
    }

    /// Given a list of types on the left and a single type on the right, this
    /// method generates constraints joining every type on the left with the
    /// type on the right, e.g., `add_left_joins([t0, t2, t3], t4)` stores the
    /// constraints `[t0 ~ t4, t1 ~ t4, t2 ~ t4, t3 ~ t4]`.
    pub fn add_left_joins(mut self, lefts: impl IntoIterator<Item = Type>, right: Type) -> Self {
        for left in lefts {
            self = self.add_join(left, right.clone());
        }
        self
    }

    /// Identical to `add_left_joins`, but doesn't take ownership of `Self`.
    pub fn insert_left_joins(
        &mut self,
        lefts: impl IntoIterator<Item = Type>,
        right: Type,
    ) -> &mut Self {
        for left in lefts {
            self.insert_join(left, right.clone());
        }
        self
    }

    /// Given a single type on the left and a list of types on the right, this
    /// method generates constraints joining the type on the left with every
    /// type on the right, e.g., `add_right_joins(t4, [t0, t2, t3])` stores the
    /// constraints `[t4 ~ t0, t4 ~ t1, t4 ~ t2, t4 ~ t3]`.
    pub fn add_right_joins(mut self, left: Type, rights: impl IntoIterator<Item = Type>) -> Self {
        for right in rights {
            self = self.add_join(left.clone(), right);
        }
        self
    }

    /// Identical to `add_right_joins`, but doesn't take ownership of `Self`.
    pub fn insert_right_joins(
        &mut self,
        left: Type,
        rights: impl IntoIterator<Item = Type>,
    ) -> &mut Self {
        for right in rights {
            self.insert_join(left.clone(), right);
        }
        self
    }

    /// Given a list of types `[t0, t1, t2, t3, ...]`, this method will
    /// transitively generate (and add) the (join) constraints
    ///
    ///     t0 ~ t1, t1 ~ t2, t2 ~ t3, ...
    ///
    pub fn add_transitive_joins(mut self, tys: impl IntoIterator<Item = Type>) -> Self {
        let mut iter = tys.into_iter();
        let mut first = iter.next();
        while let Some(a) = first.take() {
            if let Some(b) = iter.next() {
                self = self.add_join(a, b.clone());
                first = Some(b);
            }
        }
        self
    }

    /// Identical to `add_transitive_joins`, but doesn't take ownership of
    /// `Self`.
    pub fn insert_transitive_joins(&mut self, tys: impl IntoIterator<Item = Type>) -> &mut Self {
        let mut iter = tys.into_iter();
        let mut first = iter.next();
        while let Some(a) = first.take() {
            if let Some(b) = iter.next() {
                self.insert_join(a, b.clone());
                first = Some(b);
            }
        }
        self
    }

    pub fn add_context(mut self, class_name: Ident, instance: Type) -> Self {
        if !self.has_context((&class_name, &instance)) {
            self.constraints.push(Constraint::Class {
                class_name,
                instance,
            })
        }
        self
    }
    pub fn insert_context(&mut self, class_name: Ident, instance: Type) -> &mut Self {
        if !self.has_context((&class_name, &instance)) {
            self.constraints.push(Constraint::Class {
                class_name,
                instance,
            })
        }
        self
    }
    pub fn add_contexts(mut self, contexts: impl IntoIterator<Item = (Ident, Type)>) -> Self {
        for (class_name, instance) in contexts {
            self = self.add_context(class_name, instance);
        }
        self
    }
    pub fn insert_contexts(
        &mut self,
        contexts: impl IntoIterator<Item = (Ident, Type)>,
    ) -> &mut Self {
        for (class_name, instance) in contexts {
            self.insert_context(class_name, instance);
        }
        self
    }

    pub fn add_for_class(
        mut self,
        class_name: Ident,
        instances: impl IntoIterator<Item = Type>,
    ) -> Self {
        for instance in instances {
            if !self.has_context((&class_name, &instance)) {
                self = self.add_context(class_name, instance);
            }
        }
        self
    }

    pub fn insert_for_class(
        &mut self,
        class_name: Ident,
        instances: impl IntoIterator<Item = Type>,
    ) -> &mut Self {
        for instance in instances {
            if !self.has_context((&class_name, &instance)) {
                self.insert_context(class_name, instance);
            }
        }
        self
    }

    pub fn add_constraint(mut self, constraint: Constraint) -> Self {
        if !self.has_constraint(&constraint) {
            self.constraints.push(constraint);
        }
        self
    }

    pub fn insert_constraint(&mut self, constraint: Constraint) -> &mut Self {
        if !self.has_constraint(&constraint) {
            self.constraints.push(constraint);
        }
        self
    }

    pub fn add_constraints(mut self, constraints: impl IntoIterator<Item = Constraint>) -> Self {
        for constraint in constraints {
            self = self.add_constraint(constraint);
        }
        self
    }

    pub fn insert_constraints(
        &mut self,
        constraints: impl IntoIterator<Item = Constraint>,
    ) -> &mut Self {
        for constraint in constraints {
            self.insert_constraint(constraint);
        }
        self
    }
    pub fn dedupe(&mut self) {
        self.constraints.dedupe();
    }

    pub fn deduped(&mut self) -> &mut Self {
        self.constraints.dedupe();
        self
    }

    pub fn finalize_deduped<X>(self, mut f: impl FnMut(Type, Constraints) -> X) -> X {
        f(self.inferred_ty, self.constraints.deduped())
    }

    pub fn reverse_constraints(&mut self) -> &mut Self {
        self.constraints.reverse();
        self
    }

    pub fn pop_constraint(&mut self) -> Option<Constraint> {
        self.constraints.pop()
    }

    /// Splits the inner constraints vector at the given position, returning a
    /// new vector containing all the constraints *on* or *after* the provided
    /// index, updating the inner constraints to contain only the remainder.
    ///
    /// For example, if this instance contains the constraints `[c0, c1, c2,
    /// c3]`, then the method call `split_off(2)` would return `[c2, c3]` and
    /// the internal constraint vector would be updated to `[c0, c1]`.
    ///
    pub fn split_off(&mut self, at: usize) -> Constraints {
        self.constraints.split_off(at % self.len())
    }
}

impl Extend<Constraint> for Inference {
    fn extend<T: IntoIterator<Item = Constraint>>(&mut self, iter: T) {
        for constraint in iter {
            if !self.has_constraint(&constraint) {
                self.constraints.push(constraint)
            }
        }
    }
}

impl Extend<(Type, Type)> for Inference {
    fn extend<T: IntoIterator<Item = (Type, Type)>>(&mut self, iter: T) {
        for (left, right) in iter {
            if !self.has_join((&left, &right)) {
                self.constraints.push(Constraint::Join(left, right))
            }
        }
    }
}

impl Extend<(Ident, Vec<Type>)> for Inference {
    fn extend<T: IntoIterator<Item = (Ident, Vec<Type>)>>(&mut self, iter: T) {
        for (class_name, instances) in iter {
            for instance in instances {
                if !self.has_context((&class_name, &instance)) {
                    self.constraints.push(Constraint::Class {
                        class_name,
                        instance,
                    })
                }
            }
        }
    }
}

impl Extend<(Ident, Type)> for Inference {
    fn extend<T: IntoIterator<Item = (Ident, Type)>>(&mut self, iter: T) {
        for (class_name, instance) in iter {
            if !self.has_context((&class_name, &instance)) {
                self.constraints.push(Constraint::Class {
                    class_name,
                    instance,
                })
            }
        }
    }
}

impl Substitutable for Inference {
    fn ftv(&self) -> Set<Tv> {
        self.inferred_ty
            .ftv()
            .into_iter()
            .chain(self.constraints.ftv())
            .collect()
    }

    fn apply_once(&self, subst: &Subst) -> Self
    where
        Self: Sized,
    {
        Self {
            inferred_ty: self.inferred_ty.apply_once(subst),
            constraints: self.constraints.apply_once(subst),
        }
    }
}

pub struct Engine {
    environment: Environment,
    _expressions: Vec<Expr>,
    errors: Vec<Error>,
}

impl Engine {
    pub fn new() -> Self {
        Self {
            environment: Environment::new(),
            _expressions: Vec::new(),
            errors: Vec::new(),
        }
    }

    pub fn tick(&mut self) -> Tv {
        self.environment.tick()
    }
    fn fresh(&mut self) -> Type {
        self.environment.fresh()
    }

    pub fn env(&self) -> &Environment {
        &self.environment
    }
    pub fn env_mut(&mut self) -> &mut Environment {
        &mut self.environment
    }

    pub fn unifier(&mut self) -> &mut Unifier {
        self.environment.unifier_mut()
    }

    pub fn infer(&mut self, _expr: &Expr) -> Inferred<Inference> {
        todo!()
    }

    pub fn infer_defined(&mut self, defined: &[(Ident, Expr)]) -> Inferred<()> {
        for (name, expr) in defined {
            match self.infer_expr_scheme(expr) {
                Ok(scheme) => {
                    self.environment.insert_local(*name, scheme);
                }
                Err(e) => self.errors.push(e),
            }
        }
        Ok(())
    }

    pub fn infer_expr_scheme(&mut self, expr: &Expr) -> Inferred<Scheme> {
        self.infer(expr).and_then(|inferred| {
            let (ty, uni) = Unifier::from_inference(inferred);
            *self.unifier() = uni;
            self.env_mut().solve().map(|ref subst| {
                // TODO: how should canonicalization be implemented??
                self.env().canonicalize_with_locals(ty.apply(subst))
            })
        })
    }

    pub fn infer_literal(&mut self, lit: Literal) -> Inferred<Inference> {
        let con = match lit {
            Literal::Byte(_) => Con::BYTE,
            Literal::Int(_) => Con::INT,
            Literal::Nat(_) => Con::NAT,
            Literal::Float(_) => Con::FLOAT,
            Literal::Double(_) => Con::DOUBLE,
            Literal::Char(_) => Con::CHAR,
            Literal::Str(_) | Literal::EmptyStr => Con::STR,
        };
        Inference::new(Type::mk_nullary(con)).ok()
    }

    pub fn infer_tuple_expr(&mut self, exprs: &Vec<Expr>) -> Inferred<Inference> {
        if exprs.is_empty() {
            return Inference::new(Type::UNIT).ok();
        }
        exprs
            .into_iter()
            .map(|x| {
                let tv = self.fresh();
                self.infer(x)?.join_right(tv).ok()
            })
            .fold(Ok((vec![], vec![])), |acc, curr| {
                let (mut tys, mut cts) = acc?;
                curr?.finalize_deduped(|ti, cs| {
                    tys.push(ti);
                    cts.extend(cs);
                });
                Ok((tys, cts))
            })
            .map(|(ts, cs)| Inference::with_constraints(Type::Tup(ts), cs))
    }

    pub fn infer_array_expr(&mut self, exprs: &Vec<Expr>) -> Inferred<Inference> {
        match &exprs[..] {
            [] => Inference::new(Type::mk_list(self.fresh())).ok(),
            [a] => self.infer(a).map(|inf| {
                inf.finalize_deduped(|t1, c1| Inference::with_constraints(Type::mk_list(t1), c1))
            }),
            [a, rest @ ..] => {
                let var = self.tick();
                let mut inf = self.infer(a)?;
                for ex in rest {
                    let (tn, cn) = self.infer(ex)?.parts();
                    inf.extend(cn);
                    let t1 = inf.inferred_cloned();
                    inf = inf.add_left_joins([var.as_type(), t1], tn);
                }
                inf.ok()
            }
        }
    }

    pub fn infer_app_expr(&mut self, left: &Expr, right: &Expr) -> Inferred<Inference> {
        let (t1, mut c1) = infer_expr(self.env_mut(), left)?;
        let (t2, c2) = infer_expr(self.env_mut(), right)?;
        let tv = self.fresh();
        c1.extend(c2);
        c1.push(Constraint::Join(t1, Type::mk_fun(t2, tv.clone())));
        Inference::with_constraints(tv, c1.deduped()).ok()
    }
}

pub fn infer_expr_scheme(_env: &mut Environment, _expr: &Expr) -> Result<Scheme, Error> {
    todo!()
}

pub fn infer_bound_exprs(env: &mut Environment, bound_exprs: &[(Ident, Expr)]) -> Inferred<()> {
    for (name, expr) in bound_exprs {
        let scheme = infer_expr_scheme(env, expr)?;
        // how do we feel about replacing local bindings willy nilly?
        env.insert_local(*name, scheme);
    }
    Ok(())
}

pub fn infer_literal(
    _env: &mut Environment,
    lit: &Literal,
) -> Result<(Type, Vec<Constraint>), Error> {
    let con = match lit {
        Literal::Byte(_) => Con::BYTE,
        Literal::Int(_) => Con::INT,
        Literal::Nat(_) => Con::NAT,
        Literal::Float(_) => Con::FLOAT,
        Literal::Double(_) => Con::DOUBLE,
        Literal::Char(_) => Con::CHAR,
        Literal::Str(_) | Literal::EmptyStr => Con::STR,
    };
    Ok((Type::mk_nullary(con), vec![]))
}

pub fn infer_expr(
    env: &mut Environment,
    expr: &Expression<Ident, Tv>,
) -> Result<(Type, Vec<Constraint>), Error> {
    match expr {
        Expression::Ident(id) => env.get_local(id).map(|ty| (ty, vec![])),
        Expression::Path(_, _) => todo!(),
        Expression::Lit(lit) => infer_literal(env, lit),
        Expression::Neg(x) => {
            let (t1, mut c1) = infer_expr(env, x.as_ref())?;
            let tv = env.tick();
            let u1 = Type::mk_fun(t1.clone(), Type::Var(tv));
            c1.push(Constraint::Join(t1.clone(), Type::Var(tv)));
            c1.push(Constraint::Class {
                class_name: Ident::Upper(*wy_intern::NUM),
                instance: u1,
            });
            Ok((Type::Var(tv), c1))
        }
        Expression::Infix { infix, left, right } => {
            let (t1, c1) = infer_expr(env, left.as_ref())?;
            let (t2, c2) = infer_expr(env, right.as_ref())?;
            let tv = env.tick();
            let var = || Type::Var(tv);

            let u1 = Type::mk_fun(t1, Type::mk_fun(t2, var()));
            let u2 = env.get_local(infix)?;
            let mut cs = c1;
            cs.extend(c2);
            cs.push(Constraint::Join(u1, u2));
            cs.dedupe();
            Ok((var(), cs))
        }
        Expression::Section(_) => todo!(),
        Expression::Tuple(xs) => infer_tuple_expr(env, xs),
        Expression::Array(xs) => infer_array_expr(env, xs),
        Expression::List(_, _) => todo!(),
        Expression::Dict(_) => todo!(),
        Expression::Lambda(_, _) => todo!(),
        Expression::Let(_, _) => todo!(),
        Expression::App(x, y) => {
            let (t1, mut c1) = infer_expr(env, x.as_ref())?;
            let (t2, c2) = infer_expr(env, y.as_ref())?;
            let tv = env.fresh();
            c1.extend(c2);
            c1.push(Constraint::Join(t1, Type::mk_fun(t2, tv.clone())));
            Ok((tv, c1.deduped()))
        }
        Expression::Cond(xyz) => {
            let [x, y, z] = xyz.as_ref();
            let (t1, mut c1) = infer_expr(env, x)?;
            let (t2, c2) = infer_expr(env, y)?;
            let (t3, c3) = infer_expr(env, z)?;
            c1.extend(c2);
            c1.extend(c3);
            c1.extend([
                Constraint::Join(t1, Type::BOOL),
                Constraint::Join(t2.clone(), t3),
            ]);
            Ok((t2, c1.deduped()))
        }
        Expression::Case(_, _) => todo!(),
        Expression::Cast(_, _) => todo!(),
        Expression::Do(_, _) => todo!(),
        Expression::Range(_, _) => todo!(),
        Expression::Group(_) => todo!(),
    }
}

#[inline]
fn infer_tuple_expr(env: &mut Environment, exprs: &Vec<Expr>) -> Inferred<(Type, Vec<Constraint>)> {
    if exprs.is_empty() {
        return Ok((Type::UNIT, vec![]));
    }
    let init = (vec![], vec![]);
    let (ts, cs) = exprs
        .into_iter()
        .map(|x| {
            let tv = env.fresh();
            let (ty, mut cs) = infer_expr(env, x)?;
            cs.inject(Constraint::Join(ty.clone(), tv));
            Ok((ty, cs))
        })
        .fold(Ok(init), |a, c| {
            let (tyi, cis) = c?;
            let (mut tys, mut cts) = a?;
            tys.push(tyi);
            cts.extend(cis);
            Ok((tys, cts.deduped()))
        })?;
    Ok((Type::Tup(ts), cs))
}

#[inline]
fn infer_array_expr(env: &mut Environment, exprs: &Vec<Expr>) -> Inferred<(Type, Vec<Constraint>)> {
    match &exprs[..] {
        [] => {
            let tv = env.fresh();
            Ok((Type::mk_list(tv), vec![]))
        }
        [a] => {
            let (t1, c1) = infer_expr(env, a)?;
            let t2 = Type::mk_list(t1);
            Ok((t2, c1))
        }
        [a, rest @ ..] => {
            let var = env.tick();
            let (t1, mut c1) = infer_expr(env, a)?;
            let mut add = |t: Type, cs: Vec<Constraint>| {
                c1.extend(cs);
                c1.extend([
                    Constraint::Join(var.as_type(), t.clone()),
                    Constraint::Join(t1.clone(), t.clone()),
                ]);
                c1.dedupe();
            };
            for ex in rest {
                let (tn, cn) = infer_expr(env, ex)?;
                add(tn, cn);
            }
            Ok((t1.to_list(), c1))
        }
    }
}

#[cfg(test)]
mod test {
    use crate::infer::envr::Builder;

    use super::*;
    use wy_common::pretty::Many;
    #[test]
    fn test_transitive_join() {
        let tys = (0..5).map(|n| Type::Var(Tv(n))).collect::<Vec<_>>();
        println!("transitively joining {}", Many(&tys[..], ", "));
        let inference = Inference::new(Type::mk_fun(Tv(0).as_type(), Tv(2).as_type()));
        let (_ty, cs) = inference.add_transitive_joins(tys).parts();
        println!("{:?}", &cs);
        assert_eq!(
            cs,
            vec![
                Constraint::Join(Tv(0).as_type(), Tv(1).as_type()),
                Constraint::Join(Tv(1).as_type(), Tv(2).as_type()),
                Constraint::Join(Tv(2).as_type(), Tv(3).as_type()),
                Constraint::Join(Tv(3).as_type(), Tv(4).as_type()),
            ]
        )
    }

    #[test]
    fn test_inference() {
        let src = r#"
data Bool = False | True

infix 2 ||
fn (||) :: Bool -> Bool -> Bool
    | False x = x
    | True _ = True

infix 3 &&
fn (&&) :: Bool -> Bool -> Bool
    | False _ = False
    | True x = x

fn not :: Bool -> Bool
    | True = False 
    | False = True

class Eq a {
    (==) :: a -> a -> Bool;
}

fn curry :: ((a, b) -> c) -> a -> b -> c
    | f x y = f (x, y)

fn uncurry :: (a -> b -> c) -> (a, b) -> c
    | f (x, y) = f x y

fn fst :: (a, b) -> a | (x, _) = x

fn snd :: (a, b) -> b | (_, x) = x

fn flip :: (a -> b -> c) -> b -> a -> c
    | f x y = f y x

fn swap :: (a, b) -> (b, a)
    | (x, y) = (y, x)

infixr 9 \\>
fn (\>) :: (b -> c) -> (a -> b) -> c
    | f g = \x -> f (g x)

infixr 1 |>
fn (|>) :: (a -> b) -> a -> b
    | f = \x -> f x
"#;
        match wy_parser::parse_input(src) {
            Err(e) => eprintln!("{}", e),
            Ok(program) => {
                let mut engine = Engine {
                    environment: Builder::with_program(&program),
                    _expressions: vec![],
                    errors: vec![],
                };
                let src2 = "fst (True, False)) || True";
                match wy_parser::parse_expression(src2) {
                    Ok(expr) => {
                        let expr = expr.map_t(&mut |id| Tv::from(id));
                        match infer_expr(engine.env_mut(), &expr) {
                            Ok((ty, cs)) => {
                                println!("inferred type: {}", &ty);
                                println!("constraints:\n\t{}", Many(&cs[..], ",\n\t"));
                                match engine.env_mut().prepare_constraints(cs).solve() {
                                    Ok(subst) => {
                                        println!("solved substitution:\n\t{}", &subst);
                                        let tap = ty.apply(&subst);
                                        println!("applied to inferred type:\n\t{}", &tap);
                                        let canon = engine.env_mut().canonicalize_with_locals(ty);
                                        println!("canonicalized (locally):\n\t{}", &canon);
                                    }
                                    Err(e) => eprintln!("{}", e),
                                }
                            }
                            Err(e) => eprintln!("Inference failure! {}", e),
                        }
                    }
                    Err(e) => eprintln!("{}", e),
                }
            }
        }
    }
}
