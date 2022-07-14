use wy_common::Mappable;
use wy_name::ident::Ident;
use wy_syntax::{expr::Expression, record::Record, stmt::Binding, tipo::Tv, Literal};

use super::{
    constraint::{Constraint, Injection, Scheme, Type},
    envr::Environment,
    error::{Error, Inferred},
    subst::{Subst, Substitutable},
    unify::Unifier,
};

pub type Bind = Binding<Ident, Tv>;
wy_common::newtype! { usize in BindId | Show AsUsize AsRef [Bind] }

type Expr = Expression<Ident, Tv>;

#[allow(unused)]
pub fn solve(env: &mut Environment, mut constraints: Vec<Constraint>) -> Inferred<Subst> {
    let mut subst = Subst::new();
    constraints.reverse();
    let mut unifier = Unifier::new();

    while let Some(c) = constraints.pop() {
        match c {
            Constraint::Join(ta, tb) => {
                let s2 = unifier.unify(ta, tb)?;
                let s3 = subst.compose(&s2);
                constraints = constraints.apply(&s2);
                subst = s3;
            }
            Constraint::Class {
                class_name,
                instance,
            } => {}
        }
    }

    Ok(subst)
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
    env: &mut Environment,
    lit: &Literal,
) -> Result<(Type, Vec<Constraint>), Error> {
    let mut preds = vec![];
    let ty;
    match lit {
        Literal::Byte(_) | Literal::Int(_) | Literal::Nat(_) => {
            ty = env.fresh();
            preds.push(Constraint::Class {
                class_name: Ident::Upper(wy_intern::NUM),
                instance: ty.clone(),
            });
        }
        Literal::Float(_) | Literal::Double(_) => {
            ty = env.fresh();
            preds.push(Constraint::Class {
                class_name: Ident::Upper(wy_intern::FRACTIONAL),
                instance: ty.clone(),
            });
        }
        Literal::Char(_) => ty = Type::CHAR,
        Literal::Str(_) | Literal::EmptyStr => ty = Type::STR,
    };
    Ok((ty, preds))
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
                class_name: Ident::Upper(wy_intern::NUM),
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
        Expression::Section(_) => {
            todo!()
        }
        Expression::Tuple(xs) => infer_tuple_expr(env, xs),
        Expression::Array(xs) => infer_array_expr(env, xs),
        Expression::List(_, _) => todo!(),
        Expression::Dict(Record::Data(con, flds)) => {
            let err = Error::Unbound;
            let sc = if con.is_upper() {
                env.lookup_ctor(con)
            } else {
                env.lookup_local(con)
            }
            .map(|s| {
                (
                    s.tipo.clone(),
                    s.poly_contexts()
                        .fmap(|(class_name, tv)| Constraint::Class {
                            class_name,
                            instance: tv.as_type(),
                        }),
                )
            })
            .ok_or(err(*con));

            flds.into_iter()
                .filter_map(|fld| fld.as_pair())
                .fold(sc, |a, (k, e)| {
                    let (te, ce) = infer_expr(env, e)?;
                    let k_sc = env.lookup_global(k).ok_or_else(|| err(*k))?;
                    a.map(|(ty, mut cs)| {
                        cs.push(Constraint::Join(te, k_sc.tipo.clone()));
                        cs.extend(ce);
                        (ty, cs)
                    })
                })
        }
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
        Expression::Cast(ex, ty) => {
            let ty = ty.clone();
            let (t0, mut c0) = infer_expr(env, ex.as_ref())?;
            let tv = env.fresh();
            c0.push(Constraint::Join(tv.clone(), t0));
            c0.push(Constraint::Join(tv.clone(), ty.clone()));
            Ok((ty, c0))
        }
        Expression::Do(_, _) => todo!(),
        Expression::Range(_, _) => todo!(),
        Expression::Group(x) => infer_expr(env, x.as_ref()),
    }
}

#[inline]
fn infer_tuple_expr(env: &mut Environment, exprs: &[Expr]) -> Inferred<(Type, Vec<Constraint>)> {
    if exprs.is_empty() {
        return Ok((Type::UNIT, vec![]));
    }
    let init = (vec![], vec![]);
    let (ts, cs) = exprs.into_iter().fold(Ok(init), |a, c| {
        let tv = env.fresh();
        let (mut typs, mut cns) = a?;
        let (ty, cs) = infer_expr(env, c)?;
        cns.extend(cs);
        cns.inject(Constraint::Join(tv, ty.clone()));
        typs.push(ty);
        Ok((typs, cns.deduped()))
    })?;
    Ok((Type::Tup(ts), cs))
}

#[inline]
fn infer_array_expr(env: &mut Environment, exprs: &[Expr]) -> Inferred<(Type, Vec<Constraint>)> {
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
    use crate::typed::envr::Builder;

    use super::*;
    use wy_common::pretty::Many;

    #[test]
    fn test_inference_without_prelude() {
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

infixr 9 \>
fn (\>) :: (b -> c) -> (a -> b) -> c
    | f g = \x -> f (g x)

infixr 1 |>
fn (|>) :: (a -> b) -> a -> b
    | f = \x -> f x
"#;
        match wy_parser::parse_program(src) {
            Err(e) => eprintln!("{}", e),
            Ok(program) => {
                let mut envr = Builder::with_program(&program);
                let src2 = "fst (True, False) || True";
                match wy_parser::parse_expression(src2) {
                    Ok(expr) => {
                        let expr = expr.map_t(&mut |id| Tv::from(id));
                        match infer_expr(&mut envr, &expr) {
                            Ok((ty, cs)) => {
                                println!("inferred type: {}", &ty);
                                println!("constraints:\n\t{}", Many(&cs[..], ",\n\t"));
                                match solve(&mut envr, cs) {
                                    Ok(soln) => {
                                        let soln = dbg!(&soln);
                                        let apped = dbg!(ty.apply(soln));
                                        println!("inferred: {}\napplied: {}", &ty, apped)
                                    }
                                    Err(e) => eprintln!("Unification solver error: {}", e),
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
