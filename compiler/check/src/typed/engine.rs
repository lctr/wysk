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
};

pub type Bind = Binding<Ident, Tv>;
wy_common::newtype! { usize in BindId | Show AsUsize AsRef [Bind] }

type Expr = Expression<Ident, Tv>;

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
    use crate::typed::envr::Builder;

    use super::*;
    use wy_common::pretty::Many;

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

infixr 9 \>
fn (\>) :: (b -> c) -> (a -> b) -> c
    | f g = \x -> f (g x)

infixr 1 |>
fn (|>) :: (a -> b) -> a -> b
    | f = \x -> f x
"#;
        match wy_parser::parse_input(src) {
            Err(e) => eprintln!("{}", e),
            Ok(program) => {
                let mut envr = Builder::with_program(&program);
                let src2 = "fst (True, False)) || True";
                match wy_parser::parse_expression(src2) {
                    Ok(expr) => {
                        let expr = expr.map_t(&mut |id| Tv::from(id));
                        match infer_expr(&mut envr, &expr) {
                            Ok((ty, cs)) => {
                                println!("inferred type: {}", &ty);
                                println!("constraints:\n\t{}", Many(&cs[..], ",\n\t"));
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