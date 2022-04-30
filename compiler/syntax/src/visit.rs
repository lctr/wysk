use super::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum VisitError {
    Binding,
}

impl std::fmt::Display for VisitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VisitError::Binding => write!(f, "Error visiting binding"),
        }
    }
}

impl std::error::Error for VisitError {}

pub struct Visitor<T>(pub T);
impl<Id> Visit<Id, VisitError> for Visitor<()> {}
impl<Id> VisitMut<Id, VisitError> for Visitor<()> {}

/// Applying the visitor pattern to relevant AST Nodes. The methods involved
/// have all been predefined, but any overwritten definitions *must* ensure
/// that they still recurse throughout the tree.
pub trait Visit<Id, Err = VisitError>: Sized
where
    Err: std::error::Error + From<VisitError>,
{
    fn visit_expr(&mut self, expr: &Expression<Id>) -> Result<(), Err> {
        match expr {
            Expression::Ident(_) | Expression::Lit(_) => {}
            Expression::Neg(e) => self.visit_expr(e.as_ref())?,
            Expression::Infix {
                infix: _,
                left,
                right,
            } => {
                self.visit_expr(left.as_ref())?;
                self.visit_expr(right.as_ref())?;
            }
            Expression::Tuple(xs) | Expression::Array(xs) => {
                for x in xs {
                    self.visit_expr(x)?;
                }
            }
            Expression::List(e, stmts) => {
                // order?
                self.visit_expr(e.as_ref())?;
                for stmt in stmts {
                    self.visit_stmt(stmt)?;
                }
            }
            Expression::Dict(record) => match record {
                Record::Anon(fields) | Record::Data(_, fields) => {
                    for field in fields {
                        match field {
                            Field::Rest | Field::Key(_) => {}
                            Field::Entry(_, v) => self.visit_expr(v)?,
                        }
                    }
                }
            },
            Expression::Lambda(_, ex) => self.visit_expr(ex.as_ref())?,
            Expression::Let(bindings, ex) => {
                for binding in bindings {
                    self.visit_binding(binding)?;
                }
                self.visit_expr(ex.as_ref())?;
            }
            Expression::App(fun, arg) => {
                self.visit_expr(fun.as_ref())?;
                self.visit_expr(arg.as_ref())?;
            }
            Expression::Cond(abc) => {
                let [pred, pass, fail] = abc.as_ref();
                self.visit_expr(pred)?;
                self.visit_expr(pass)?;
                self.visit_expr(fail)?;
            }
            Expression::Case(e, alts) => {
                self.visit_expr(e.as_ref())?;
                for alt in alts {
                    self.visit_alt(alt)?;
                }
            }
            Expression::Cast(x, _) => self.visit_expr(x.as_ref())?,
            Expression::Do(stmts, e) => {
                for stmt in stmts {
                    self.visit_stmt(stmt)?;
                }
                self.visit_expr(e.as_ref())?;
            }
            Expression::Range(a, b) => {
                self.visit_expr(a.as_ref())?;
                if let Some(b) = b {
                    self.visit_expr(b.as_ref())?;
                }
            }
            Expression::Group(x) => self.visit_expr(x.as_ref())?,
        };
        Ok(())
    }
    fn visit_alt(&mut self, alt: &Alternative<Id>) -> Result<(), Err> {
        let Alternative {
            pat,
            pred,
            body,
            wher,
        } = alt;
        self.visit_pat(pat)?;
        if let Some(ex) = pred {
            self.visit_expr(ex)?;
        }
        self.visit_expr(body)?;
        for binding in wher {
            self.visit_binding(binding)?;
        }
        Ok(())
    }
    fn visit_pat(&mut self, pat: &Pattern<Id>) -> Result<(), Err> {
        if let Pattern::<Id>::Con(_, pats)
        | Pattern::<Id>::Lst(pats)
        | Pattern::<Id>::Tup(pats) = pat
        {
            for pat in pats {
                self.visit_pat(pat)?;
            }
        }
        Ok(())
    }
    fn visit_binding(&mut self, binding: &Binding<Id>) -> Result<(), Err> {
        let Binding { arms, .. } = binding;
        if arms.len() == 1 {
            self.visit_expr(&arms[0].body)?;
            Ok(())
        } else {
            Err(VisitError::Binding.into())
        }
        // for arm in arms {
        //     self.visit_expr(&arm.body)?;
        //     break;
        // }
        // Ok(())
    }
    fn visit_stmt(&mut self, stmt: &Statement<Id>) -> Result<(), Err> {
        match stmt {
            Statement::Generator(pat, ex) => {
                self.visit_pat(pat)?;
                self.visit_expr(ex)?;
            }
            Statement::Predicate(ex) => self.visit_expr(ex)?,
            Statement::DoLet(bnds) => {
                for binding in bnds {
                    self.visit_binding(binding)?;
                }
            }
        };
        Ok(())
    }
    fn visit_module(&mut self, module: &Module<Id>) -> Result<(), Err> {
        for inst in &module.implems {
            for binding in &inst.defs {
                self.visit_binding(binding)?;
            }
        }
        for fundefs in &module.fundefs {
            for arm in &fundefs.defs {
                self.visit_binding(&arm)?
            }
        }
        Ok(())
    }
}

pub trait VisitMut<Id, Err>: Sized
where
    Err: std::error::Error + From<VisitError>,
{
    fn visit_expr_mut(&mut self, expr: &mut Expression<Id>) -> Result<(), Err> {
        match expr {
            Expression::Ident(_) | Expression::Lit(_) => {}
            Expression::Neg(ex) => {
                self.visit_expr_mut(ex)?;
            }
            Expression::Infix {
                infix: _,
                left,
                right,
            } => {
                self.visit_expr_mut(left.as_mut())?;
                self.visit_expr_mut(right.as_mut())?;
            }
            Expression::Tuple(exp) | Expression::Array(exp) => {
                for x in exp {
                    self.visit_expr_mut(x)?;
                }
            }
            Expression::List(exp, stmts) => {
                self.visit_expr_mut(exp)?;
                for stmt in stmts {
                    self.visit_stmt_mut(stmt)?;
                }
            }
            Expression::Dict(record) => match record {
                Record::Anon(fields) | Record::Data(_, fields) => {
                    for field in fields {
                        match field {
                            Field::Rest | Field::Key(_) => {}
                            Field::Entry(_, exp) => {
                                self.visit_expr_mut(exp)?;
                            }
                        }
                    }
                }
            },
            Expression::Lambda(_, exp) => {
                self.visit_expr_mut(exp)?;
            }
            Expression::Let(_bindings, exp) => {
                self.visit_expr_mut(exp)?;
            }
            Expression::App(_, _) => todo!(),
            Expression::Cond(abc) => {
                for exp in abc.as_mut() {
                    self.visit_expr_mut(exp)?;
                }
            }
            Expression::Case(exp, alts) => {
                self.visit_expr_mut(exp)?;
                for alt in alts {
                    self.visit_alt_mut(alt)?;
                }
            }
            Expression::Group(exp) | Expression::Cast(exp, _) => {
                self.visit_expr_mut(exp.as_mut())?;
            }
            Expression::Do(stmts, exp) => {
                for stmt in stmts {
                    self.visit_stmt_mut(stmt)?;
                }
                self.visit_expr_mut(exp)?;
            }
            Expression::Range(exp1, exp2) => {
                self.visit_expr_mut(exp1)?;
                if let Some(exp) = exp2 {
                    self.visit_expr_mut(exp.as_mut())?;
                }
            }
        }
        Ok(())
    }
    fn visit_alt_mut(&mut self, alt: &mut Alternative<Id>) -> Result<(), Err> {
        let Alternative {
            pat, pred, body, ..
        } = alt;
        self.visit_pat_mut(pat)?;
        if let Some(expr) = pred {
            self.visit_expr_mut(expr)?;
        }
        self.visit_expr_mut(body)?;
        Ok(())
    }
    fn visit_pat_mut(&mut self, pat: &mut Pattern<Id>) -> Result<(), Err> {
        if let Pattern::<Id>::Con(_, pats)
        | Pattern::<Id>::Lst(pats)
        | Pattern::<Id>::Tup(pats) = pat
        {
            for pat in pats {
                self.visit_pat_mut(pat)?;
            }
        }
        Ok(())
    }
    fn visit_binding_mut(
        &mut self,
        binding: &mut Binding<Id>,
    ) -> Result<(), Err> {
        let Binding { arms, .. } = binding;
        for arm in arms {
            if let Some(pred) = &mut arm.pred {
                self.visit_expr_mut(pred)?;
            };
            self.visit_expr_mut(&mut arm.body)?;
        }
        Ok(())
    }
    fn visit_stmt_mut(&mut self, stmt: &mut Statement<Id>) -> Result<(), Err> {
        match stmt {
            Statement::Generator(pat, expr) => {
                self.visit_pat_mut(pat)?;
                self.visit_expr_mut(expr)?;
            }
            Statement::Predicate(expr) => {
                self.visit_expr_mut(expr)?;
            }
            Statement::DoLet(bindings) => {
                for binding in bindings {
                    self.visit_binding_mut(binding)?;
                }
            }
        };
        Ok(())
    }
    fn visit_module_mut(&mut self, module: &mut Module<Id>) -> Result<(), Err> {
        for binding in module
            .implems
            .iter_mut()
            .flat_map(|decl| decl.defs.iter_mut())
        {
            self.visit_binding_mut(binding)?;
        }
        for binding in module
            .fundefs
            .iter_mut()
            .flat_map(|decl| decl.defs.iter_mut())
        {
            self.visit_binding_mut(binding)?;
        }

        Ok(())
    }
}

pub fn var_pat_vars<Id, F>(pat: &Pattern<Id>, mut f: F)
where
    F: FnMut(&Id),
{
    match pat {
        Pattern::Var(id) => f(id),
        Pattern::Con(_, pats) => {
            pats.iter().for_each(|pat| var_pat_vars(pat, |id| f(id)))
        }
        _ => {}
    }
}
