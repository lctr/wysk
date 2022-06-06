use wy_graph::EdgeVisitor;

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

/// Applying the visitor pattern to relevant AST Nodes. The methods involved
/// have all been predefined, but any overwritten definitions *must* ensure
/// that they still recurse throughout the tree.
pub trait Visit<Id, T, Err = VisitError>: Sized
where
    Err: std::error::Error + From<VisitError>,
{
    fn visit_ident(&mut self, _id: &Id) -> Result<(), Err> {
        Ok(())
    }
    fn visit_expr(&mut self, expr: &Expression<Id, T>) -> Result<(), Err> {
        match expr {
            Expression::Ident(id) => {
                self.visit_ident(id)?;
            }
            Expression::Lit(_) | Expression::Path(..) => {}
            Expression::Neg(e) => self.visit_expr(e.as_ref())?,
            Expression::Infix {
                infix: _,
                left,
                right,
            } => {
                self.visit_expr(left.as_ref())?;
                self.visit_expr(right.as_ref())?;
            }
            Expression::Section(sec) => {
                self.visit_expr(sec.expr())?;
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
    fn visit_alt(&mut self, alt: &Alternative<Id, T>) -> Result<(), Err> {
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
    fn visit_pat(&mut self, pat: &Pattern<Id, T>) -> Result<(), Err> {
        if let Pattern::Dat(_, pats) | Pattern::Vec(pats) | Pattern::Tup(pats) = pat {
            for pat in pats {
                self.visit_pat(pat)?;
            }
        }
        Ok(())
    }
    fn visit_binding(&mut self, binding: &Binding<Id, T>) -> Result<(), Err> {
        let Binding { arms, .. } = binding;
        if arms.len() == 1 {
            self.visit_expr(&arms[0].body)?;
            Ok(())
        } else {
            Err(VisitError::Binding.into())
        }
    }
    fn visit_stmt(&mut self, stmt: &Statement<Id, T>) -> Result<(), Err> {
        match stmt {
            Statement::Generator(pat, ex) => {
                self.visit_pat(pat)?;
                self.visit_expr(ex)?;
            }
            Statement::Predicate(ex) => self.visit_expr(ex)?,
            Statement::JustLet(bnds) => {
                for binding in bnds {
                    self.visit_binding(binding)?;
                }
            }
        };
        Ok(())
    }
    fn visit_module<U>(&mut self, module: &Module<Id, U, T>) -> Result<(), Err> {
        for inst in &module.implems {
            for binding in &inst.defs {
                self.visit_binding(binding)?;
            }
        }
        for fundefs in &module.fundefs {
            for arm in &fundefs.defs {
                if let Some(pred) = &arm.pred {
                    self.visit_expr(pred)?;
                }
                self.visit_expr(&arm.body)?;
            }
        }
        Ok(())
    }
}

pub trait VisitMut<Id, T, Err>: Sized
where
    Err: std::error::Error + From<VisitError>,
{
    fn visit_expr_mut(&mut self, expr: &mut Expression<Id, T>) -> Result<(), Err> {
        match expr {
            Expression::Ident(_) | Expression::Lit(_) | Expression::Path(..) => {}
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
            Expression::Section(sec) => {
                self.visit_expr_mut(sec.expr_mut())?;
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
    fn visit_alt_mut(&mut self, alt: &mut Alternative<Id, T>) -> Result<(), Err> {
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
    fn visit_pat_mut(&mut self, pat: &mut Pattern<Id, T>) -> Result<(), Err> {
        if let Pattern::Dat(_, pats) | Pattern::Vec(pats) | Pattern::Tup(pats) = pat {
            for pat in pats {
                self.visit_pat_mut(pat)?;
            }
        }
        Ok(())
    }
    fn visit_binding_mut(&mut self, binding: &mut Binding<Id, T>) -> Result<(), Err> {
        let Binding { arms, .. } = binding;
        for arm in arms {
            if let Some(pred) = &mut arm.pred {
                self.visit_expr_mut(pred)?;
            };
            self.visit_expr_mut(&mut arm.body)?;
        }
        Ok(())
    }
    fn visit_stmt_mut(&mut self, stmt: &mut Statement<Id, T>) -> Result<(), Err> {
        match stmt {
            Statement::Generator(pat, expr) => {
                self.visit_pat_mut(pat)?;
                self.visit_expr_mut(expr)?;
            }
            Statement::Predicate(expr) => {
                self.visit_expr_mut(expr)?;
            }
            Statement::JustLet(bindings) => {
                for binding in bindings {
                    self.visit_binding_mut(binding)?;
                }
            }
        };
        Ok(())
    }
    fn visit_module_mut<U>(&mut self, module: &mut Module<Id, U, T>) -> Result<(), Err> {
        for binding in module
            .implems
            .iter_mut()
            .flat_map(|decl| decl.defs.iter_mut())
        {
            self.visit_binding_mut(binding)?;
        }
        for arm in module
            .fundefs
            .iter_mut()
            .flat_map(|decl| decl.defs.iter_mut())
        {
            if let Some(pred) = &mut arm.pred {
                self.visit_expr_mut(pred)?;
            };
            self.visit_expr_mut(&mut arm.body)?;
        }

        Ok(())
    }
}

pub fn var_pat_vars<Id, T, F>(pat: &Pattern<Id, T>, mut f: F)
where
    F: FnMut(&Id),
{
    match pat {
        Pattern::Var(id) => f(id),
        Pattern::Dat(_, pats) => pats.iter().for_each(|pat| var_pat_vars(pat, |id| f(id))),
        _ => {}
    }
}

impl<'a, T> Visit<Ident, T> for EdgeVisitor<'a, Ident, T> {
    fn visit_ident(&mut self, id: &Ident) -> Result<(), VisitError> {
        if let Some(idx) = self.map.get(id) {
            self.graph.connect(self.node_id, *idx);
        }
        Ok(())
    }

    fn visit_expr(&mut self, expr: &Expression<Ident, T>) -> Result<(), VisitError> {
        match expr {
            Expression::Ident(id) => {
                self.visit_ident(id)?;
            }
            Expression::Lit(_) | Expression::Path(..) => {}
            Expression::Neg(e) => self.visit_expr(e.as_ref())?,
            Expression::Infix {
                infix: _,
                left,
                right,
            } => {
                self.visit_expr(left.as_ref())?;
                self.visit_expr(right.as_ref())?;
            }
            Expression::Section(sec) => {
                self.visit_expr(sec.expr())?;
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

    fn visit_alt(&mut self, alt: &Alternative<Ident, T>) -> Result<(), VisitError> {
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

    fn visit_pat(&mut self, pat: &Pattern<Ident, T>) -> Result<(), VisitError> {
        if let Pattern::<Ident, T>::Dat(_, pats)
        | Pattern::<Ident, T>::Vec(pats)
        | Pattern::<Ident, T>::Tup(pats) = pat
        {
            for pat in pats {
                self.visit_pat(pat)?;
            }
        }
        Ok(())
    }

    fn visit_binding(&mut self, binding: &Binding<Ident, T>) -> Result<(), VisitError> {
        let Binding { arms, .. } = binding;
        if arms.len() == 1 {
            self.visit_expr(&arms[0].body)?;
            Ok(())
        } else {
            Err(VisitError::Binding.into())
        }
    }

    fn visit_stmt(&mut self, stmt: &Statement<Ident, T>) -> Result<(), VisitError> {
        match stmt {
            Statement::Generator(pat, ex) => {
                self.visit_pat(pat)?;
                self.visit_expr(ex)?;
            }
            Statement::Predicate(ex) => self.visit_expr(ex)?,
            Statement::JustLet(bnds) => {
                for binding in bnds {
                    self.visit_binding(binding)?;
                }
            }
        };
        Ok(())
    }

    fn visit_module<U>(&mut self, module: &Module<Ident, U, T>) -> Result<(), VisitError> {
        for inst in &module.implems {
            for binding in &inst.defs {
                self.visit_binding(binding)?;
            }
        }
        for fundefs in &module.fundefs {
            for arm in &fundefs.defs {
                if let Some(pred) = &arm.pred {
                    self.visit_expr(pred)?;
                }
                self.visit_expr(&arm.body)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {}
