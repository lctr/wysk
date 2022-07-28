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
    fn visit_ident(&mut self, id: &Id) -> Result<(), Err>;

    fn visit_lit(&mut self, lit: &Literal) -> Result<(), Err>;

    fn visit_path(&mut self, head: &Id, tail: &Vec<Id>) -> Result<(), Err> {
        self.visit_ident(head)?;
        for id in tail.into_iter() {
            self.visit_ident(id)?;
        }
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
                for stmt in stmts {
                    self.visit_stmt(stmt)?;
                }
                self.visit_expr(e.as_ref())?;
            }
            Expression::Dict(record) => {
                self.visit_record(record, Self::visit_expr)?;
            }
            Expression::Lambda(pat, ex) => {
                self.visit_pat(pat)?;
                self.visit_expr(ex.as_ref())?;
            }
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

    fn visit_record<X>(
        &mut self,
        record: &Record<Id, X>,
        mut f: impl FnMut(&mut Self, &X) -> Result<(), Err>,
    ) -> Result<(), Err> {
        let (ctor, fields) = match record {
            Record::Anon(fields) => (None, fields),
            Record::Data(id, fields) => (Some(id), fields),
        };
        if let Some(id) = ctor {
            self.visit_ident(id)?;
        }
        for field in fields {
            self.visit_field(field, &mut f)?;
        }
        Ok(())
    }

    fn visit_field<X>(
        &mut self,
        field: &Field<Id, X>,
        f: &mut impl FnMut(&mut Self, &X) -> Result<(), Err>,
    ) -> Result<(), Err> {
        match field {
            Field::Rest => (),
            Field::Key(id) => {
                self.visit_ident(id)?;
            }
            Field::Entry(id, x) => {
                self.visit_ident(id)?;
                f(self, x)?;
            }
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
        match pat {
            Pattern::Wild => (),
            Pattern::Var(id) => {
                self.visit_ident(id)?;
            }
            Pattern::Lit(lit) => {
                self.visit_lit(lit)?;
            }
            Pattern::Dat(id, pats) => {
                self.visit_ident(id)?;
                for pat in pats {
                    self.visit_pat(pat)?;
                }
            }
            Pattern::Tup(pats) | Pattern::Vec(pats) => {
                for pat in pats {
                    self.visit_pat(pat)?;
                }
            }
            Pattern::Lnk(head, tail) => {
                self.visit_pat(head.as_ref())?;
                self.visit_pat(tail.as_ref())?;
            }
            Pattern::At(id, pat) => {
                self.visit_ident(id)?;
                self.visit_pat(pat)?;
            }
            Pattern::Or(pats) => {
                for pat in pats {
                    self.visit_pat(pat)?;
                }
            }
            Pattern::Rec(rec) => {
                self.visit_record(rec, Self::visit_pat)?;
            }
            Pattern::Cast(pat, ty) => {
                self.visit_pat(pat.as_ref())?;
                self.visit_type(ty)?;
            }
            Pattern::Rng(a, b) => {
                self.visit_pat(a.as_ref())?;
                if let Some(pat) = b {
                    self.visit_pat(pat.as_ref())?;
                }
            }
        }

        Ok(())
    }
    fn visit_binding(&mut self, binding: &Binding<Id, T>) -> Result<(), Err> {
        let Binding { name, tipo, arms } = binding;
        self.visit_ident(name)?;
        if let Some(sig) = tipo {
            self.visit_signature(sig)?;
        }
        if arms.is_empty() {
            return Err(VisitError::Binding.into());
        } else {
            for arm in arms {
                self.visit_match(arm)?;
            }
        }
        Ok(())
    }
    fn visit_match(&mut self, arm: &Match<Id, T>) -> Result<(), Err> {
        let Match {
            args,
            pred,
            body,
            wher,
        } = arm;
        // first we go through the locally defined bindings, then we
        // look at the body of the binding.
        // should we linearize the recursive relationship between
        // bindings and matches ?? since a binding has matches, each
        // of which have bindings, each of which have matches, ..., etc.
        // recursing over this may not be the best idea...
        for wh in wher {
            self.visit_binding(wh)?;
        }
        for arg in args {
            self.visit_pat(arg)?;
        }
        if let Some(x) = pred {
            self.visit_expr(x)?;
        }
        self.visit_expr(body)?;
        Ok(())
    }
    fn visit_signature(&mut self, signature: &Signature<Id, T>) -> Result<(), Err> {
        let Signature { each, ctxt, tipo } = signature;
        self.visit_quantified(each)?;
        self.visit_contexts(ctxt)?;
        self.visit_type(tipo)?;
        Ok(())
    }
    fn visit_quantified(&mut self, qtvs: &[T]) -> Result<(), Err> {
        for tv in qtvs {
            self.visit_tyvar(tv)?;
        }
        Ok(())
    }
    fn visit_tyvar(&mut self, tyvar: &T) -> Result<(), Err> {
        #![allow(unused_variables)]
        Ok(())
    }
    fn visit_tycon(&mut self, tycon: &Con<Id, T>) -> Result<(), Err> {
        #![allow(unused_variables)]
        Ok(())
    }
    fn visit_contexts(&mut self, ctxts: &[Context<Id, T>]) -> Result<(), Err> {
        for ctxt in ctxts {
            let Context { class, head } = ctxt;
            self.visit_ident(class)?;
            self.visit_tyvar(head)?;
        }
        Ok(())
    }
    fn visit_type(&mut self, tipo: &Type<Id, T>) -> Result<(), Err> {
        match tipo {
            Type::Var(tv) => {
                self.visit_tyvar(tv)?;
            }
            Type::Con(con, tys) => {
                self.visit_tycon(con)?;
                for ty in tys {
                    self.visit_type(ty)?;
                }
            }
            Type::Fun(ta, tb) => {
                self.visit_type(ta.as_ref())?;
                self.visit_type(tb.as_ref())?;
            }
            Type::Tup(tys) => {
                for ty in tys {
                    self.visit_type(ty)?;
                }
            }
            Type::Vec(ty) => {
                self.visit_type(ty.as_ref())?;
            }
            Type::Rec(_) => todo!(),
        };
        Ok(())
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
    fn visit_ident_mut(&mut self, id: &mut Id) -> Result<(), Err>;

    fn visit_lit_mut(&mut self, lit: &mut Literal) -> Result<(), Err>;

    fn visit_path_mut(&mut self, head: &mut Id, tail: &mut Vec<Id>) -> Result<(), Err> {
        self.visit_ident_mut(head)?;
        for ident in tail {
            self.visit_ident_mut(ident)?;
        }
        Ok(())
    }

    fn visit_expr_mut(&mut self, expr: &mut Expression<Id, T>) -> Result<(), Err> {
        match expr {
            Expression::Ident(id) => {
                self.visit_ident_mut(id)?;
            }
            Expression::Lit(lit) => {
                self.visit_lit_mut(lit)?;
            }
            Expression::Path(head, tail) => {
                self.visit_path_mut(head, tail)?;
            }
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
            Expression::App(f, x) => {
                self.visit_expr_mut(f.as_mut())?;
                self.visit_expr_mut(x.as_mut())?;
            }
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
        match pat {
            Pattern::Wild => todo!(),
            Pattern::Var(_) => todo!(),
            Pattern::Lit(_) => todo!(),
            Pattern::Dat(id, pats) => {
                self.visit_ident_mut(id)?;
                for pat in pats {
                    self.visit_pat_mut(pat)?;
                }
            }
            Pattern::Vec(pats) | Pattern::Tup(pats) => {
                for pat in pats {
                    self.visit_pat_mut(pat)?;
                }
            }
            Pattern::Lnk(_, _) => todo!(),
            Pattern::At(_, _) => todo!(),
            Pattern::Or(_) => todo!(),
            Pattern::Rec(_) => todo!(),
            Pattern::Cast(_, _) => todo!(),
            Pattern::Rng(_, _) => todo!(),
        }
        Ok(())
    }
    fn visit_binding_mut(&mut self, binding: &mut Binding<Id, T>) -> Result<(), Err> {
        let Binding { name, tipo, arms } = binding;
        self.visit_ident_mut(name)?;
        if let Some(sig) = tipo {
            self.visit_signature_mut(sig)?;
        }
        if arms.is_empty() {
            return Err(VisitError::Binding.into());
        } else {
            for arm in arms {
                self.visit_match_mut(arm)?;
            }
        }
        Ok(())
    }
    fn visit_match_mut(&mut self, arm: &mut Match<Id, T>) -> Result<(), Err> {
        let Match {
            args,
            pred,
            body,
            wher,
        } = arm;
        // first we go through the locally defined bindings, then we
        // look at the body of the binding.
        // should we linearize the recursive relationship between
        // bindings and matches ?? since a binding has matches, each
        // of which have bindings, each of which have matches, ..., etc.
        // recursing over this may not be the best idea...
        for wh in wher {
            self.visit_binding_mut(wh)?;
        }
        for arg in args {
            self.visit_pat_mut(arg)?;
        }
        if let Some(x) = pred {
            self.visit_expr_mut(x)?;
        }
        self.visit_expr_mut(body)?;
        Ok(())
    }
    fn visit_signature_mut(&mut self, signature: &mut Signature<Id, T>) -> Result<(), Err> {
        let Signature { each, ctxt, tipo } = signature;
        self.visit_quantified_mut(each)?;
        self.visit_contexts_mut(ctxt)?;
        self.visit_type_mut(tipo)?;
        Ok(())
    }
    fn visit_quantified_mut(&mut self, qtvs: &mut [T]) -> Result<(), Err> {
        for tv in qtvs {
            self.visit_tyvar_mut(tv)?;
        }
        Ok(())
    }
    fn visit_tyvar_mut(&mut self, tyvar: &mut T) -> Result<(), Err> {
        #![allow(unused_variables)]
        Ok(())
    }
    fn visit_tycon_mut(&mut self, tycon: &mut Con<Id, T>) -> Result<(), Err> {
        #![allow(unused_variables)]
        Ok(())
    }
    fn visit_contexts_mut(&mut self, ctxts: &mut [Context<Id, T>]) -> Result<(), Err> {
        for ctxt in ctxts {
            let Context { class, head } = ctxt;
            self.visit_ident_mut(class)?;
            self.visit_tyvar_mut(head)?;
        }
        Ok(())
    }
    fn visit_type_mut(&mut self, tipo: &mut Type<Id, T>) -> Result<(), Err> {
        match tipo {
            Type::Var(tv) => {
                self.visit_tyvar_mut(tv)?;
            }
            Type::Con(con, tys) => {
                self.visit_tycon_mut(con)?;
                for ty in tys {
                    self.visit_type_mut(ty)?;
                }
            }
            Type::Fun(ta, tb) => {
                self.visit_type_mut(ta.as_mut())?;
                self.visit_type_mut(tb.as_mut())?;
            }
            Type::Tup(tys) => {
                for ty in tys {
                    self.visit_type_mut(ty)?;
                }
            }
            Type::Vec(ty) => {
                self.visit_type_mut(ty.as_mut())?;
            }
            Type::Rec(_) => todo!(),
        };
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

impl<'a, Id, T> Visit<Id, T> for EdgeVisitor<'a, Id, T>
where
    Id: Eq + std::hash::Hash,
{
    fn visit_ident(&mut self, id: &Id) -> Result<(), VisitError> {
        if let Some(idx) = self.map.get(id) {
            self.graph.connect(self.node_id, *idx);
        }
        Ok(())
    }

    fn visit_lit(&mut self, _: &Literal) -> Result<(), VisitError> {
        Ok(())
    }

    fn visit_expr(&mut self, expr: &Expression<Id, T>) -> Result<(), VisitError> {
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

    fn visit_alt(&mut self, alt: &Alternative<Id, T>) -> Result<(), VisitError> {
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

    fn visit_pat(&mut self, pat: &Pattern<Id, T>) -> Result<(), VisitError> {
        if let Pattern::Dat(_, pats) | Pattern::Vec(pats) | Pattern::Tup(pats) = pat {
            for pat in pats {
                self.visit_pat(pat)?;
            }
        }
        Ok(())
    }

    fn visit_binding(&mut self, binding: &Binding<Id, T>) -> Result<(), VisitError> {
        let Binding { arms, .. } = binding;
        if arms.len() == 1 {
            self.visit_expr(&arms[0].body)?;
            Ok(())
        } else {
            Err(VisitError::Binding.into())
        }
    }

    fn visit_stmt(&mut self, stmt: &Statement<Id, T>) -> Result<(), VisitError> {
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

    fn visit_module<U>(&mut self, module: &Module<Id, U, T>) -> Result<(), VisitError> {
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
