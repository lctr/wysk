use wy_lexer::Literal;
use wy_span::{Dummy, Span, Spanned};

use crate::{
    expr::{Expression, Range, Section},
    pattern::Pattern,
    record::{Field, Record},
    stmt::{Alternative, Arm, Binding, Statement},
    tipo::{
        Annotation, Con, Parameter, Predicate, Qualified, Quantified, Signature, SimpleType, Type,
    },
    Module, Program,
};

// use wy_graph::EdgeVisitor;

// use super::*;

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
pub trait Visit<Id, T = Id, E = VisitError> {
    fn visit_ident(&mut self, ident: &Id) -> Result<(), E> {
        #![allow(unused_variables)]
        Ok(())
    }
    fn visit_path(&mut self, root: &Id, tail: &[Id]) -> Result<(), E> {
        #![allow(unused_variables)]
        Ok(())
    }
    fn visit_lit(&mut self, lit: &Literal) -> Result<(), E> {
        #![allow(unused_variables)]
        Ok(())
    }

    fn visit_expr(&mut self, expr: &Expression<Id, T>) -> Result<(), E> {
        match expr {
            Expression::Ident(id) => self.visit_ident(id),
            Expression::Path(root, tail) => self.visit_path(root, &tail[..]),
            Expression::Lit(lit) => self.visit_lit(lit),
            Expression::Neg(e) => self.visit_expr(e.as_ref()),
            Expression::Infix { infix, left, right } => {
                self.visit_ident(infix)?;
                self.visit_expr(left.as_ref())?;
                self.visit_expr(right.as_ref())
            }
            Expression::Section(section) => self.visit_section(section),
            Expression::Tuple(xs) => xs
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_expr(c))),
            Expression::Array(xs) => xs
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_expr(c))),
            Expression::List(head, stmts) => stmts
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_stmt(c)))
                .and(self.visit_expr(head.as_ref())),
            Expression::Dict(record) => self.visit_record(record, Self::visit_expr),
            Expression::Lambda(pat, expr) => {
                self.visit_pat(pat).and(self.visit_expr(expr.as_ref()))
            }
            Expression::Let(binds, expr) => binds
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_binding(c)))
                .and(self.visit_expr(expr.as_ref())),
            Expression::App(f, arg) => {
                self.visit_expr(f.as_ref())?;
                self.visit_expr(arg.as_ref())
            }
            Expression::Cond(cond) => {
                let [x, y, z] = cond.as_ref();
                self.visit_expr(x)?;
                self.visit_expr(y)?;
                self.visit_expr(z)
            }
            Expression::Case(scrut, alts) => alts
                .into_iter()
                .fold(self.visit_expr(scrut.as_ref()), |a, c| {
                    a.and(self.visit_alt(c))
                }),
            Expression::Cast(e, ty) => self.visit_expr(e.as_ref()).and(self.visit_ty(ty)),
            Expression::Do(stmts, ret) => stmts
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_stmt(c)))
                .and(self.visit_expr(ret.as_ref())),
            Expression::Range(range) => self.visit_range(range.as_ref()),
            Expression::Group(x) => self.visit_expr(x.as_ref()),
        }
    }

    fn visit_section(&mut self, section: &Section<Id, T>) -> Result<(), E> {
        match section {
            Section::Prefix { prefix, right } => self
                .visit_ident(prefix)
                .and(self.visit_expr(right.as_ref())),
            Section::Suffix { left, suffix } => {
                self.visit_expr(left.as_ref()).and(self.visit_ident(suffix))
            }
        }
    }

    fn visit_range(&mut self, range: &Range<Id, T>) -> Result<(), E> {
        match range {
            Range::From(x) => self.visit_expr(x),
            Range::FromThen([x, y]) => self.visit_expr(x).and(self.visit_expr(y)),
            Range::FromTo([x, y]) => self.visit_expr(x).and(self.visit_expr(y)),
            Range::FromThenTo([x, y, z]) => self
                .visit_expr(x)
                .and(self.visit_expr(y).and(self.visit_expr(z))),
        }
    }

    fn visit_record<F, X>(&mut self, record: &Record<Id, X>, mut f: F) -> Result<(), E>
    where
        F: FnMut(&mut Self, &X) -> Result<(), E>,
    {
        match record {
            Record::Anon(fields) => fields
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_field(c, &mut f))),
            Record::Data(con, fields) => {
                self.visit_ident(con)?;
                fields
                    .into_iter()
                    .fold(Ok(()), |a, c| a.and(self.visit_field(c, &mut f)))
            }
        }
    }

    fn visit_field<F, X>(&mut self, field: &Field<Id, X>, f: &mut F) -> Result<(), E>
    where
        F: FnMut(&mut Self, &X) -> Result<(), E>,
    {
        match field {
            Field::Rest => Ok(()),
            Field::Key(k) => self.visit_ident(k),
            Field::Entry(k, v) => self.visit_ident(k).and(f(self, v)),
        }
    }

    fn visit_binding(&mut self, binding: &Binding<Id, T>) -> Result<(), E> {
        let Binding { name, tsig, arms } = binding;
        self.visit_ident(name)?;
        self.visit_signature(tsig)?;
        arms.into_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_arm(c)))
    }

    fn visit_signature(&mut self, tsig: &Signature<Id, T>) -> Result<(), E> {
        match tsig {
            Signature::Implicit => Ok(()),
            Signature::Explicit(annot) => self.visit_annot(annot),
        }
    }

    fn visit_arm(&mut self, arm: &Arm<Id, T>) -> Result<(), E> {
        let Arm {
            args,
            cond,
            body,
            wher,
        } = arm;
        wher.into_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_binding(c)))?;
        args.into_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_pat(c)))?;
        if let Some(cond) = cond {
            self.visit_expr(cond)?;
        }
        self.visit_expr(body)
    }

    fn visit_stmt(&mut self, stmt: &Statement<Id, T>) -> Result<(), E> {
        match stmt {
            Statement::Generator(pat, expr) => self.visit_pat(pat).and(self.visit_expr(expr)),
            Statement::Predicate(expr) => self.visit_expr(expr),
            Statement::JustLet(binds) => binds
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_binding(c))),
        }
    }

    fn visit_alt(&mut self, alt: &Alternative<Id, T>) -> Result<(), E> {
        let Alternative {
            pat,
            cond,
            body,
            wher,
        } = alt;
        wher.into_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_binding(c)))?;
        self.visit_pat(pat)?;
        if let Some(cond) = cond {
            self.visit_expr(cond)?;
        }
        self.visit_expr(body)
    }

    fn visit_pat(&mut self, pat: &Pattern<Id, T>) -> Result<(), E> {
        match pat {
            Pattern::Wild => Ok(()),
            Pattern::Var(id) => self.visit_ident(id),
            Pattern::Lit(lit) => self.visit_lit(lit),
            Pattern::Neg(p) => self.visit_pat(p.as_ref()),
            Pattern::Dat(con, args) => args
                .into_iter()
                .fold(self.visit_ident(con), |a, c| a.and(self.visit_pat(c))),
            Pattern::Tup(ps) => ps.into_iter().fold(Ok(()), |a, c| a.and(self.visit_pat(c))),
            Pattern::Vec(ps) => ps.into_iter().fold(Ok(()), |a, c| a.and(self.visit_pat(c))),
            Pattern::Lnk(ph, pt) => self.visit_pat(ph.as_ref()).and(self.visit_pat(pt.as_ref())),
            Pattern::At(id, p) => self.visit_ident(id).and(self.visit_pat(p.as_ref())),
            Pattern::Or(ps) => ps.into_iter().fold(Ok(()), |a, c| a.and(self.visit_pat(c))),
            Pattern::Rec(record) => self.visit_record(record, Self::visit_pat),
            Pattern::Cast(p, ty) => self.visit_pat(p.as_ref()).and(self.visit_ty(ty)),
        }
    }

    fn visit_ty(&mut self, ty: &Type<Id, T>) -> Result<(), E> {
        match ty {
            Type::Var(v) => self.visit_tyvar(v),
            Type::Con(con, args) => args
                .into_iter()
                .fold(self.visit_tycon(con), |a, c| a.and(self.visit_ty(c))),
            Type::Fun(f, arg) => self.visit_ty(f.as_ref()).and(self.visit_ty(arg.as_ref())),
            Type::Tup(ts) => ts.into_iter().fold(Ok(()), |a, c| a.and(self.visit_ty(c))),
            Type::Vec(t) => self.visit_ty(t.as_ref()),
        }
    }

    fn visit_tyvar(&mut self, var: &T) -> Result<(), E> {
        #![allow(unused_variables)]
        Ok(())
    }

    fn visit_tycon(&mut self, con: &Con<Id, T>) -> Result<(), E> {
        #![allow(unused_variables)]
        Ok(())
    }

    fn visit_annot(&mut self, annot: &Annotation<Id, T>) -> Result<(), E> {
        let Annotation { quant, qual } = annot;
        self.visit_quantified(quant).and(self.visit_qualified(qual))
    }

    fn visit_quantified(&mut self, quant: &Quantified<Id, T>) -> Result<(), E> {
        quant.iter().fold(Ok(()), |a, c| {
            a.and(
                self.visit_ident(c.head_ref())
                    .and(self.visit_tyvar(c.tail_ref())),
            )
        })
    }

    fn visit_qualified(&mut self, qual: &Qualified<Id, T>) -> Result<(), E> {
        qual.pred_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_predicate(c)))
            .and(self.visit_ty(&qual.tipo))
    }

    fn visit_predicate(&mut self, pred: &Predicate<Id, T>) -> Result<(), E> {
        let Predicate { class, head } = pred;
        self.visit_ident(class).and(self.visit_parameter(head))
    }

    fn visit_parameter(&mut self, param: &Parameter<T>) -> Result<(), E> {
        let Parameter(head, tail) = param;
        tail.into_iter()
            .fold(self.visit_tyvar(head), |a, c| a.and(self.visit_tyvar(c)))
    }

    fn visit_simple_ty(&mut self, simple_ty: &SimpleType<Id, T>) -> Result<(), E> {
        let SimpleType(head, tail) = simple_ty;
        tail.into_iter()
            .fold(self.visit_ident(head), |a, c| a.and(self.visit_tyvar(c)))
    }

    fn visit_module<P>(&mut self, module: &Module<Id, T, P>) -> Result<(), E>;

    fn visit_program<U>(&mut self, program: &Program<Id, T, U>) -> Result<(), E> {
        self.visit_module(&program.module)
    }
}
pub trait VisitMut<Id, T = Id, E = VisitError> {
    fn visit_ident_mut(&mut self, ident: &mut Id) -> Result<(), E>;
    fn visit_path_mut(&mut self, root: &mut Id, tail: &mut [Id]) -> Result<(), E> {
        #![allow(unused_variables)]
        Ok(())
    }

    fn visit_lit_mut(&mut self, lit: &mut Literal) -> Result<(), E> {
        #![allow(unused_variables)]
        Ok(())
    }

    fn visit_expr_mut(&mut self, expr: &mut Expression<Id, T>) -> Result<(), E> {
        match expr {
            Expression::Ident(id) => self.visit_ident_mut(id),
            Expression::Path(root, tail) => self.visit_path_mut(root, &mut tail[..]),
            Expression::Lit(lit) => self.visit_lit_mut(lit),
            Expression::Neg(e) => self.visit_expr_mut(e.as_mut()),
            Expression::Infix { infix, left, right } => {
                self.visit_ident_mut(infix)?;
                self.visit_expr_mut(left.as_mut())?;
                self.visit_expr_mut(right.as_mut())
            }
            Expression::Section(section) => self.visit_section_mut(section),
            Expression::Tuple(xs) => xs
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_expr_mut(c))),
            Expression::Array(xs) => xs
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_expr_mut(c))),
            Expression::List(head, stmts) => stmts
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_stmt_mut(c)))
                .and(self.visit_expr_mut(head.as_mut())),
            Expression::Dict(record) => self.visit_record_mut(record, Self::visit_expr_mut),
            Expression::Lambda(pat, expr) => self
                .visit_pat_mut(pat)
                .and(self.visit_expr_mut(expr.as_mut())),
            Expression::Let(binds, expr) => binds
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_binding_mut(c)))
                .and(self.visit_expr_mut(expr.as_mut())),
            Expression::App(f, arg) => {
                self.visit_expr_mut(f.as_mut())?;
                self.visit_expr_mut(arg.as_mut())
            }
            Expression::Cond(cond) => {
                let [x, y, z] = cond.as_mut();
                self.visit_expr_mut(x)?;
                self.visit_expr_mut(y)?;
                self.visit_expr_mut(z)
            }
            Expression::Case(scrut, alts) => alts
                .into_iter()
                .fold(self.visit_expr_mut(scrut.as_mut()), |a, c| {
                    a.and(self.visit_alt_mut(c))
                }),
            Expression::Cast(e, ty) => self.visit_expr_mut(e.as_mut()).and(self.visit_ty_mut(ty)),
            Expression::Do(stmts, ret) => stmts
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_stmt_mut(c)))
                .and(self.visit_expr_mut(ret.as_mut())),
            Expression::Range(range) => self.visit_range_mut(range.as_mut()),
            Expression::Group(x) => self.visit_expr_mut(x.as_mut()),
        }
    }

    fn visit_section_mut(&mut self, section: &mut Section<Id, T>) -> Result<(), E> {
        match section {
            Section::Prefix { prefix, right } => self
                .visit_ident_mut(prefix)
                .and(self.visit_expr_mut(right.as_mut())),
            Section::Suffix { left, suffix } => self
                .visit_expr_mut(left.as_mut())
                .and(self.visit_ident_mut(suffix)),
        }
    }

    fn visit_range_mut(&mut self, range: &mut Range<Id, T>) -> Result<(), E> {
        match range {
            Range::From(x) => self.visit_expr_mut(x),
            Range::FromThen([x, y]) => self.visit_expr_mut(x).and(self.visit_expr_mut(y)),
            Range::FromTo([x, y]) => self.visit_expr_mut(x).and(self.visit_expr_mut(y)),
            Range::FromThenTo([x, y, z]) => self
                .visit_expr_mut(x)
                .and(self.visit_expr_mut(y).and(self.visit_expr_mut(z))),
        }
    }

    fn visit_record_mut<F, X>(&mut self, record: &mut Record<Id, X>, mut f: F) -> Result<(), E>
    where
        F: FnMut(&mut Self, &mut X) -> Result<(), E>,
    {
        match record {
            Record::Anon(fields) => fields
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_field_mut(c, &mut f))),
            Record::Data(con, fields) => {
                self.visit_ident_mut(con)?;
                fields
                    .into_iter()
                    .fold(Ok(()), |a, c| a.and(self.visit_field_mut(c, &mut f)))
            }
        }
    }

    fn visit_field_mut<F, X>(&mut self, field: &mut Field<Id, X>, f: &mut F) -> Result<(), E>
    where
        F: FnMut(&mut Self, &mut X) -> Result<(), E>,
    {
        match field {
            Field::Rest => Ok(()),
            Field::Key(k) => self.visit_ident_mut(k),
            Field::Entry(k, v) => self.visit_ident_mut(k).and(f(self, v)),
        }
    }

    fn visit_binding_mut(&mut self, binding: &mut Binding<Id, T>) -> Result<(), E> {
        let Binding { name, tsig, arms } = binding;
        self.visit_ident_mut(name)?;
        self.visit_signature_mut(tsig)?;
        arms.into_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_arm_mut(c)))
    }

    fn visit_signature_mut(&mut self, tsig: &mut Signature<Id, T>) -> Result<(), E> {
        match tsig {
            Signature::Implicit => Ok(()),
            Signature::Explicit(annot) => self.visit_annot_mut(annot),
        }
    }

    fn visit_arm_mut(&mut self, arm: &mut Arm<Id, T>) -> Result<(), E> {
        let Arm {
            args,
            cond,
            body,
            wher,
        } = arm;
        wher.into_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_binding_mut(c)))?;
        args.into_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_pat_mut(c)))?;
        if let Some(cond) = cond {
            self.visit_expr_mut(cond)?;
        }
        self.visit_expr_mut(body)
    }

    fn visit_stmt_mut(&mut self, stmt: &mut Statement<Id, T>) -> Result<(), E> {
        match stmt {
            Statement::Generator(pat, expr) => {
                self.visit_pat_mut(pat).and(self.visit_expr_mut(expr))
            }
            Statement::Predicate(expr) => self.visit_expr_mut(expr),
            Statement::JustLet(binds) => binds
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_binding_mut(c))),
        }
    }

    fn visit_alt_mut(&mut self, alt: &mut Alternative<Id, T>) -> Result<(), E> {
        let Alternative {
            pat,
            cond,
            body,
            wher,
        } = alt;
        wher.into_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_binding_mut(c)))?;
        self.visit_pat_mut(pat)?;
        if let Some(cond) = cond {
            self.visit_expr_mut(cond)?;
        }
        self.visit_expr_mut(body)
    }

    fn visit_pat_mut(&mut self, pat: &mut Pattern<Id, T>) -> Result<(), E> {
        match pat {
            Pattern::Wild => Ok(()),
            Pattern::Var(id) => self.visit_ident_mut(id),
            Pattern::Lit(lit) => self.visit_lit_mut(lit),
            Pattern::Neg(p) => self.visit_pat_mut(p.as_mut()),
            Pattern::Dat(con, args) => args.into_iter().fold(self.visit_ident_mut(con), |a, c| {
                a.and(self.visit_pat_mut(c))
            }),
            Pattern::Tup(ps) => ps
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_pat_mut(c))),
            Pattern::Vec(ps) => ps
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_pat_mut(c))),
            Pattern::Lnk(ph, pt) => self
                .visit_pat_mut(ph.as_mut())
                .and(self.visit_pat_mut(pt.as_mut())),
            Pattern::At(id, p) => self.visit_ident_mut(id).and(self.visit_pat_mut(p.as_mut())),
            Pattern::Or(ps) => ps
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_pat_mut(c))),
            Pattern::Rec(record) => self.visit_record_mut(record, Self::visit_pat_mut),
            Pattern::Cast(p, ty) => self.visit_pat_mut(p.as_mut()).and(self.visit_ty_mut(ty)),
        }
    }

    fn visit_ty_mut(&mut self, ty: &mut Type<Id, T>) -> Result<(), E> {
        match ty {
            Type::Var(v) => self.visit_tyvar_mut(v),
            Type::Con(con, args) => args.into_iter().fold(self.visit_tycon_mut(con), |a, c| {
                a.and(self.visit_ty_mut(c))
            }),
            Type::Fun(f, arg) => self
                .visit_ty_mut(f.as_mut())
                .and(self.visit_ty_mut(arg.as_mut())),
            Type::Tup(ts) => ts
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_ty_mut(c))),
            Type::Vec(t) => self.visit_ty_mut(t.as_mut()),
        }
    }

    fn visit_tyvar_mut(&mut self, var: &mut T) -> Result<(), E> {
        #![allow(unused_variables)]
        Ok(())
    }
    fn visit_tycon_mut(&mut self, con: &mut Con<Id, T>) -> Result<(), E> {
        #![allow(unused_variables)]
        Ok(())
    }

    fn visit_annot_mut(&mut self, annot: &mut Annotation<Id, T>) -> Result<(), E> {
        let Annotation { quant, qual } = annot;
        self.visit_quantified_mut(quant)
            .and(self.visit_qualified_mut(qual))
    }

    fn visit_quantified_mut(&mut self, quant: &mut Quantified<Id, T>) -> Result<(), E> {
        quant.iter_mut().fold(Ok(()), |a, c| {
            a.and(
                self.visit_ident_mut(c.head_mut())
                    .and(self.visit_tyvar_mut(c.tail_mut())),
            )
        })
    }

    fn visit_qualified_mut(&mut self, qual: &mut Qualified<Id, T>) -> Result<(), E> {
        qual.pred_iter_mut()
            .fold(Ok(()), |a, c| a.and(self.visit_predicate_mut(c)))
            .and(self.visit_ty_mut(&mut qual.tipo))
    }

    fn visit_predicate_mut(&mut self, pred: &mut Predicate<Id, T>) -> Result<(), E> {
        let Predicate { class, head } = pred;
        self.visit_ident_mut(class)
            .and(self.visit_parameter_mut(head))
    }

    fn visit_parameter_mut(&mut self, param: &mut Parameter<T>) -> Result<(), E> {
        let Parameter(head, tail) = param;
        tail.into_iter().fold(self.visit_tyvar_mut(head), |a, c| {
            a.and(self.visit_tyvar_mut(c))
        })
    }

    fn visit_simple_ty_mut(&mut self, simple_ty: &mut SimpleType<Id, T>) -> Result<(), E> {
        let SimpleType(head, tail) = simple_ty;
        tail.into_iter().fold(self.visit_ident_mut(head), |a, c| {
            a.and(self.visit_tyvar_mut(c))
        })
    }

    fn visit_module_mut<P>(&mut self, module: &mut Module<Id, T, P>) -> Result<(), E>;

    fn visit_program_mut<U>(&mut self, program: &mut Program<Id, T, U>) -> Result<(), E> {
        self.visit_module_mut(&mut program.module)
    }
}

pub struct SpannedVisitor<'v, V>(pub &'v mut V);

impl<'v, V, Id, T, E> Visit<Spanned<Id>, Spanned<T>, E> for SpannedVisitor<'v, V>
where
    V: Visit<Id, T, E>,
{
    fn visit_ident(&mut self, Spanned(ident, _): &Spanned<Id>) -> Result<(), E> {
        self.0.visit_ident(ident)
    }

    fn visit_path(
        &mut self,
        Spanned(root, _): &Spanned<Id>,
        tail: &[Spanned<Id>],
    ) -> Result<(), E> {
        self.0.visit_ident(root)?;
        for Spanned(ident, _) in tail {
            self.0.visit_ident(ident)?;
        }
        Ok(())
    }

    fn visit_lit(&mut self, lit: &Literal) -> Result<(), E> {
        self.0.visit_lit(lit)
    }

    fn visit_expr(&mut self, expr: &Expression<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        match expr {
            Expression::Ident(Spanned(id, _)) => self.0.visit_ident(id),
            Expression::Path(root, tail) => self.visit_path(root, &tail[..]),
            Expression::Lit(lit) => self.visit_lit(lit),
            Expression::Neg(e) => self.visit_expr(e.as_ref()),
            Expression::Infix { infix, left, right } => {
                self.visit_ident(infix)?;
                self.visit_expr(left.as_ref())?;
                self.visit_expr(right.as_ref())
            }
            Expression::Section(section) => self.visit_section(section),
            Expression::Tuple(xs) => xs
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_expr(c))),
            Expression::Array(xs) => xs
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_expr(c))),
            Expression::List(head, stmts) => stmts
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_stmt(c)))
                .and(self.visit_expr(head.as_ref())),
            Expression::Dict(record) => self.visit_record(record, Self::visit_expr),
            Expression::Lambda(pat, expr) => {
                self.visit_pat(pat).and(self.visit_expr(expr.as_ref()))
            }
            Expression::Let(binds, expr) => binds
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_binding(c)))
                .and(self.visit_expr(expr.as_ref())),
            Expression::App(f, arg) => {
                self.visit_expr(f.as_ref())?;
                self.visit_expr(arg.as_ref())
            }
            Expression::Cond(cond) => {
                let [x, y, z] = cond.as_ref();
                self.visit_expr(x)?;
                self.visit_expr(y)?;
                self.visit_expr(z)
            }
            Expression::Case(scrut, alts) => alts
                .into_iter()
                .fold(self.visit_expr(scrut.as_ref()), |a, c| {
                    a.and(self.visit_alt(c))
                }),
            Expression::Cast(e, ty) => self.visit_expr(e.as_ref()).and(self.visit_ty(ty)),
            Expression::Do(stmts, ret) => stmts
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_stmt(c)))
                .and(self.visit_expr(ret.as_ref())),
            Expression::Range(range) => self.visit_range(range.as_ref()),
            Expression::Group(x) => self.visit_expr(x.as_ref()),
        }
    }

    fn visit_section(&mut self, section: &Section<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        match section {
            Section::Prefix { prefix, right } => self
                .visit_ident(prefix)
                .and(self.visit_expr(right.as_ref())),
            Section::Suffix { left, suffix } => {
                self.visit_expr(left.as_ref()).and(self.visit_ident(suffix))
            }
        }
    }

    fn visit_range(&mut self, range: &Range<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        match range {
            Range::From(x) => self.visit_expr(x),
            Range::FromThen([x, y]) => self.visit_expr(x).and(self.visit_expr(y)),
            Range::FromTo([x, y]) => self.visit_expr(x).and(self.visit_expr(y)),
            Range::FromThenTo([x, y, z]) => self
                .visit_expr(x)
                .and(self.visit_expr(y).and(self.visit_expr(z))),
        }
    }

    fn visit_record<F, X>(&mut self, record: &Record<Spanned<Id>, X>, mut f: F) -> Result<(), E>
    where
        F: FnMut(&mut Self, &X) -> Result<(), E>,
    {
        match record {
            Record::Anon(fields) => fields
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_field(c, &mut f))),
            Record::Data(con, fields) => {
                self.visit_ident(con)?;
                fields
                    .into_iter()
                    .fold(Ok(()), |a, c| a.and(self.visit_field(c, &mut f)))
            }
        }
    }

    fn visit_field<F, X>(&mut self, field: &Field<Spanned<Id>, X>, f: &mut F) -> Result<(), E>
    where
        F: FnMut(&mut Self, &X) -> Result<(), E>,
    {
        match field {
            Field::Rest => Ok(()),
            Field::Key(Spanned(k, _)) => self.0.visit_ident(k),
            Field::Entry(Spanned(k, _), v) => self.0.visit_ident(k).and(f(self, v)),
        }
    }

    fn visit_binding(&mut self, binding: &Binding<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        let Binding {
            name: Spanned(name, _),
            tsig,
            arms,
        } = binding;
        self.0.visit_ident(name)?;
        self.visit_signature(tsig)?;
        arms.into_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_arm(c)))
    }

    fn visit_signature(&mut self, tsig: &Signature<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        match tsig {
            Signature::Implicit => Ok(()),
            Signature::Explicit(annot) => self.visit_annot(annot),
        }
    }

    fn visit_arm(&mut self, arm: &Arm<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        let Arm {
            args,
            cond,
            body,
            wher,
        } = arm;
        wher.into_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_binding(c)))?;
        args.into_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_pat(c)))?;
        if let Some(cond) = cond {
            self.visit_expr(cond)?;
        }
        self.visit_expr(body)
    }

    fn visit_stmt(&mut self, stmt: &Statement<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        match stmt {
            Statement::Generator(pat, expr) => self.visit_pat(pat).and(self.visit_expr(expr)),
            Statement::Predicate(expr) => self.visit_expr(expr),
            Statement::JustLet(binds) => binds
                .into_iter()
                .fold(Ok(()), |a, c| a.and(self.visit_binding(c))),
        }
    }

    fn visit_alt(&mut self, alt: &Alternative<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        let Alternative {
            pat,
            cond,
            body,
            wher,
        } = alt;
        wher.into_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_binding(c)))?;
        self.visit_pat(pat)?;
        if let Some(cond) = cond {
            self.visit_expr(cond)?;
        }
        self.visit_expr(body)
    }

    fn visit_pat(&mut self, pat: &Pattern<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        match pat {
            Pattern::Wild => Ok(()),
            Pattern::Var(Spanned(id, _)) => self.0.visit_ident(id),
            Pattern::Lit(lit) => self.0.visit_lit(lit),
            Pattern::Neg(p) => self.visit_pat(p.as_ref()),
            Pattern::Dat(Spanned(con, _), args) => args
                .into_iter()
                .fold(self.0.visit_ident(con), |a, c| a.and(self.visit_pat(c))),
            Pattern::Tup(ps) => ps.into_iter().fold(Ok(()), |a, c| a.and(self.visit_pat(c))),
            Pattern::Vec(ps) => ps.into_iter().fold(Ok(()), |a, c| a.and(self.visit_pat(c))),
            Pattern::Lnk(ph, pt) => self.visit_pat(ph.as_ref()).and(self.visit_pat(pt.as_ref())),
            Pattern::At(Spanned(id, _), p) => {
                self.0.visit_ident(id).and(self.visit_pat(p.as_ref()))
            }
            Pattern::Or(ps) => ps.into_iter().fold(Ok(()), |a, c| a.and(self.visit_pat(c))),
            Pattern::Rec(record) => self.visit_record(record, Self::visit_pat),
            Pattern::Cast(p, ty) => self.visit_pat(p.as_ref()).and(self.visit_ty(ty)),
        }
    }

    fn visit_ty(&mut self, ty: &Type<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        match ty {
            Type::Var(Spanned(v, _)) => self.0.visit_tyvar(v),
            Type::Con(con, args) => args
                .into_iter()
                .fold(self.visit_tycon(con), |a, c| a.and(self.visit_ty(c))),
            Type::Fun(f, arg) => self.visit_ty(f.as_ref()).and(self.visit_ty(arg.as_ref())),
            Type::Tup(ts) => ts.into_iter().fold(Ok(()), |a, c| a.and(self.visit_ty(c))),
            Type::Vec(t) => self.visit_ty(t.as_ref()),
        }
    }

    fn visit_tyvar(&mut self, Spanned(var, _): &Spanned<T>) -> Result<(), E> {
        self.0.visit_tyvar(var)
    }

    fn visit_tycon(&mut self, con: &Con<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        match con {
            Con::List => self.0.visit_tycon(&Con::List),
            Con::Tuple(n) => self.0.visit_tycon(&Con::Tuple(*n)),
            Con::Arrow => self.0.visit_tycon(&Con::Arrow),
            Con::Named(Spanned(id, _)) => self.0.visit_ident(id),
            Con::Varied(Spanned(tv, _)) => self.0.visit_tyvar(tv),
        }
    }

    fn visit_annot(&mut self, annot: &Annotation<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        let Annotation { quant, qual } = annot;
        self.visit_quantified(quant).and(self.visit_qualified(qual))
    }

    fn visit_quantified(&mut self, quant: &Quantified<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        quant.iter().fold(Ok(()), |a, c| {
            a.and(
                self.0
                    .visit_ident(c.head_ref().item())
                    .and(self.0.visit_tyvar(c.tail_ref().item())),
            )
        })
    }

    fn visit_qualified(&mut self, qual: &Qualified<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        qual.pred_iter()
            .fold(Ok(()), |a, c| a.and(self.visit_predicate(c)))
            .and(self.visit_ty(&qual.tipo))
    }

    fn visit_predicate(&mut self, pred: &Predicate<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        let Predicate { class, head } = pred;
        self.0
            .visit_ident(class.item())
            .and(self.visit_parameter(head))
    }

    fn visit_parameter(&mut self, param: &Parameter<Spanned<T>>) -> Result<(), E> {
        let Parameter(head, tail) = param;
        tail.into_iter()
            .fold(self.0.visit_tyvar(head.item()), |a, c| {
                a.and(self.0.visit_tyvar(c.item()))
            })
    }

    fn visit_simple_ty(
        &mut self,
        simple_ty: &SimpleType<Spanned<Id>, Spanned<T>>,
    ) -> Result<(), E> {
        let SimpleType(head, tail) = simple_ty;
        tail.into_iter()
            .fold(self.0.visit_ident(head.item()), |a, c| {
                a.and(self.0.visit_tyvar(c.item()))
            })
    }

    /// Not implemented since modules aren't parametrized by spanned wrappers
    fn visit_module<P>(&mut self, _: &Module<Spanned<Id>, Spanned<T>, P>) -> Result<(), E> {
        Ok(())
    }
}

impl<'v, V, Id, T, E> VisitMut<Spanned<Id>, Spanned<T>, E> for SpannedVisitor<'v, V>
where
    V: VisitMut<Id, T, E>,
{
    fn visit_ident_mut(&mut self, Spanned(ident, _): &mut Spanned<Id>) -> Result<(), E> {
        self.0.visit_ident_mut(ident)
    }

    fn visit_tyvar_mut(&mut self, Spanned(var, _): &mut Spanned<T>) -> Result<(), E> {
        self.0.visit_tyvar_mut(var)
    }

    fn visit_tycon_mut(&mut self, con: &mut Con<Spanned<Id>, Spanned<T>>) -> Result<(), E> {
        // Tricking the type checker into updating a `Con<Spanned<A>,
        // Spanned<B>>` from a modified `Con<A, B>`
        fn map_spanned<A, B>(
            con: Con<A, B>,
            span_a: Span,
            span_b: Span,
        ) -> Con<Spanned<A>, Spanned<B>> {
            use wy_common::functor::*;
            con.map_fst(&mut Func::New(|id| Spanned(id, span_a)))
                .map_snd(&mut Func::New(|t| Spanned(t, span_b)))
        }
        match con {
            Con::List => {
                let mut listcon = Con::List;
                self.0.visit_tycon_mut(&mut listcon)?;
                *con = map_spanned(listcon, Span::DUMMY, Span::DUMMY);
                Ok(())
            }
            Con::Tuple(n) => {
                let mut tupcon = Con::Tuple(*n);
                self.0.visit_tycon_mut(&mut tupcon)?;
                *con = map_spanned(tupcon, Span::DUMMY, Span::DUMMY);
                Ok(())
            }
            Con::Arrow => {
                let mut fcon = Con::Arrow;
                self.0.visit_tycon_mut(&mut fcon)?;
                *con = map_spanned(fcon, Span::DUMMY, Span::DUMMY);
                Ok(())
            }
            Con::Named(Spanned(id, _)) => self.0.visit_ident_mut(id),
            Con::Varied(Spanned(tv, _)) => self.0.visit_tyvar_mut(tv),
        }
    }

    fn visit_module_mut<P>(&mut self, _: &mut Module<Spanned<Id>, Spanned<T>, P>) -> Result<(), E> {
        Ok(())
    }

    fn visit_program_mut<U>(
        &mut self,
        _: &mut Program<Spanned<Id>, Spanned<T>, U>,
    ) -> Result<(), E> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {}
