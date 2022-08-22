use wy_lexer::Token;
use wy_name::Chain;
use wy_span::{BytePos, Span, Spanned};

use crate::{
    attr::{Attribute, DocLine, Pragma},
    decl::{
        AliasDecl, ClassDecl, DataDecl, FixityDecl, FnDecl, InstDecl, MethodBody, MethodDef,
        NewtypeDecl, Selector, TypeArg, TypeArgs, Variant, WithClause,
    },
    expr::Expression,
    pattern::Pattern,
    record::{Field, Record},
    stmt::{Alternative, Arm, Binding, Branch, Guard, LocalDef, Statement},
    tipo::{
        Annotation, Con, Parameter, Predicate, Qualified, Quantified, Signature, SimpleType, Type,
        Var,
    },
    Import, ImportSpec, Module,
};

pub trait ReSpan {
    /// Returns a vector containing mutable references to *all* spans
    /// held by the type.
    ///
    /// The default functionality and implementation of this trait
    /// relies on this method being correctly implemented as spans
    /// will first be collected mutably and then modified as opposed
    /// spans being modified during traversal of the type.
    fn spans_mut(&mut self) -> Vec<&mut Span>;

    /// Modifies in-place the spans contained by a type, shifting
    /// spans by adding the given `byte_offset` to the start and end
    /// of every respective span.
    ///
    /// This method is currently implemented by default, relying on
    /// first collecting mutable references to all inner spans in a
    /// vector before incremnting in place.
    fn respan(&mut self, byte_offset: BytePos) {
        for span in self.spans_mut() {
            *span += byte_offset;
        }
    }
}

impl<X> ReSpan for Vec<X>
where
    X: ReSpan,
{
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        self.into_iter().flat_map(|x| x.spans_mut()).collect()
    }
}

impl<X> ReSpan for Option<X>
where
    X: ReSpan,
{
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        match self {
            Some(x) => x.spans_mut(),
            None => vec![],
        }
    }
}

impl<X> ReSpan for Token<X> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        vec![&mut self.span]
    }
}

impl<Id, T, P> ReSpan for Module<Id, T, P> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        let Module {
            srcpath: _,
            modname: _,
            imports,
            infixes,
            datatys,
            classes,
            implems,
            fundefs,
            aliases,
            newtyps,
            pragmas,
        } = self;
        spans.extend(imports.spans_mut());
        spans.extend(infixes.spans_mut());
        spans.extend(datatys.spans_mut());
        spans.extend(classes.spans_mut());
        spans.extend(implems.spans_mut());
        spans.extend(fundefs.spans_mut());
        spans.extend(aliases.spans_mut());
        spans.extend(newtyps.spans_mut());
        spans.extend(pragmas.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for Pragma<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let Pragma { span, plmt, attr } = self;
        let mut spans = vec![];
        spans.push(&mut self.span);
        spans.extend(self.attr.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for Attribute<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        match self {
            Attribute::Test
            | Attribute::Todo
            | Attribute::Inline
            | Attribute::NoInline
            | Attribute::Fixity(_) => (),
            Attribute::Doc(docline) => spans.extend(docline.spans_mut()),
            Attribute::Derive(spnds) => spans.extend(spnds.into_iter().map(Spanned::span_mut)),
            Attribute::Specialize(spnd, tys) => {
                spans.push(spnd.span_mut());
                spans.extend(tys.spans_mut());
            }
            Attribute::Custom(spnd, tokens) => {
                spans.push(spnd.span_mut());
                spans.extend(tokens.spans_mut());
            }
        };
        spans
    }
}

impl ReSpan for DocLine {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        vec![&mut self.span]
    }
}

impl<Id> ReSpan for Chain<Spanned<Id>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        self.iter_mut().map(Spanned::span_mut).collect()
    }
}

impl<Id> ReSpan for FixityDecl<Spanned<Id>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let FixityDecl { span, infixes, fixity, from_pragma } = self;
        let mut spans = vec![];
        spans.push(&mut self.span);
        spans.extend(self.infixes.iter_mut().map(|sp| sp.span_mut()));
        spans
    }
}

impl<Id> ReSpan for ImportSpec<Spanned<Id>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let ImportSpec { name, qualified, rename, hidden, imports } = self;
        let mut spans = vec![];
        spans.extend(self.name.spans_mut());
        if let Some(spnd) = self.rename.as_mut() {
            spans.push(spnd.span_mut());
        }
        spans.extend(self.imports.spans_mut());
        spans
    }
}

impl<Id> ReSpan for Import<Spanned<Id>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        match self {
            Import::Operator(spnd)
            | Import::Function(spnd)
            | Import::Abstract(spnd)
            | Import::Total(spnd) => spans.push(spnd.span_mut()),
            Import::Partial(head, tail) => {
                spans.push(head.span_mut());
                spans.extend(tail.into_iter().map(Spanned::span_mut));
            }
        };
        spans
    }
}

impl<Id, T> ReSpan for DataDecl<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let DataDecl {
        //     span,
        //     prag,
        //     tdef,
        //     pred,
        //     vnts,
        //     with,
        // } = self;
        let mut spans = vec![];
        spans.push(&mut self.span);
        spans.extend(self.prag.spans_mut());
        spans.extend(self.tdef.spans_mut());
        spans.extend(self.pred.spans_mut());
        spans.extend(self.vnts.spans_mut());
        spans.extend(self.with.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for SimpleType<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let SimpleType(head, tail) = self;
        let mut spans = vec![];
        spans.push(self.0.span_mut());
        spans.extend(self.1.iter_mut().map(Spanned::span_mut));
        spans
    }
}

impl<Id, T> ReSpan for Variant<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let Variant {
        //     name,
        //     span,
        //     prag,
        //     args,
        // } = self;
        let mut spans = vec![];
        spans.push(self.name.span_mut());
        spans.push(&mut self.span);
        spans.extend(self.prag.spans_mut());
        spans.extend(self.args.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for TypeArgs<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        match self {
            TypeArgs::Curried(tys) => spans.extend(tys.spans_mut()),
            TypeArgs::Record(sels) => spans.extend(sels.spans_mut()),
        };
        spans
    }
}

impl<Id, T> ReSpan for Selector<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        spans.push(self.name.span_mut());
        spans.extend(self.tipo.spans_mut());
        spans
    }
}

impl<Id> ReSpan for WithClause<Spanned<Id>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let WithClause { span, names, from_pragma } = self;
        let mut spans = vec![];
        spans.push(&mut self.span);
        spans.extend(self.names.iter_mut().map(|name| name.span_mut()));
        spans
    }
}

impl<Id, T> ReSpan for NewtypeDecl<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let NewtypeDecl {
        //     span,
        //     prag,
        //     tdef,
        //     ctor,
        //     narg,
        //     with,
        // } = self;
        let mut spans = vec![];
        spans.push(&mut self.span);
        spans.extend(self.prag.spans_mut());
        spans.extend(self.tdef.spans_mut());
        spans.push(self.ctor.span_mut());
        spans.extend(self.narg.spans_mut());
        spans.extend(self.with.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for TypeArg<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        match self {
            TypeArg::Empty(_) => (),
            TypeArg::Type(ty) => spans.extend(ty.spans_mut()),
            TypeArg::Selector(sel) => spans.extend(sel.spans_mut()),
        };
        spans
    }
}

impl<Id, T> ReSpan for AliasDecl<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let AliasDecl {
        //     span,
        //     prag,
        //     ldef,
        //     tipo,
        // } = self;
        let mut spans = vec![];
        spans.push(&mut self.span);
        spans.extend(self.prag.spans_mut());
        spans.extend(self.ldef.spans_mut());
        spans.extend(self.tipo.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for ClassDecl<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let ClassDecl {
        //     span,
        //     prag,
        //     cdef,
        //     pred,
        //     defs,
        // } = self;
        let mut spans = vec![];
        spans.push(&mut self.span);
        spans.extend(self.prag.spans_mut());
        spans.extend(self.cdef.spans_mut());
        spans.extend(self.pred.spans_mut());
        spans.extend(self.defs.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for MethodDef<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let MethodDef {
        //     span,
        //     prag,
        //     name,
        //     annt,
        //     body,
        // } = self;
        let mut spans = vec![];
        spans.push(&mut self.span);
        spans.extend(self.prag.spans_mut());
        spans.push(self.name.span_mut());
        spans.extend(self.annt.spans_mut());
        spans.extend(self.body.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for MethodBody<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        match self {
            MethodBody::Unimplemented => (),
            MethodBody::Default(arms) => spans.extend(arms.spans_mut()),
        };
        spans
    }
}

impl<Id, T> ReSpan for InstDecl<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let InstDecl {
        //     span,
        //     prag,
        //     name,
        //     tipo,
        //     pred,
        //     defs,
        // } = self;
        let mut spans = vec![];
        spans.push(&mut self.span);
        spans.extend(self.prag.spans_mut());
        spans.push(self.name.span_mut());
        spans.extend(self.tipo.spans_mut());
        spans.extend(self.pred.spans_mut());
        spans.extend(self.defs.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for FnDecl<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let FnDecl {
        //     span,
        //     prag,
        //     name,
        //     sign,
        //     defs,
        // } = self;
        let mut spans = vec![];
        spans.push(&mut self.span);
        spans.extend(self.prag.spans_mut());
        spans.push(self.name.span_mut());
        spans.extend(self.sign.spans_mut());
        spans.extend(self.defs.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for Expression<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        match self {
            Expression::Ident(Spanned(_, sp)) => spans.push(sp),
            Expression::Path(Spanned(_, sp_head), sps) => {
                spans.push(sp_head);
                for Spanned(_, sp) in sps {
                    spans.push(sp)
                }
            }
            Expression::Lit(_) => (),
            Expression::Neg(x) | Expression::Group(x) => spans.extend(x.spans_mut()),
            Expression::Infix { infix, left, right } => {
                spans.push(infix.span_mut());
                spans.extend(left.spans_mut());
                spans.extend(right.spans_mut());
            }
            Expression::Section(sec) => {
                let (affix, subexpr) = sec.parts_mut();
                spans.push(affix.span_mut());
                spans.extend(subexpr.spans_mut());
            }
            Expression::Tuple(xs) | Expression::Array(xs) => {
                spans.extend(xs.into_iter().flat_map(Self::spans_mut))
            }
            Expression::List(head, quals) => {
                spans.extend(head.spans_mut());
                spans.extend(quals.spans_mut());
            }
            Expression::Dict(rec) => {
                let fields = match rec {
                    Record::Anon(fields) => fields,
                    Record::Data(spnd, fields) => {
                        spans.push(spnd.span_mut());
                        fields
                    }
                };
                fields.into_iter().for_each(|field| match field {
                    Field::Rest => (),
                    Field::Key(spnd) => spans.push(spnd.span_mut()),
                    Field::Entry(spnd, rhs) => {
                        spans.push(spnd.span_mut());
                        spans.extend(rhs.spans_mut())
                    }
                })
            }
            Expression::Lambda(arg, body) => {
                spans.extend(arg.spans_mut());
                spans.extend(body.spans_mut())
            }
            Expression::Let(binds, body) => {
                spans.extend(binds.spans_mut());
                spans.extend(body.spans_mut())
            }
            Expression::App(head, arg) => {
                spans.extend(head.spans_mut());
                spans.extend(arg.spans_mut());
            }
            Expression::Cond(xyz) => {
                spans.extend(xyz.as_mut().into_iter().flat_map(Self::spans_mut))
            }
            Expression::Case(scrut, alts) => {
                spans.extend(scrut.spans_mut());
                spans.extend(alts.spans_mut())
            }
            Expression::Cast(x, ty) => {
                spans.extend(x.spans_mut());
                spans.extend(ty.spans_mut());
            }
            Expression::Do(stmts, ret) => {
                spans.extend(stmts.spans_mut());
                spans.extend(ret.spans_mut());
            }
            Expression::Range(range) => {
                let (start, rest) = range.parts_mut();
                spans.extend(start.spans_mut());
                spans.extend(rest.into_iter().flatten().flat_map(Self::spans_mut));
            }
        };
        spans
    }
}

impl<Id, T> ReSpan for Pattern<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        match self {
            Pattern::Wild | Pattern::Lit(_) => (),
            Pattern::Var(spnd) => spans.push(spnd.span_mut()),
            Pattern::Neg(pat) => spans.extend(pat.spans_mut()),
            Pattern::Dat(con, args) => {
                spans.push(con.span_mut());
                spans.extend(args.spans_mut());
            }
            Pattern::Tup(ps) | Pattern::Vec(ps) | Pattern::Or(ps) => {
                spans.extend(ps.into_iter().flat_map(Self::spans_mut))
            }
            Pattern::Lnk(head, tail) => {
                spans.extend(head.spans_mut());
                spans.extend(tail.spans_mut());
            }
            Pattern::At(spanned, pat) => {
                spans.push(spanned.span_mut());
                spans.extend(pat.spans_mut());
            }
            Pattern::Rec(rec) => spans.extend(rec.spans_mut()),
            Pattern::Cast(pat, ty) => {
                spans.extend(pat.spans_mut());
                spans.extend(ty.spans_mut());
            }
        };
        spans
    }
}

impl<Id, T> ReSpan for Binding<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        spans.push(self.name.span_mut());
        spans.extend(self.tsig.spans_mut());
        spans.extend(self.arms.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for Arm<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        spans.extend(self.args.spans_mut());
        spans.extend(self.cond.spans_mut());
        spans.extend(self.wher.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for Alternative<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        spans.extend(self.pat.spans_mut());
        spans.extend(self.cond.spans_mut());
        spans.extend(self.body.spans_mut());
        spans.extend(self.wher.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for Statement<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        match self {
            Statement::Generator(pat, expr) => {
                spans.extend(pat.spans_mut());
                spans.extend(expr.spans_mut());
            }
            Statement::Predicate(pred) => spans.extend(pred.spans_mut()),
            Statement::JustLet(binds) => spans.extend(binds.spans_mut()),
        };
        spans
    }
}

impl<Id, T> ReSpan for Con<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        match self {
            Con::List | Con::Tuple(_) | Con::Arrow => vec![],
            Con::Named(spnd) => vec![spnd.span_mut()],
            Con::Varied(spnd) => vec![spnd.span_mut()],
        }
    }
}

impl<Id, T> ReSpan for Type<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        match self {
            Type::Var(spnd) => spans.push(spnd.span_mut()),
            Type::Con(spnd, args) => {
                spans.extend(spnd.spans_mut());
                spans.extend(args.spans_mut());
            }
            Type::Fun(ta, tb) => {
                spans.extend(ta.spans_mut());
                spans.extend(tb.spans_mut());
            }
            Type::Tup(ts) => spans.extend(ts.spans_mut()),
            Type::Vec(t) => spans.extend(t.spans_mut()),
        };
        spans
    }
}

impl<Id, T> ReSpan for Signature<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        match self {
            Signature::Implicit => (),
            Signature::Explicit(annot) => spans.extend(annot.spans_mut()),
        };
        spans
    }
}

impl<Id, T> ReSpan for Annotation<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        spans.extend(self.quant.spans_mut());
        spans.extend(self.qual.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for Quantified<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // since `Quantified` holds a vector of `Var`s, each from which
        // 2 spans are contributed
        let mut spans = Vec::with_capacity(2 * self.0.len());
        for v in &mut self.0 {
            spans.extend(v.spans_mut());
        }
        spans
    }
}

impl<Id, T> ReSpan for Var<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        vec![self.0.span_mut(), self.1.span_mut()]
    }
}

impl<Id, T> ReSpan for Qualified<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let Qualified { pred, tipo } = self;
        let mut spans = vec![];
        spans.extend(self.pred.spans_mut());
        spans.extend(self.tipo.spans_mut());
        spans
    }
}

impl<Id, T> ReSpan for Predicate<Spanned<Id>, Spanned<T>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let Predicate { class, head } = self;
        let mut spans = vec![];
        spans.push(self.class.span_mut());
        spans.extend(self.head.spans_mut());
        spans
    }
}

impl<Id> ReSpan for Parameter<Spanned<Id>> {
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        // let Parameter(head, tail) = self;
        let mut spans = vec![];
        spans.push(self.0.span_mut());
        spans.extend(self.1.iter_mut().map(|sp| sp.span_mut()));
        spans
    }
}

impl<Id, X> ReSpan for Record<Spanned<Id>, X>
where
    X: ReSpan,
{
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        match self {
            Record::Anon(fields) => spans.extend(fields.spans_mut()),
            Record::Data(spnd, fields) => {
                spans.push(spnd.span_mut());
                spans.extend(fields.spans_mut())
            }
        };
        spans
    }
}

impl<Id, X> ReSpan for Field<Spanned<Id>, X>
where
    X: ReSpan,
{
    fn spans_mut(&mut self) -> Vec<&mut Span> {
        let mut spans = vec![];
        match self {
            Field::Rest => (),
            Field::Key(spnd) => spans.push(spnd.span_mut()),
            Field::Entry(spnd, rhs) => {
                spans.push(spnd.span_mut());
                spans.extend(rhs.spans_mut())
            }
        };
        spans
    }
}
