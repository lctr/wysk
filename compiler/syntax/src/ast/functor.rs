use crate::{
    attr::{Attribute, Pragma},
    decl::{
        AliasDecl, ClassDecl, DataDecl, Declaration, FnDecl, InstDecl, MethodBody, MethodDef,
        MethodImpl, NewtypeDecl, Selector, TypeArg, TypeArgs, Variant, WithClause,
    },
    expr::{Expression, Range, Section},
    pattern::Pattern,
    record::{Field, Record},
    stmt::{Alternative, Arm, Binding, Statement},
    tipo::{Annotation, Con, Predicate, Qualified, Quantified, Signature, SimpleType, Type, Var},
    Module, Program,
};
use wy_common::functor::{Func, Functor, MapFst, MapSnd, MapThrd};
use wy_span::Spanned;

impl<Id, T, U, A> MapFst<Id, A> for Program<Id, T, U>
where
    Id: Eq + std::hash::Hash,
    A: Eq + std::hash::Hash,
{
    type WrapFst = Program<A, T, U>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> A,
    {
        let Program {
            module,
            fixities,
            comments,
        } = self;
        let module = module.map_fst(f);
        let fixities = fixities.into_iter().map(|pair| pair.map_fst(f)).collect();
        Program {
            module,
            fixities,
            comments,
        }
    }
}

impl<Id, U, T, A> MapSnd<T, A> for Program<Id, T, U> {
    type WrapSnd = Program<Id, A, U>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(T) -> A,
    {
        let Program {
            module,
            fixities,
            comments,
        } = self;
        let module = module.map_snd(f);
        Program {
            module,
            fixities,
            comments,
        }
    }
}

impl<Id, U, T, A> MapThrd<U, A> for Program<Id, T, U> {
    type WrapThrd = Program<Id, T, A>;

    fn map_thrd<F>(self, f: &mut Func<'_, F>) -> Self::WrapThrd
    where
        F: FnMut(U) -> A,
    {
        let Program {
            module,
            fixities,
            comments,
        } = self;
        let module = module.map_thrd(f);
        Program {
            module,
            fixities,
            comments,
        }
    }
}

impl<Id, T, U, X> MapFst<Id, X> for Module<Id, T, U> {
    type WrapFst = Module<X, T, U>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let Module {
            srcpath: uid,
            modname,
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
        let modname = modname.mapf(f);
        let f = &mut Func::New(|spanned: Spanned<Id>| spanned.mapf(f));
        let imports = imports.into_iter().map(|i| i.mapf(f)).collect();
        let infixes = infixes.into_iter().map(|d| d.mapf(f)).collect();
        let datatys = datatys.map_fst(f);
        let classes = classes.map_fst(f);
        let implems = implems.map_fst(f);
        let fundefs = fundefs.map_fst(f);
        let aliases = aliases.map_fst(f);
        let newtyps = newtyps.map_fst(f);
        let pragmas = pragmas.map_fst(f);
        Module {
            srcpath: uid,
            modname,
            imports,
            infixes,
            datatys,
            classes,
            implems,
            fundefs,
            aliases,
            newtyps,
            pragmas,
        }
    }
}

impl<Id, T, U, X> MapThrd<U, X> for Module<Id, T, U> {
    type WrapThrd = Module<Id, T, X>;

    fn map_thrd<F>(self, f: &mut Func<'_, F>) -> Self::WrapThrd
    where
        F: FnMut(U) -> X,
    {
        let Module {
            srcpath: uid,
            modname,
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
        let uid = f.apply(uid);
        Module {
            srcpath: uid,
            modname,
            imports,
            infixes,
            datatys,
            classes,
            implems,
            fundefs,
            aliases,
            newtyps,
            pragmas,
        }
    }
}

impl<Id, T, U, X> MapSnd<T, X> for Module<Id, T, U> {
    type WrapSnd = Module<Id, X, U>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(T) -> X,
    {
        let Module {
            srcpath,
            modname,
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
        let f = &mut Func::New(|spanned: Spanned<T>| spanned.mapf(f));
        let datatys = datatys.map_snd(f);
        let classes = classes.map_snd(f);
        let implems = implems.map_snd(f);
        let fundefs = fundefs.map_snd(f);
        let aliases = aliases.map_snd(f);
        let newtyps = newtyps.map_snd(f);
        let pragmas = pragmas.map_snd(f);
        Module {
            srcpath,
            modname,
            imports,
            infixes,
            datatys,
            classes,
            implems,
            fundefs,
            aliases,
            newtyps,
            pragmas,
        }
    }
}

// //////////////////////

impl<Id, V, X> MapFst<Id, X> for Pragma<Id, V> {
    type WrapFst = Pragma<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        Pragma {
            span: self.span,
            plmt: self.plmt,
            attr: self.attr.map_fst(f),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Pragma<Id, V> {
    type WrapSnd = Pragma<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        Pragma {
            span: self.span,
            plmt: self.plmt,
            attr: self.attr.map_snd(f),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Attribute<Id, V> {
    type WrapFst = Attribute<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Attribute::Test => Attribute::Test,
            Attribute::Todo => Attribute::Todo,
            Attribute::Inline => Attribute::Inline,
            Attribute::NoInline => Attribute::NoInline,
            Attribute::Doc(doc) => Attribute::Doc(doc),
            Attribute::Fixity(fixity) => Attribute::Fixity(fixity),
            Attribute::Derive(ids) => {
                Attribute::Derive(ids.into_iter().map(|id| f.apply(id)).collect())
            }
            Attribute::Specialize(tys) => Attribute::Specialize(tys.map_fst(f)),
            Attribute::Custom(id, tokens) => Attribute::Custom(f.apply(id), tokens),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Attribute<Id, V> {
    type WrapSnd = Attribute<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Attribute::Test => Attribute::Test,
            Attribute::Todo => Attribute::Todo,
            Attribute::Inline => Attribute::Inline,
            Attribute::NoInline => Attribute::NoInline,
            Attribute::Doc(doc) => Attribute::Doc(doc),
            Attribute::Fixity(fixity) => Attribute::Fixity(fixity),
            Attribute::Derive(ids) => Attribute::Derive(ids),
            Attribute::Specialize(tys) => Attribute::Specialize(tys.map_snd(f)),
            Attribute::Custom(id, tokens) => Attribute::Custom(id, tokens),
        }
    }
}

// //////////////////////

impl<Id, V, X> MapFst<Id, X> for DataDecl<Id, V> {
    type WrapFst = DataDecl<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let DataDecl {
            span,
            prag,
            tdef,
            pred,
            vnts,
            with,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_fst(f)).collect();
        let tdef = tdef.map_fst(f);
        let pred = pred.map_fst(f);
        let vnts = vnts.map_fst(f);
        let with = with.map(|w| w.fmap(f));
        DataDecl {
            span,
            prag,
            tdef,
            pred,
            vnts,
            with,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for DataDecl<Id, V> {
    type WrapSnd = DataDecl<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let DataDecl {
            span,
            prag,
            tdef,
            pred,
            vnts,
            with,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_snd(f)).collect();
        let tdef = tdef.map_snd(f);
        let pred = pred.map_snd(f);
        let vnts = vnts.map_snd(f);
        DataDecl {
            span,
            prag,
            tdef,
            pred,
            vnts,
            with,
        }
    }
}

impl<Id, X> Functor<Id, X> for WithClause<Id> {
    type Wrapper = WithClause<X>;

    fn fmap<F>(self, f: &mut Func<'_, F>) -> Self::Wrapper
    where
        F: FnMut(Id) -> X,
    {
        WithClause {
            span: self.span,
            names: self.names.map_fst(f),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Selector<Id, V> {
    type WrapFst = Selector<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        Selector {
            name: f.apply(self.name),
            tipo: self.tipo.map_fst(f),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Selector<Id, V> {
    type WrapSnd = Selector<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        Selector {
            name: self.name,
            tipo: self.tipo.map_snd(f),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for TypeArg<Id, V> {
    type WrapFst = TypeArg<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            TypeArg::Empty(_) => TypeArg::Empty(std::marker::PhantomData),
            TypeArg::Type(t) => TypeArg::Type(t.map_fst(f)),
            TypeArg::Selector(sel) => TypeArg::Selector(sel.map_fst(f)),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for TypeArg<Id, V> {
    type WrapSnd = TypeArg<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            TypeArg::Empty(_) => TypeArg::Empty(std::marker::PhantomData),
            TypeArg::Type(t) => TypeArg::Type(t.map_snd(f)),
            TypeArg::Selector(sel) => TypeArg::Selector(sel.map_snd(f)),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for TypeArgs<Id, V> {
    type WrapFst = TypeArgs<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            TypeArgs::Curried(t) => TypeArgs::Curried(t.map_fst(f)),
            TypeArgs::Record(sel) => TypeArgs::Record(sel.map_fst(f)),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for TypeArgs<Id, V> {
    type WrapSnd = TypeArgs<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            TypeArgs::Curried(t) => TypeArgs::Curried(t.map_snd(f)),
            TypeArgs::Record(sel) => TypeArgs::Record(sel.map_snd(f)),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Variant<Id, V> {
    type WrapFst = Variant<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let Variant {
            name,
            span,
            prag,
            args,
        } = self;
        let name = f.apply(name);
        let prag = prag.into_iter().map(|prag| prag.map_fst(f)).collect();
        let args = args.map_fst(f);
        Variant {
            name,
            span,
            prag,
            args,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Variant<Id, V> {
    type WrapSnd = Variant<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let Variant {
            name,
            span,
            prag,
            args,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_snd(f)).collect();
        let args = args.map_snd(f);
        Variant {
            name,
            span,
            prag,
            args,
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for AliasDecl<Id, V> {
    type WrapFst = AliasDecl<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        AliasDecl {
            span: self.span,
            prag: self.prag.into_iter().map(|prag| prag.map_fst(f)).collect(),
            ldef: self.ldef.map_fst(f),
            tipo: self.tipo.map_fst(f),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for AliasDecl<Id, V> {
    type WrapSnd = AliasDecl<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        AliasDecl {
            span: self.span,
            prag: self.prag.into_iter().map(|prag| prag.map_snd(f)).collect(),
            ldef: self.ldef.map_snd(f),
            tipo: self.tipo.map_snd(f),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for NewtypeDecl<Id, V> {
    type WrapFst = NewtypeDecl<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let NewtypeDecl {
            span,
            prag,
            tdef,
            ctor,
            narg,
            with,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_fst(f)).collect();
        let tdef = tdef.map_fst(f);
        let ctor = f.apply(ctor);
        let narg = narg.map_fst(f);
        let with = with.map(|w| w.fmap(f));
        NewtypeDecl {
            span,
            prag,
            tdef,
            ctor,
            narg,
            with,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for NewtypeDecl<Id, V> {
    type WrapSnd = NewtypeDecl<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let NewtypeDecl {
            span,
            prag,
            tdef,
            ctor,
            narg,
            with,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_snd(f)).collect();
        let tdef = tdef.map_snd(f);
        let narg = narg.map_snd(f);
        NewtypeDecl {
            span,
            prag,
            tdef,
            ctor,
            narg,
            with,
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for ClassDecl<Id, V> {
    type WrapFst = ClassDecl<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let ClassDecl {
            span,
            prag,
            cdef,
            pred,
            defs,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_fst(f)).collect();
        let cdef = cdef.map_fst(f);
        let pred = pred.map_fst(f);
        let defs = defs.map_fst(f);
        ClassDecl {
            span,
            prag,
            cdef,
            pred,
            defs,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for ClassDecl<Id, V> {
    type WrapSnd = ClassDecl<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let ClassDecl {
            span,
            prag,
            cdef,
            pred,
            defs,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_snd(f)).collect();
        let cdef = cdef.map_snd(f);
        let pred = pred.map_snd(f);
        let defs = defs.map_snd(f);
        ClassDecl {
            span,
            prag,
            cdef,
            pred,
            defs,
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for InstDecl<Id, V> {
    type WrapFst = InstDecl<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let InstDecl {
            span,
            prag,
            name,
            tipo,
            pred,
            defs,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_fst(f)).collect();
        let name = f.apply(name);
        let tipo = tipo.map_fst(f);
        let pred = pred.map_fst(f);
        let defs = defs.map_fst(f);
        InstDecl {
            span,
            prag,
            name,
            tipo,
            pred,
            defs,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for InstDecl<Id, V> {
    type WrapSnd = InstDecl<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let InstDecl {
            span,
            prag,
            name,
            tipo,
            pred,
            defs,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_snd(f)).collect();
        let tipo = tipo.map_snd(f);
        let pred = pred.map_snd(f);
        let defs = defs.map_snd(f);
        InstDecl {
            span,
            prag,
            name,
            tipo,
            pred,
            defs,
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for MethodImpl<Id, V> {
    type WrapFst = MethodImpl<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let MethodImpl {
            span,
            prag,
            name,
            tsig,
            arms,
        } = self;
        let prag = prag.map_fst(f);
        let name = f.apply(name);
        let tsig = tsig.map_fst(f);
        let arms = arms.map_fst(f);
        MethodImpl {
            span,
            prag,
            name,
            tsig,
            arms,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for MethodImpl<Id, V> {
    type WrapSnd = MethodImpl<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let MethodImpl {
            span,
            prag,
            name,
            tsig,
            arms,
        } = self;
        let prag = prag.map_snd(f);
        let tsig = tsig.map_snd(f);
        let arms = arms.map_snd(f);
        MethodImpl {
            span,
            prag,
            name,
            tsig,
            arms,
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for FnDecl<Id, V> {
    type WrapFst = FnDecl<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let FnDecl {
            span,
            prag,
            name,
            sign,
            defs,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_fst(f)).collect();
        let name = f.apply(name);
        let sign = sign.map_fst(f);
        let defs = defs.map_fst(f);
        FnDecl {
            span,
            prag,
            name,
            sign,
            defs,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for FnDecl<Id, V> {
    type WrapSnd = FnDecl<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let FnDecl {
            span,
            prag,
            name,
            sign,
            defs,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_snd(f)).collect();
        let sign = sign.map_snd(f);
        let defs = defs.map_snd(f);
        FnDecl {
            span,
            prag,
            name,
            sign,
            defs,
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for MethodBody<Id, V> {
    type WrapFst = MethodBody<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            MethodBody::Unimplemented => MethodBody::Unimplemented,
            MethodBody::Default(arms) => MethodBody::Default(arms.map_fst(f)),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for MethodBody<Id, V> {
    type WrapSnd = MethodBody<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            MethodBody::Unimplemented => MethodBody::Unimplemented,
            MethodBody::Default(arms) => MethodBody::Default(arms.map_snd(f)),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for MethodDef<Id, V> {
    type WrapFst = MethodDef<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let MethodDef {
            span,
            prag,
            name,
            annt,
            body,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_fst(f)).collect();
        let name = f.apply(name);
        let annt = annt.map_fst(f);
        let body = body.map_fst(f);
        MethodDef {
            span,
            prag,
            name,
            annt,
            body,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for MethodDef<Id, V> {
    type WrapSnd = MethodDef<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let MethodDef {
            span,
            prag,
            name,
            annt,
            body,
        } = self;
        let prag = prag.into_iter().map(|prag| prag.map_snd(f)).collect();
        let annt = annt.map_snd(f);
        let body = body.map_snd(f);
        MethodDef {
            span,
            prag,
            name,
            annt,
            body,
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Declaration<Id, V> {
    type WrapFst = Declaration<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Declaration::Import(d) => Declaration::Import(d.mapf(f)),
            Declaration::Data(d) => Declaration::Data(d.map_fst(f)),
            Declaration::Alias(d) => Declaration::Alias(d.map_fst(f)),
            Declaration::Fixity(d) => Declaration::Fixity(d.mapf(f)),
            Declaration::Class(d) => Declaration::Class(d.map_fst(f)),
            Declaration::Instance(d) => Declaration::Instance(d.map_fst(f)),
            Declaration::Function(d) => Declaration::Function(d.map_fst(f)),
            Declaration::Newtype(d) => Declaration::Newtype(d.map_fst(f)),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Declaration<Id, V> {
    type WrapSnd = Declaration<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Declaration::Import(d) => Declaration::Import(d),
            Declaration::Data(d) => Declaration::Data(d.map_snd(f)),
            Declaration::Alias(d) => Declaration::Alias(d.map_snd(f)),
            Declaration::Fixity(d) => Declaration::Fixity(d),
            Declaration::Class(d) => Declaration::Class(d.map_snd(f)),
            Declaration::Instance(d) => Declaration::Instance(d.map_snd(f)),
            Declaration::Function(d) => Declaration::Function(d.map_snd(f)),
            Declaration::Newtype(d) => Declaration::Newtype(d.map_snd(f)),
        }
    }
}

// ///////////////////////////

impl<Id, V, X> MapFst<Id, X> for Var<Id, V> {
    type WrapFst = Var<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        Var(f.apply(self.0), self.1)
    }
}

impl<Id, V, X> MapSnd<V, X> for Var<Id, V> {
    type WrapSnd = Var<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        Var(self.0, f.apply(self.1))
    }
}

impl<Id, V, X> MapFst<Id, X> for Con<Id, V> {
    type WrapFst = Con<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Con::List => Con::List,
            Con::Tuple(n) => Con::Tuple(n),
            Con::Arrow => Con::Arrow,
            Con::Named(id) => Con::Named(f.apply(id)),
            Con::Varied(v) => Con::Varied(v),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Con<Id, V> {
    type WrapSnd = Con<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Con::List => Con::List,
            Con::Tuple(n) => Con::Tuple(n),
            Con::Arrow => Con::Arrow,
            Con::Named(id) => Con::Named(id),
            Con::Varied(v) => Con::Varied(f.apply(v)),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Type<Id, V> {
    type WrapFst = Type<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Type::Var(v) => Type::Var(v),
            Type::Con(con, args) => Type::Con(con.map_fst(f), args.map_fst(f)),
            Type::Fun(t1, t2) => {
                let t1 = Box::new(t1.map_fst(f));
                let t2 = Box::new(t2.map_fst(f));
                Type::Fun(t1, t2)
            }
            Type::Tup(ts) => Type::Tup(ts.map_fst(f)),
            Type::Vec(t) => Type::Vec(Box::new(t.map_fst(f))),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Type<Id, V> {
    type WrapSnd = Type<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Type::Var(v) => Type::Var(f.apply(v)),
            Type::Con(con, args) => Type::Con(con.map_snd(f), args.map_snd(f)),
            Type::Fun(t1, t2) => Type::Fun(Box::new(t1.map_snd(f)), Box::new(t2.map_snd(f))),
            Type::Tup(ts) => Type::Tup(ts.map_snd(f)),
            Type::Vec(t) => Type::Vec(Box::new(t.map_snd(f))),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for SimpleType<Id, V> {
    type WrapFst = SimpleType<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        SimpleType(f.apply(self.0), self.1)
    }
}

impl<Id, V, X> MapSnd<V, X> for SimpleType<Id, V> {
    type WrapSnd = SimpleType<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        SimpleType(self.0, Functor::fmap(self.1, f))
    }
}

impl<Id, V, X> MapFst<Id, X> for Predicate<Id, V> {
    type WrapFst = Predicate<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let Predicate { class, head } = self;
        let class = f.apply(class);
        Predicate { class, head }
    }
}

impl<Id, V, X> MapSnd<V, X> for Predicate<Id, V> {
    type WrapSnd = Predicate<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let Predicate { class, head } = self;
        let head = head.mapf(f);
        Predicate { class, head }
    }
}

impl<Id, V, X> MapFst<Id, X> for Qualified<Id, V> {
    type WrapFst = Qualified<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        Qualified {
            pred: self.pred.map_fst(f),
            tipo: self.tipo.map_fst(f),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Qualified<Id, V> {
    type WrapSnd = Qualified<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        Qualified {
            pred: self.pred.map_snd(f),
            tipo: self.tipo.map_snd(f),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Quantified<Id, V> {
    type WrapFst = Quantified<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        Quantified(self.0.map_fst(f))
    }
}

impl<Id, V, X> MapSnd<V, X> for Quantified<Id, V> {
    type WrapSnd = Quantified<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        Quantified(self.0.map_snd(f))
    }
}

impl<Id, V, X> MapFst<Id, X> for Annotation<Id, V> {
    type WrapFst = Annotation<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        Annotation {
            quant: self.quant.map_fst(f),
            qual: self.qual.map_fst(f),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Annotation<Id, V> {
    type WrapSnd = Annotation<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        Annotation {
            quant: self.quant.map_snd(f),
            qual: self.qual.map_snd(f),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Signature<Id, V> {
    type WrapFst = Signature<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Signature::Implicit => Signature::Implicit,
            Signature::Explicit(ann) => Signature::Explicit(ann.map_fst(f)),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Signature<Id, V> {
    type WrapSnd = Signature<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Signature::Implicit => Signature::Implicit,
            Signature::Explicit(ann) => Signature::Explicit(ann.map_snd(f)),
        }
    }
}

// ///////////////////////////

impl<Id, V, X> MapFst<Id, X> for Arm<Id, V> {
    type WrapFst = Arm<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let Arm {
            args,
            cond,
            body,
            wher,
        } = self;
        let args = args.map_fst(f);
        let cond = cond.map_fst(f);
        let body = body.map_fst(f);
        let wher = wher.map_fst(f);
        Arm {
            args,
            cond,
            body,
            wher,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Arm<Id, V> {
    type WrapSnd = Arm<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let Arm {
            args,
            cond,
            body,
            wher,
        } = self;
        let args = args.map_snd(f);
        let cond = cond.map_snd(f);
        let body = body.map_snd(f);
        let wher = wher.map_snd(f);
        Arm {
            args,
            cond,
            body,
            wher,
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Alternative<Id, V> {
    type WrapFst = Alternative<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let Alternative {
            pat,
            cond,
            body,
            wher,
        } = self;
        let pat = pat.map_fst(f);
        let cond = cond.map_fst(f);
        let body = body.map_fst(f);
        let wher = wher.map_fst(f);
        Alternative {
            pat,
            cond,
            body,
            wher,
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Alternative<Id, V> {
    type WrapSnd = Alternative<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let Alternative {
            pat,
            cond,
            body,
            wher,
        } = self;
        let pat = pat.map_snd(f);
        let cond = cond.map_snd(f);
        let body = body.map_snd(f);
        let wher = wher.map_snd(f);
        Alternative {
            pat,
            cond,
            body,
            wher,
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Binding<Id, V> {
    type WrapFst = Binding<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        let Binding { name, tsig, arms } = self;
        let name = f.apply(name);
        let tsig = tsig.map_fst(f);
        let arms = arms.map_fst(f);
        Binding { name, arms, tsig }
    }
}

impl<Id, V, X> MapSnd<V, X> for Binding<Id, V> {
    type WrapSnd = Binding<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        let Binding { name, tsig, arms } = self;
        let tsig = tsig.map_snd(f);
        let arms = arms.map_snd(f);
        Binding { name, arms, tsig }
    }
}

impl<Id, V, X> MapFst<Id, X> for Statement<Id, V> {
    type WrapFst = Statement<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Statement::Generator(pat, ex) => Statement::Generator(pat.map_fst(f), ex.map_fst(f)),
            Statement::Predicate(ex) => Statement::Predicate(ex.map_fst(f)),
            Statement::JustLet(binds) => Statement::JustLet(binds.map_fst(f)),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Statement<Id, V> {
    type WrapSnd = Statement<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Statement::Generator(pat, ex) => Statement::Generator(pat.map_snd(f), ex.map_snd(f)),
            Statement::Predicate(ex) => Statement::Predicate(ex.map_snd(f)),
            Statement::JustLet(binds) => Statement::JustLet(binds.map_snd(f)),
        }
    }
}

// ///////////////////////////

impl<Id, V, X> MapFst<Id, X> for Section<Id, V> {
    type WrapFst = Section<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Section::Prefix { prefix, right } => Section::Prefix {
                prefix: f.apply(prefix),
                right: Box::new(right.map_fst(f)),
            },
            Section::Suffix { left, suffix } => Section::Suffix {
                suffix: f.apply(suffix),
                left: Box::new(left.map_fst(f)),
            },
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Section<Id, V> {
    type WrapSnd = Section<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Section::Prefix { prefix, right } => Section::Prefix {
                prefix,
                right: Box::new(right.map_snd(f)),
            },
            Section::Suffix { left, suffix } => Section::Suffix {
                suffix,
                left: Box::new(left.map_snd(f)),
            },
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Range<Id, V> {
    type WrapFst = Range<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Range::From(x) => Range::From(x.map_fst(f)),
            Range::FromThen([x, y]) => Range::FromThen([x.map_fst(f), y.map_fst(f)]),
            Range::FromTo([x, y]) => Range::FromTo([x.map_fst(f), y.map_fst(f)]),
            Range::FromThenTo([x, y, z]) => {
                Range::FromThenTo([x.map_fst(f), y.map_fst(f), z.map_fst(f)])
            }
        }
    }
}
impl<Id, V, X> MapSnd<V, X> for Range<Id, V> {
    type WrapSnd = Range<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Range::From(x) => Range::From(x.map_snd(f)),
            Range::FromThen([x, y]) => Range::FromThen([x.map_snd(f), y.map_snd(f)]),
            Range::FromTo([x, y]) => Range::FromTo([x.map_snd(f), y.map_snd(f)]),
            Range::FromThenTo([x, y, z]) => {
                Range::FromThenTo([x.map_snd(f), y.map_snd(f), z.map_snd(f)])
            }
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Expression<Id, V> {
    type WrapFst = Expression<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Expression::Ident(id) => Expression::Ident(f.apply(id)),
            Expression::Path(head, tail) => Expression::Path(f.apply(head), Functor::fmap(tail, f)),
            Expression::Lit(lit) => Expression::Lit(lit),
            Expression::Neg(exp) => Expression::Neg(Box::new(exp.map_fst(f))),
            Expression::Infix { infix, left, right } => Expression::Infix {
                infix: f.apply(infix),
                left: Box::new(left.map_fst(f)),
                right: Box::new(right.map_fst(f)),
            },
            Expression::Section(sec) => Expression::Section(sec.map_fst(f)),
            Expression::Tuple(xs) => Expression::Tuple(xs.map_fst(f)),
            Expression::Array(xs) => Expression::Array(xs.map_fst(f)),
            Expression::List(x, stmts) => {
                Expression::List(Box::new(x.map_fst(f)), stmts.map_fst(f))
            }
            Expression::Dict(rec) => Expression::Dict(rec.map_fst(f)),
            Expression::Lambda(pat, body) => {
                Expression::Lambda(pat.map_fst(f), Box::new(body.map_fst(f)))
            }
            Expression::Let(bs, body) => Expression::Let(bs.map_fst(f), Box::new(body.map_fst(f))),
            Expression::App(fun, arg) => {
                Expression::App(Box::new(fun.map_fst(f)), Box::new(arg.map_fst(f)))
            }
            Expression::Cond(xyz) => {
                let [x, y, z] = *xyz;
                let x = x.map_fst(f);
                let y = y.map_fst(f);
                let z = z.map_fst(f);
                Expression::Cond(Box::new([x, y, z]))
            }
            Expression::Case(e, a) => Expression::Case(Box::new(e.map_fst(f)), a.map_fst(f)),
            Expression::Match(a) => Expression::Match(a.map_fst(f)),
            Expression::Cast(e, ty) => Expression::Cast(Box::new(e.map_fst(f)), ty.map_fst(f)),
            Expression::Do(stmts, e) => Expression::Do(stmts.map_fst(f), Box::new(e.map_fst(f))),
            Expression::Range(rng) => Expression::Range(Box::new(rng.map_fst(f))),
            Expression::Group(e) => Expression::Group(Box::new(e.map_fst(f))),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Expression<Id, V> {
    type WrapSnd = Expression<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Expression::Ident(id) => Expression::Ident(id),
            Expression::Path(head, tail) => Expression::Path(head, tail),
            Expression::Lit(lit) => Expression::Lit(lit),
            Expression::Neg(exp) => Expression::Neg(Box::new(exp.map_snd(f))),
            Expression::Infix { infix, left, right } => Expression::Infix {
                infix,
                left: Box::new(left.map_snd(f)),
                right: Box::new(right.map_snd(f)),
            },
            Expression::Section(sec) => Expression::Section(sec.map_snd(f)),
            Expression::Tuple(xs) => Expression::Tuple(xs.map_snd(f)),
            Expression::Array(xs) => Expression::Array(xs.map_snd(f)),
            Expression::List(x, stmts) => {
                Expression::List(Box::new(x.map_snd(f)), stmts.map_snd(f))
            }
            Expression::Dict(rec) => Expression::Dict(rec.map_snd(f)),
            Expression::Lambda(pat, body) => {
                Expression::Lambda(pat.map_snd(f), Box::new(body.map_snd(f)))
            }
            Expression::Let(bs, body) => Expression::Let(bs.map_snd(f), Box::new(body.map_snd(f))),
            Expression::App(fun, arg) => {
                Expression::App(Box::new(fun.map_snd(f)), Box::new(arg.map_snd(f)))
            }
            Expression::Cond(xyz) => {
                let [x, y, z] = *xyz;
                let x = x.map_snd(f);
                let y = y.map_snd(f);
                let z = z.map_snd(f);
                Expression::Cond(Box::new([x, y, z]))
            }
            Expression::Case(e, a) => Expression::Case(Box::new(e.map_snd(f)), a.map_snd(f)),
            Expression::Match(a) => Expression::Match(a.map_snd(f)),
            Expression::Cast(e, ty) => Expression::Cast(Box::new(e.map_snd(f)), ty.map_snd(f)),
            Expression::Do(stmts, e) => Expression::Do(stmts.map_snd(f), Box::new(e.map_snd(f))),
            Expression::Range(rng) => Expression::Range(Box::new(rng.map_snd(f))),
            Expression::Group(e) => Expression::Group(Box::new(e.map_snd(f))),
        }
    }
}

// ////////////////////////////

impl<Id, V, X> MapFst<Id, X> for Pattern<Id, V> {
    type WrapFst = Pattern<X, V>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Pattern::Wild => Pattern::Wild,
            Pattern::Var(id) => Pattern::Var(f.apply(id)),
            Pattern::Lit(lit) => Pattern::Lit(lit),
            Pattern::Neg(pat) => Pattern::Neg(Box::new(pat.map_fst(f))),
            Pattern::Dat(id, args) => Pattern::Dat(f.apply(id), args.map_fst(f)),
            Pattern::Tup(pats) => Pattern::Tup(pats.map_fst(f)),
            Pattern::Vec(pats) => Pattern::Vec(pats.map_fst(f)),
            Pattern::Lnk(head, tail) => {
                let head = head.map_fst(f);
                let tail = tail.map_fst(f);
                Pattern::Lnk(Box::new(head), Box::new(tail))
            }
            Pattern::At(id, pat) => {
                let id = f.apply(id);
                let pat = pat.map_fst(f);
                Pattern::At(id, Box::new(pat))
            }
            Pattern::Or(pats) => Pattern::Or(pats.map_fst(f)),
            Pattern::Rec(rec) => Pattern::Rec(rec.map_fst(f)),
            Pattern::Cast(pat, ty) => Pattern::Cast(Box::new(pat.map_fst(f)), ty.map_fst(f)),
        }
    }
}

impl<Id, V, X> MapSnd<V, X> for Pattern<Id, V> {
    type WrapSnd = Pattern<Id, X>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(V) -> X,
    {
        match self {
            Pattern::Wild => Pattern::Wild,
            Pattern::Var(id) => Pattern::Var(id),
            Pattern::Lit(lit) => Pattern::Lit(lit),
            Pattern::Neg(pat) => Pattern::Neg(Box::new(pat.map_snd(f))),
            Pattern::Dat(id, args) => Pattern::Dat(id, args.map_snd(f)),
            Pattern::Tup(pats) => Pattern::Tup(pats.map_snd(f)),
            Pattern::Vec(pats) => Pattern::Vec(pats.map_snd(f)),
            Pattern::Lnk(head, tail) => {
                let head = head.map_snd(f);
                let tail = tail.map_snd(f);
                Pattern::Lnk(Box::new(head), Box::new(tail))
            }
            Pattern::At(id, pat) => Pattern::At(id, Box::new(pat.map_snd(f))),
            Pattern::Or(pats) => Pattern::Or(pats.map_snd(f)),
            Pattern::Rec(rec) => Pattern::Rec(rec.map_snd(f)),
            Pattern::Cast(pat, ty) => Pattern::Cast(Box::new(pat.map_snd(f)), ty.map_snd(f)),
        }
    }
}

// ////////////////

impl<Id, X, V> MapFst<Id, X> for Record<Id, V>
where
    V: MapFst<Id, X>,
{
    type WrapFst = Record<X, V::WrapFst>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Record::Anon(fields) => Record::Anon(fields.map_fst(f)),
            Record::Data(con, fields) => Record::Data(f.apply(con), fields.map_fst(f)),
        }
    }
}

impl<Id, X, V, T> MapSnd<T, X> for Record<Id, V>
where
    V: MapSnd<T, X>,
{
    type WrapSnd = Record<Id, V::WrapSnd>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(T) -> X,
    {
        match self {
            Record::Anon(fields) => Record::Anon(fields.map_snd(f)),
            Record::Data(con, fields) => Record::Data(con, fields.map_snd(f)),
        }
    }
}

impl<Id, V, X> MapFst<Id, X> for Field<Id, V>
where
    V: MapFst<Id, X>,
{
    type WrapFst = Field<X, V::WrapFst>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(Id) -> X,
    {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(k) => Field::Key(f.apply(k)),
            Field::Entry(k, v) => Field::Entry(f.apply(k), v.map_fst(f)),
        }
    }
}

impl<'a, Id, V, X> MapFst<&'a Id, X> for &'a Field<Id, V>
where
    &'a V: MapFst<&'a Id, X>,
{
    type WrapFst = Field<X, <&'a V as MapFst<&'a Id, X>>::WrapFst>;

    fn map_fst<F>(self, f: &mut Func<'_, F>) -> Self::WrapFst
    where
        F: FnMut(&'a Id) -> X,
    {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(id) => Field::Key(f.apply(id)),
            Field::Entry(id, val) => Field::Entry(f.apply(id), val.map_fst(f)),
        }
    }
}

impl<Id, V, X, T> MapSnd<T, X> for Field<Id, V>
where
    V: MapSnd<T, X>,
{
    type WrapSnd = Field<Id, V::WrapSnd>;

    fn map_snd<F>(self, f: &mut Func<'_, F>) -> Self::WrapSnd
    where
        F: FnMut(T) -> X,
    {
        match self {
            Field::Rest => Field::Rest,
            Field::Key(id) => Field::Key(id),
            Field::Entry(id, v) => Field::Entry(id, v.map_snd(f)),
        }
    }
}
