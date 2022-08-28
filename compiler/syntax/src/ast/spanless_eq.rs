use std::path::PathBuf;

use wy_common::functor::{Func, MapFst, MapSnd, Wrap1, Wrap2};
use wy_failure::{diff::diff_assert_eq, SrcPath};
use wy_lexer::{Lexeme, Token};
use wy_name::Chain;
use wy_span::Spanned;

use crate::{
    attr::{Attribute, DocLine, Pragma},
    decl::{
        AliasDecl, ClassDecl, DataDecl, FixityDecl, FnDecl, InstDecl, MethodBody, MethodDef,
        MethodImpl, NewtypeDecl, Selector, TypeArg, TypeArgs, Variant, WithClause,
    },
    expr::{Expression, Range, Section},
    module::{Import, ImportSpec, Module},
    pattern::Pattern,
    record::{Field, Record},
    stmt::{Alternative, Arm, Binding, LocalDef, Statement},
    tipo::{
        Annotation, Con, Parameter, Predicate, Qualified, Quantified, Signature, SimpleType, Type,
        Var,
    },
};

/// Generic function over any type with two type parameters wrapped in
/// `Span`s that implement `MapFst` and `MapSnd`, mapping the
/// parameters `Spanned<A>` to `A` and `Spanned<B>` to `B`.
pub fn de_span2<A, B, X>(x: X) -> Wrap2<Wrap1<X, Spanned<A>, A>, Spanned<B>, B>
where
    X: MapFst<Spanned<A>, A> + MapSnd<Spanned<B>, B>,
    Wrap1<X, Spanned<A>, A>: MapSnd<Spanned<B>, B>,
{
    x.map_fst(&mut Func::New(Spanned::take_item))
        .map_snd(&mut Func::New(Spanned::take_item))
}

///! This module provides functionality for comparing AST nodes
///! without regards to their spans. This is necessary for checking
///! whether AST nodes are identical regardless as to from where in the
///! source code they may have been parsed, such as when testing
///! parser output, comparing (parser-generated) sugared/desugared
///! AST-nodes or implement structural node sharing.
///!
///!
///! Included in this module is the `SpanlessEq` trait along with
///! implementations for all AST nodes, as well as some common types
///! and wrappers, (such as `Vec`, `Box`, `Option`, fix-sized arrays, etc.),
///! as well as the type `Spanless<T>`, which is a wrapper around a
///! type `T: SpanlessEq` with an implementation of `PartialEq` that
///! calls `SpanlessEq::spanless_eq`.

/// Simple wrapper around some type `T: SpanlessEq` for which
pub struct Spanless<T: SpanlessEq>(pub T);

impl<T: SpanlessEq + std::fmt::Debug> std::fmt::Debug for Spanless<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        T::fmt(&self.0, f)
    }
}
impl<T: SpanlessEq + std::fmt::Display> std::fmt::Display for Spanless<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        T::fmt(&self.0, f)
    }
}

impl<T: SpanlessEq> Spanless<T> {
    pub fn assert_eq(self, other: T)
    where
        T: std::fmt::Debug,
    {
        diff_assert_eq!(self, other)
    }
}

impl<T> PartialEq for Spanless<T>
where
    T: SpanlessEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0.spanless_eq(&other.0)
    }
}

impl<T> PartialEq<T> for Spanless<T>
where
    T: SpanlessEq,
{
    fn eq(&self, other: &T) -> bool {
        self.0.spanless_eq(other)
    }
}

impl<T> PartialEq<&T> for Spanless<T>
where
    T: SpanlessEq,
{
    fn eq(&self, other: &&T) -> bool {
        self.0.spanless_eq(*other)
    }
}

/// Public interface allowing for comparison of types without regard
/// for their spans.
///
/// An example of this is when comparing two `Expression` nodes, both
/// parametrized by `Spanned`-wrapped types, i.e., comparing two nodes of
/// type `Expression<Spanned<Id>, Spanned<T>>` for some types `Id: PartialEq`,
/// `T: PartialEq`.
///
/// Another use case lies in the desugaring one can apply when it
/// comes to class predicates. For example, it is possible to
/// implement syntactic sugar such that
/// ```wysk
///     |A {a, b, c}|
/// ```
/// generates the same type predicate information as
/// ```wysk
///     |A a, A b, A c|
/// ```
/// and only differ based on `Span` data.
///
/// Many base implementations for wrappers around `Spanned<X>` for
/// some `X: PartialEq` rely on the `Spanned::item_eq` method, but
/// this may be overwritten.
pub trait SpanlessEq: PartialEq {
    fn spanless_eq(&self, other: &Self) -> bool;
}

/// Shortcut to allow applying spanless equality comparisons on tuples
/// without relying on new closures.
#[inline]
fn spanless_eq_pair<X: SpanlessEq>((left, right): (&X, &X)) -> bool {
    left.spanless_eq(right)
}

impl<X> SpanlessEq for Spanned<X>
where
    X: PartialEq,
{
    #[inline]
    fn spanless_eq(&self, other: &Self) -> bool {
        self.item_eq(other)
    }
}

impl<X> SpanlessEq for Vec<X>
where
    X: SpanlessEq,
{
    #[inline]
    fn spanless_eq(&self, other: &Self) -> bool {
        self.len() == other.len()
            && self
                .into_iter()
                .zip(other.into_iter())
                // .all(|(this, that)| this.spanless_eq(that))
                .all(spanless_eq_pair)
    }
}

impl<X> SpanlessEq for Option<X>
where
    X: SpanlessEq,
{
    #[inline]
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (None, None) => true,
            (Some(this), Some(that)) => this.spanless_eq(that),
            _ => false,
        }
    }
}

impl<X> SpanlessEq for Box<X>
where
    X: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.as_ref().spanless_eq(&other.as_ref())
    }
}

impl<X, E> SpanlessEq for Result<X, E>
where
    X: SpanlessEq,
    E: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Ok(this), Ok(that)) => this.spanless_eq(that),
            (Err(this), Err(that)) => this.spanless_eq(that),
            _ => false,
        }
    }
}

impl<X, Y> SpanlessEq for (X, Y)
where
    X: SpanlessEq,
    Y: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.0.spanless_eq(&other.0) && self.1.spanless_eq(&other.1)
    }
}

impl<X, Y, Z> SpanlessEq for (X, Y, Z)
where
    X: SpanlessEq,
    Y: SpanlessEq,
    Z: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.0.spanless_eq(&other.0) && self.1.spanless_eq(&other.1) && self.2.spanless_eq(&other.2)
    }
}

impl<X, Y, Z, U> SpanlessEq for (X, Y, Z, U)
where
    X: SpanlessEq,
    Y: SpanlessEq,
    Z: SpanlessEq,
    U: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.0.spanless_eq(&other.0)
            && self.1.spanless_eq(&other.1)
            && self.2.spanless_eq(&other.2)
            && self.3.spanless_eq(&other.3)
    }
}

impl<X, const N: usize> SpanlessEq for [X; N]
where
    X: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.into_iter()
            .zip(other.into_iter())
            .all(spanless_eq_pair)
    }
}

impl<X> SpanlessEq for Chain<X>
where
    X: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(spanless_eq_pair)
    }
}

impl SpanlessEq for Lexeme {
    #[inline]
    fn spanless_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }
}

impl<X> SpanlessEq for Token<X>
where
    X: SpanlessEq,
{
    #[inline]
    fn spanless_eq(&self, other: &Self) -> bool {
        self.lexeme.eq(&other.lexeme)
    }
}

impl SpanlessEq for PathBuf {
    #[inline]
    fn spanless_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }
}

impl SpanlessEq for SrcPath {
    #[inline]
    fn spanless_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }
}

impl<Id, T, P> SpanlessEq for Module<Id, T, P>
where
    Id: SpanlessEq,
    T: SpanlessEq,
    P: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        // let Module {
        //     srcpath, modname,
        //     imports, infixes,
        //     datatys, classes,
        //     implems, fundefs,
        //     aliases, newtyps,
        //     pragmas
        // } = self;
        self.modname.spanless_eq(&other.modname)
            && self.srcpath.eq(&other.srcpath)
            && self.imports.spanless_eq(&other.imports)
            && self.infixes.spanless_eq(&other.infixes)
            && self.datatys.spanless_eq(&other.datatys)
            && self.classes.spanless_eq(&other.classes)
            && self.implems.spanless_eq(&other.implems)
            && self.fundefs.spanless_eq(&other.fundefs)
            && self.aliases.spanless_eq(&other.aliases)
            && self.newtyps.spanless_eq(&other.newtyps)
            && self.pragmas.spanless_eq(&other.pragmas)
    }
}

impl<Id, T> SpanlessEq for Pragma<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.plmt.eq(&other.plmt) && self.attr.spanless_eq(&other.attr)
    }
}

impl<Id, T> SpanlessEq for Attribute<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Attribute::Test, Attribute::Test)
            | (Attribute::Todo, Attribute::Todo)
            | (Attribute::Inline, Attribute::Inline)
            | (Attribute::NoInline, Attribute::NoInline) => true,
            (Attribute::Doc(this), Attribute::Doc(that)) => this.spanless_eq(that),
            (Attribute::Fixity(this), Attribute::Fixity(that)) => this == that,
            (Attribute::Derive(this), Attribute::Derive(that)) => this.spanless_eq(that),
            (Attribute::Specialize(these), Attribute::Specialize(those)) => {
                these.spanless_eq(those)
            }
            (Attribute::Custom(this, these), Attribute::Custom(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            _ => false,
        }
    }
}

impl SpanlessEq for DocLine {
    fn spanless_eq(&self, other: &Self) -> bool {
        self.id == other.id && self.line_kind == other.line_kind
    }
}

impl<Id> SpanlessEq for FixityDecl<Id>
where
    Id: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.fixity == other.fixity
            && self.from_pragma == other.from_pragma
            && self.infixes.spanless_eq(&other.infixes)
    }
}

impl<Id> SpanlessEq for ImportSpec<Id>
where
    Id: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.name.spanless_eq(&other.name)
            && self.hidden == other.hidden
            && self.qualified == other.qualified
            && self.rename.spanless_eq(&other.rename)
            && self.imports.spanless_eq(&other.imports)
    }
}

impl<Id> SpanlessEq for Import<Id>
where
    Id: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Import::Operator(this), Import::Operator(that))
            | (Import::Function(this), Import::Function(that))
            | (Import::Abstract(this), Import::Abstract(that))
            | (Import::Total(this), Import::Total(that)) => this.spanless_eq(that),
            (Import::Partial(this, these), Import::Partial(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            _ => false,
        }
    }
}

impl<Id, T> SpanlessEq for DataDecl<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.prag.spanless_eq(&other.prag)
            && self.pred.spanless_eq(&other.pred)
            && self.tdef.spanless_eq(&other.tdef)
            && self.vnts.spanless_eq(&other.vnts)
            && self.with.spanless_eq(&other.with)
    }
}

impl<Id, T> SpanlessEq for SimpleType<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.0.spanless_eq(&other.0) && self.1.spanless_eq(&other.1)
    }
}

impl<Id, T> SpanlessEq for Variant<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.name.spanless_eq(&other.name)
            && self.prag.spanless_eq(&other.prag)
            && self.args.spanless_eq(&other.args)
    }
}

impl<Id, T> SpanlessEq for TypeArgs<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TypeArgs::Curried(this), TypeArgs::Curried(that)) => this.spanless_eq(that),
            (TypeArgs::Record(this), TypeArgs::Record(that)) => this.spanless_eq(that),
            _ => false,
        }
    }
}

impl<Id, T> SpanlessEq for Selector<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.name.spanless_eq(&other.name) && self.tipo.spanless_eq(&other.tipo)
    }
}

impl<Id> SpanlessEq for WithClause<Id>
where
    Id: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.names.len() == other.names.len()
            && self
                .names_iter()
                .zip(other.names_iter())
                .all(|(mine, theirs)| mine == theirs)
    }
}

impl<Id, T> SpanlessEq for NewtypeDecl<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        // let NewtypeDecl {
        //     span, prag,
        //     tdef, ctor,
        //     narg, with
        // } = self;
        self.prag.spanless_eq(&other.prag)
            && self.tdef.spanless_eq(&other.tdef)
            && self.ctor.spanless_eq(&other.ctor)
            && self.narg.spanless_eq(&other.narg)
            && self.with.spanless_eq(&other.with)
    }
}

impl<Id, V, T, S> SpanlessEq for TypeArg<Id, V, T, S>
where
    Id: SpanlessEq,
    V: SpanlessEq,
    T: SpanlessEq,
    S: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TypeArg::Empty(_), TypeArg::Empty(_)) => true,
            (TypeArg::Type(this), TypeArg::Type(that)) => this.spanless_eq(that),
            (TypeArg::Selector(this), TypeArg::Selector(that)) => this.spanless_eq(that),
            _ => false,
        }
    }
}

impl<Id, T> SpanlessEq for AliasDecl<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.prag.spanless_eq(&other.prag)
            && self.ldef.spanless_eq(&other.ldef)
            && self.tipo.spanless_eq(&other.tipo)
    }
}

impl<Id, T> SpanlessEq for ClassDecl<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.prag.spanless_eq(&other.prag)
            && self.cdef.spanless_eq(&other.cdef)
            && self.pred.spanless_eq(&other.pred)
            && self.defs.spanless_eq(&other.defs)
    }
}

impl<Id, T> SpanlessEq for MethodDef<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.name.spanless_eq(&other.name)
            && self.prag.spanless_eq(&other.prag)
            && self.annt.spanless_eq(&other.annt)
            && self.body.spanless_eq(&other.body)
    }
}

impl<Id, T> SpanlessEq for MethodBody<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (MethodBody::Unimplemented, MethodBody::Unimplemented) => true,
            // should this be false??
            (MethodBody::Unimplemented, MethodBody::Default(ts))
            | (MethodBody::Default(ts), MethodBody::Unimplemented)
                if ts.is_empty() =>
            {
                true
            }
            (MethodBody::Default(this), MethodBody::Default(that)) => this.spanless_eq(that),
            _ => false,
        }
    }
}

impl<Id, T> SpanlessEq for InstDecl<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.name.spanless_eq(&other.name)
            && self.prag.spanless_eq(&other.prag)
            && self.pred.spanless_eq(&other.pred)
            && self.tipo.spanless_eq(&other.tipo)
            && self.defs.spanless_eq(&other.defs)
    }
}

impl<Id, T> SpanlessEq for MethodImpl<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.name.spanless_eq(&other.name)
            && self.prag.spanless_eq(&other.prag)
            && self.tsig.spanless_eq(&other.tsig)
            && self.arms.spanless_eq(&other.arms)
    }
}

impl<Id, T> SpanlessEq for FnDecl<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.name.spanless_eq(&other.name)
            && self.prag.spanless_eq(&other.prag)
            && self.sign.spanless_eq(&other.sign)
            && self.defs.spanless_eq(&other.defs)
    }
}

impl<Id, T> SpanlessEq for Expression<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Expression::Ident(this), Expression::Ident(that)) => this.spanless_eq(that),
            (Expression::Path(this, these), Expression::Path(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            (Expression::Lit(this), Expression::Lit(that)) => this == that,
            (Expression::Neg(this), Expression::Neg(that)) => this.spanless_eq(that),
            (Expression::Group(this), Expression::Group(that)) => this.spanless_eq(that),
            (
                Expression::Infix {
                    infix: this_infix,
                    left: this_left,
                    right: this_right,
                },
                Expression::Infix {
                    infix: that_infix,
                    left: that_left,
                    right: that_right,
                },
            ) => {
                this_infix.spanless_eq(that_infix)
                    && this_left.spanless_eq(that_left)
                    && this_right.spanless_eq(that_right)
            }
            (Expression::Section(this), Expression::Section(that)) => this.spanless_eq(that),
            (Expression::Tuple(this), Expression::Tuple(that)) => this.spanless_eq(that),
            (Expression::Array(this), Expression::Array(that)) => this.spanless_eq(that),
            (Expression::List(this, these), Expression::List(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            (Expression::Dict(this), Expression::Dict(that)) => this.spanless_eq(that),
            (Expression::Lambda(this, these), Expression::Lambda(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            (Expression::Let(this, these), Expression::Let(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            (Expression::App(this, these), Expression::App(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            (Expression::Cond(this), Expression::Cond(that)) => this.spanless_eq(that),
            (Expression::Case(this, these), Expression::Case(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            (Expression::Match(these), Expression::Match(those)) => these.spanless_eq(those),
            (Expression::Cast(this, these), Expression::Cast(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            (Expression::Do(this, these), Expression::Do(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            (Expression::Range(this), Expression::Range(that)) => this.spanless_eq(that),
            _ => false,
        }
    }
}

impl<Id, T> SpanlessEq for Section<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Section::Prefix {
                    prefix: this_affix,
                    right: this_expr,
                },
                Section::Prefix {
                    prefix: that_affix,
                    right: that_expr,
                },
            )
            | (
                Section::Suffix {
                    left: this_expr,
                    suffix: this_affix,
                },
                Section::Suffix {
                    left: that_expr,
                    suffix: that_affix,
                },
            ) => this_affix.spanless_eq(that_affix) && this_expr.spanless_eq(that_expr),
            _ => false,
        }
    }
}

impl<Id, T> SpanlessEq for Range<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Range::From(this), Range::From(that)) => this.spanless_eq(that),

            (Range::FromThen(this), Range::FromThen(that)) => this.spanless_eq(that),

            (Range::FromTo(this), Range::FromTo(that)) => this.spanless_eq(that),

            (Range::FromThenTo(this), Range::FromThenTo(that)) => this.spanless_eq(that),
            _ => false,
        }
    }
}

impl<Id, T> SpanlessEq for Pattern<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Pattern::Wild, Pattern::Wild) => true,
            (Pattern::Lit(this), Pattern::Lit(that)) => this == that,
            (Pattern::Var(this), Pattern::Var(that)) => this.spanless_eq(that),
            (Pattern::Neg(this), Pattern::Neg(that)) => this.spanless_eq(that),
            (Pattern::Dat(this, these), Pattern::Dat(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            (Pattern::Tup(this), Pattern::Tup(that)) => this.spanless_eq(that),
            (Pattern::Vec(this), Pattern::Vec(that)) => this.spanless_eq(that),
            (Pattern::Lnk(this, these), Pattern::Lnk(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            (Pattern::At(this, these), Pattern::At(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            (Pattern::Or(this), Pattern::Or(that)) => this.spanless_eq(that),
            (Pattern::Rec(this), Pattern::Rec(that)) => this.spanless_eq(that),
            (Pattern::Cast(this, these), Pattern::Cast(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            _ => false,
        }
    }
}

impl<Id, T> SpanlessEq for Binding<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.name.spanless_eq(&other.name)
            && self.tsig.spanless_eq(&other.tsig)
            && self.arms.spanless_eq(&other.arms)
    }
}

impl<Id, T> SpanlessEq for Arm<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.args.spanless_eq(&other.args)
            && self.cond.spanless_eq(&other.cond)
            && self.body.spanless_eq(&other.body)
            && self.wher.spanless_eq(&other.wher)
    }
}

impl<Id, T> SpanlessEq for Alternative<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.pat.spanless_eq(&other.pat)
            && self.cond.spanless_eq(&other.cond)
            && self.body.spanless_eq(&other.body)
            && self.wher.spanless_eq(&other.wher)
    }
}

impl<Id, T> SpanlessEq for Statement<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Statement::Generator(this_pat, this_expr),
                Statement::Generator(that_pat, that_expr),
            ) => this_pat.spanless_eq(that_pat) && this_expr.spanless_eq(that_expr),
            (Statement::Predicate(this), Statement::Predicate(that)) => this.spanless_eq(that),
            (Statement::JustLet(these), Statement::JustLet(those)) => these.spanless_eq(those),
            _ => false,
        }
    }
}

impl<Id, T> SpanlessEq for LocalDef<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (LocalDef::Binder(this), LocalDef::Binder(that)) => this.spanless_eq(that),
            (LocalDef::Match(this), LocalDef::Match(that)) => this.spanless_eq(that),
            _ => false,
        }
    }
}

// What about Symbol::COMMA_<N> vs Con::Tuple(N + 1)
impl<Id, T> SpanlessEq for Con<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Con::List, Con::List) | (Con::Arrow, Con::Arrow) => true,
            (Con::Tuple(a), Con::Tuple(b)) => a == b,
            (Con::Named(a), Con::Named(b)) => a.spanless_eq(b),
            (Con::Varied(a), Con::Varied(b)) => a.spanless_eq(b),
            _ => false,
        }
    }
}

// what about Con((->), [a0, .., an]) vs a0 -> ... -> an ??
impl<Id, T> SpanlessEq for Type<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Var(this), Type::Var(that)) => this.spanless_eq(that),
            (Type::Con(this_con, these_args), Type::Con(that_con, those_args)) => {
                this_con.spanless_eq(that_con) && these_args.spanless_eq(those_args)
            }
            (Type::Fun(this_x, this_y), Type::Fun(that_x, that_y)) => {
                this_x.as_ref().spanless_eq(that_x.as_ref())
                    && this_y.as_ref().spanless_eq(that_y.as_ref())
            }
            (Type::Tup(these), Type::Tup(those)) => these.spanless_eq(those),
            (Type::Vec(this), Type::Vec(that)) => this.as_ref().spanless_eq(that.as_ref()),
            _ => false,
        }
    }
}

impl<Id, T> SpanlessEq for Signature<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Signature::Implicit, Signature::Implicit) => true,
            (Signature::Explicit(this), Signature::Explicit(that)) => this.spanless_eq(that),
            _ => false,
        }
    }
}

impl<Id, T> SpanlessEq for Annotation<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.qual.spanless_eq(&other.qual) && self.quant.spanless_eq(&other.quant)
    }
}

impl<Id, T> SpanlessEq for Quantified<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.0.spanless_eq(&other.0)
    }
}

impl<Id, T> SpanlessEq for Var<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.0.spanless_eq(&other.0) && self.1.spanless_eq(&other.1)
    }
}

impl<Id, T> SpanlessEq for Qualified<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.pred.spanless_eq(&other.pred) && self.tipo.spanless_eq(&other.tipo)
    }
}

impl<Id, T> SpanlessEq for Predicate<Id, T>
where
    Id: SpanlessEq,
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.class.spanless_eq(&other.class) && self.head.spanless_eq(&other.head)
    }
}

impl<T> SpanlessEq for Parameter<T>
where
    T: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        self.0.spanless_eq(&other.0) && self.1.spanless_eq(&other.1)
    }
}

impl<Id, X> SpanlessEq for Record<Id, X>
where
    Id: SpanlessEq,
    X: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Record::Anon(this), Record::Anon(that)) => this.spanless_eq(that),
            (Record::Data(this, these), Record::Data(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            _ => false,
        }
    }
}

impl<Id, X> SpanlessEq for Field<Id, X>
where
    Id: SpanlessEq,
    X: SpanlessEq,
{
    fn spanless_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Field::Rest, Field::Rest) => true,
            (Field::Key(this), Field::Key(that)) => this.spanless_eq(that),
            (Field::Entry(this, these), Field::Entry(that, those)) => {
                this.spanless_eq(that) && these.spanless_eq(those)
            }
            _ => false,
        }
    }
}
