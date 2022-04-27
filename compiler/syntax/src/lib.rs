use wy_common::{text, Map};
use wy_intern::symbol::Symbol;
use wy_lexer::Literal;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Name {
    Upper(Symbol),
    Lower(Symbol),
    Infix(Symbol),
}

impl Name {
    pub fn get_symbol(&self) -> Symbol {
        match self {
            Self::Upper(s) | Self::Lower(s) | Self::Infix(s) => *s,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program<Id> {
    pub modules: Vec<Module<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module<Id = Name> {
    pub modname: Id,
    pub datatys: Vec<DataDecl>,
    pub classes: Vec<ClassDecl>,
    pub implems: Vec<InstDecl>,
    pub fundefs: Vec<FnDecl>,
    pub infixes: Vec<FixityDecl>,
    pub aliases: Vec<AliasDecl>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportDecl<Id = Name> {
    pub name: Id,
    pub rename: Option<Id>,
    pub hidden: bool,
    pub imports: Vec<Import<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Import<Id = Name> {
    Function(Id),
    /// Type imports: type only, no type constructors
    Abstract(Id),
    /// Data type imports that include *all* of their constructors
    Total(Id),
    /// Data type imports that include only the specified constructors
    Partial(Id, Vec<Id>),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Prec(pub u8);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Assoc {
    Left,
    Right,
    None,
}

impl Assoc {
    pub fn is_left(&self) -> bool {
        matches!(self, Self::Left)
    }
    pub fn is_right(&self) -> bool {
        matches!(self, Self::Right)
    }
    pub fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Fixity {
    pub assoc: Assoc,
    pub prec: Prec,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixityDecl<Id = Name> {
    pub infixes: Vec<Id>,
    pub fixity: Fixity,
}

impl<Id> FixityDecl<Id> {
    pub fn new(assoc: Assoc, prec: Prec, infixes: Vec<Id>) -> Self {
        Self {
            infixes,
            fixity: Fixity { assoc, prec },
        }
    }
}

#[derive(Clone, Debug)]
pub struct FixityTable<Id = Name>(pub Map<Id, Fixity>);

impl From<&[FixityDecl]> for FixityTable {
    fn from(fixity_decls: &[FixityDecl]) -> Self {
        Self(
            fixity_decls
                .iter()
                .flat_map(|FixityDecl { infixes, fixity }| {
                    infixes.iter().map(|infix| (*infix, *fixity))
                })
                .collect(),
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DataDecl<Id = Name> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub ctxt: Vec<Context<Id>>,
    pub vnts: Vec<Variant<Id>>,
    pub with: Vec<Id>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variant<Id = Name> {
    pub name: Id,
    pub args: Vec<Type<Id>>,
    pub tag: Tag,
    pub arity: Arity,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Tag(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Arity(pub usize);

impl Arity {
    pub fn from_len<T>(ts: &[T]) -> Self {
        Self(ts.len())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AliasDecl<Id = Name> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub sign: Signature<Id>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NewtypeDecl<Id = Name> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub ctor: Id,
    pub tipo: Type<Id>,
    pub with: Vec<Id>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Tv(pub u32);

impl Tv {
    pub fn incr(&self) -> Self {
        Self(self.0 + 1)
    }

    pub fn display(&self) -> String {
        text::display_var(self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<Id = Name> {
    Var(Tv),
    Con(Id, Vec<Type<Id>>),
    Fun(Box<Type<Id>>, Box<Type<Id>>),
    Tup(Vec<Type<Id>>),
    Vec(Vec<Type<Id>>),
    Rec(Record<Type<Id>, Id>),
}

impl<Id> Type<Id> {
    pub const UNIT: Self = Self::Tup(vec![]);
    pub const NIL: Self = Self::Vec(vec![]);
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Record<T, Id = Name> {
    Anon(Vec<Field<T, Id>>),
    Data(Id, Vec<Field<T, Id>>),
}

impl<T, Id> Record<T, Id> {
    pub const VOID: Self = Self::Anon(vec![]);
    pub fn len(&self) -> usize {
        match self {
            Record::Anon(es) | Record::Data(_, es) => es.len(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Field<T, Id = Name> {
    Rest,
    Key(Id),
    Entry(Id, T),
}

impl<T, Id> Field<T, Id> {
    pub fn is_rest(&self) -> bool {
        matches!(self, Self::Rest)
    }
    pub fn key_only(&self) -> bool {
        matches!(self, Self::Key(..))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context<Id = Name> {
    pub class: Id,
    pub pram: Tv,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassDecl<Id = Name> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub ctxt: Vec<Context<Id>>,
    pub defs: Vec<Method<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstDecl<Id = Name> {
    pub name: Id,
    pub tipo: Type<Id>,
    pub ctxt: Vec<Context<Id>>,
    pub defs: Vec<Binding<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnDecl<Id = Name> {
    pub defs: Binding<Id>,
    pub sign: Option<Signature<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature<Id = Name> {
    pub ctxt: Vec<Context<Id>>,
    pub tipo: Type<Id>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Method<Id = Name> {
    Sig(Id, Signature<Id>),
    Impl(Binding<Id>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding<Id = Name> {
    pub name: Id,
    pub arms: Vec<Match<Id>>,
    pub tipo: Option<Signature<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Match<Id = Name> {
    pub args: Vec<Pattern<Id>>,
    pub pred: Option<Expression<Id>>,
    pub body: Expression<Id>,
    pub wher: Vec<Binding<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alternative<Id = Name> {
    pub pat: Pattern<Id>,
    pub pred: Option<Expression<Id>>,
    pub body: Expression<Id>,
    pub wher: Vec<Binding<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Declaration<Id = Name> {
    Data(DataDecl<Id>),
    Alias(AliasDecl<Id>),
    Fixity(FixityDecl<Id>),
    Class(ClassDecl<Id>),
    Instance(InstDecl<Id>),
    Function(FnDecl<Id>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expression<Id = Name> {
    Ident(Id),
    Lit(Literal),
    Neg(Box<Expression<Id>>),
    Infix {
        infix: Id,
        left: Box<[Expression<Id>; 2]>,
    },
    Tuple(Vec<Expression<Id>>),
    Array(Vec<Expression<Id>>),
    List(Box<Expression<Id>>, Vec<Statement<Id>>),
    Dict(Record<Expression<Id>, Id>),
    Lambda(Pattern<Id>, Box<Expression<Id>>),
    Let(Binding<Id>, Box<Expression<Id>>),
    App(Box<Expression<Id>>, Box<Expression<Id>>),
    Cond(Box<[Expression<Id>; 3]>),
    Case(Box<Expression<Id>>, Vec<Alternative<Id>>),
    Cast(Box<Expression<Id>>, Type<Id>),
    Do(Vec<Statement<Id>>, Box<Expression<Id>>),
    Range(Box<Expression<Id>>, Option<Box<Expression<Id>>>),
    Group(Box<Expression<Id>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement<Id = Name> {
    // <PAT> <- <EXPR>
    Generator(Pattern<Id>, Expression<Id>),
    // <EXPR>
    Predicate(Expression<Id>),
    // let (<ID> <PAT>* = <EXPR>)+
    DoLet(Vec<Binding<Id>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern<Id = Name> {
    Wild,
    Var(Id),
    Lit(Literal),
    Con(Id, Vec<Pattern<Id>>),
    Tup(Vec<Pattern<Id>>),
    Lst(Vec<Pattern<Id>>),
    At(Id, Box<Pattern<Id>>),
    Or(Vec<Pattern<Id>>),
    Rec(Record<Pattern<Id>, Id>),
    Cast(Box<Pattern<Id>>, Type<Id>),
}

impl<Id> Pattern<Id> {
    pub const UNIT: Self = Self::Tup(vec![]);
    pub const NIL: Self = Self::Lst(vec![]);
    pub const VOID: Self = Self::Rec(Record::VOID);
}
