pub mod fixity;
pub mod tipo;
pub mod visit;

use std::rc::Rc;

use tipo::*;
use wy_common::{text, Map};
use wy_intern::symbol::Symbol;
use wy_lexer::Literal;

use fixity::*;

// TODO: documentation; potential split-up of definitions into separate files?

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Ident {
    Upper(Symbol),
    Lower(Symbol),
    Infix(Symbol),
}

impl std::fmt::Debug for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Upper(arg0) => write!(f, "Upper({})", arg0),
            Self::Lower(arg0) => write!(f, "Lower({})", arg0),
            Self::Infix(arg0) => write!(f, "Infix({})", arg0),
        }
    }
}

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.get_symbol())
    }
}

impl Ident {
    pub fn get_symbol(&self) -> Symbol {
        match self {
            Self::Upper(s) | Self::Lower(s) | Self::Infix(s) => *s,
        }
    }
    pub fn is_upper(&self) -> bool {
        matches!(self, Self::Upper(..))
    }
    pub fn is_lower(&self) -> bool {
        matches!(self, Self::Lower(..))
    }
    pub fn is_infix(&self) -> bool {
        matches!(self, Self::Infix(..))
    }

    pub fn minus_sign() -> Self {
        Self::Infix(wy_intern::intern_once("-"))
    }
}

wy_common::newtype!({ u64 in Uid | Show (+= usize |rhs| rhs as u64) });

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program<Id = Ident> {
    pub modules: Vec<Module<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module<Id = Ident> {
    pub modname: Id,
    pub imports: Vec<ImportDecl<Id>>,
    pub datatys: Vec<DataDecl<Id>>,
    pub classes: Vec<ClassDecl<Id>>,
    pub implems: Vec<InstDecl<Id>>,
    pub fundefs: Vec<FnDecl<Id>>,
    pub infixes: Vec<FixityDecl<Id>>,
    pub aliases: Vec<AliasDecl<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportDecl<Id = Ident> {
    pub name: Id,
    pub rename: Option<Id>,
    pub hidden: bool,
    pub imports: Vec<Import<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Import<Id = Ident> {
    Function(Id),
    /// Type imports: type only, no type constructors
    Abstract(Id),
    /// Data type imports that include *all* of their constructors
    Total(Id),
    /// Data type imports that include only the specified constructors
    Partial(Id, Vec<Id>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixityDecl<Id = Ident> {
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

impl<Id: Copy + Eq + std::hash::Hash> From<&[FixityDecl<Id>]>
    for FixityTable<Id>
{
    fn from(fixity_decls: &[FixityDecl<Id>]) -> Self {
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
pub struct DataDecl<Id = Ident> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub ctxt: Vec<Context<Id>>,
    pub vnts: Vec<Variant<Id>>,
    pub with: Vec<Id>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variant<Id = Ident> {
    pub name: Id,
    pub args: Vec<Type<Id>>,
    // pub tag: Tag,
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
pub struct AliasDecl<Id = Ident> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub sign: Signature<Id>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NewtypeDecl<Id = Ident> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub ctor: Id,
    pub tipo: Type<Id>,
    pub with: Vec<Id>,
}

/// A `Context` always appears as an element in a sequence of other `Context`s
/// preceding a `=>` and a type signature, and encodes what *type constraints* a
/// given *type variable* must adhere to in the following type signature.
///
/// For example, the following type signature contains *two* `Context`s
/// corresponding to two type variables `a` and `b`, where, for some given
/// typeclasses `A` and `B`, `a` is constrained (= required to be a member of)
/// the typeclass `A`, and `b` is constrained to `B`.
/// ```wysk
/// ~~> Context 1
/// ~~|  vvv
///     |A a, B b| => (a, b)
/// ~~:       ^^^  
/// ~~:  Context 2
/// ~~: ^--------^
/// ~~: Context 1 and Context 2, surrounded by `|` and followed by `=>`
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context<Id = Ident, T = Tv> {
    pub class: Id,
    /// Defaults to `Tv`, but is parametrized in order to allow for simple
    /// (lowercase) identifiers to be used during parsing (which should then be
    /// *normalized* once the RHS is available so that `T` directly matches any
    /// type variables from the RHS).
    pub tyvar: T,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassDecl<Id = Ident> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub ctxt: Vec<Context<Id>>,
    pub defs: Vec<Method<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstDecl<Id = Ident> {
    pub name: Id,
    pub tipo: Type<Id>,
    pub ctxt: Vec<Context<Id>>,
    pub defs: Vec<Binding<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnDecl<Id = Ident> {
    pub name: Id,
    pub defs: Vec<Binding<Id>>,
    pub sign: Option<Signature<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature<Id = Ident> {
    pub ctxt: Vec<Context<Id>>,
    pub tipo: Type<Id>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Method<Id = Ident> {
    Sig(Id, Signature<Id>),
    Impl(Binding<Id>),
}

/// ```wysk
/// ~{
///       `name`
///         |          `tipo`   
///         v     vvvvvvvvvvvvvvvv
/// }~  fn foo :: a -> b -> (a, b)
///     | x y = (x, y);
/// ~~: ^^^^^^^^^^^^^^ `arms[0]`
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding<Id = Ident> {
    pub name: Id,
    pub arms: Vec<Match<Id>>,
    pub tipo: Option<Signature<Id>>,
}

/// ```wysk
///     fn foo :: Int -> Int -> Bool
/// ~~> Match[0]
/// ~~|  `args`
/// ~~|   vvv
///     | x y if x > y = True
/// ~~:       ^^^^^^^^   ^^^^
/// ~~:        `pred`   `body`
/// ~~> Match[1]
/// ~~|  `args`
/// ~~|   vvv
///     | x y = False && u where u = x + y > 0
/// ~~:   ^^^   ^^^^^^^^^^ ^^^^^^^^^^^^^^^^^^^
/// ~~: `args`    `body`         `wher[0]`
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Match<Id = Ident> {
    pub args: Vec<Pattern<Id>>,
    pub pred: Option<Expression<Id>>,
    pub body: Expression<Id>,
    pub wher: Vec<Binding<Id>>,
}

/// Pattern matching over a function definition
/// ```wysk
/// fn null :: [a] -> Bool
/// | [] = True
/// | _ = False;
/// ```
/// can be simplified to a `case` expression
/// ```wysk
/// fn null :: [a] -> Bool
/// | xs = case xs of
/// ~~> Alternative[0]
/// ~~|  `pat`
/// ~~|   vv
///     | [] -> True
/// ~~> Alternative[1]
/// ~~|  `pat`
/// ~~|   |  `pred`      `body`
/// ~~|   v vvvvvvvvv    vvvvv
///     | _ if t || u -> False
///         where t = True;
/// ~~:           ^^^^^^^^ `wher[0]`
///               u = False;
/// ~~:           ^^^^^^^^^ `wher[1]`
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alternative<Id = Ident> {
    pub pat: Pattern<Id>,
    pub pred: Option<Expression<Id>>,
    pub body: Expression<Id>,
    pub wher: Vec<Binding<Id>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Declaration<Id = Ident> {
    Data(DataDecl<Id>),
    Alias(AliasDecl<Id>),
    Fixity(FixityDecl<Id>),
    Class(ClassDecl<Id>),
    Instance(InstDecl<Id>),
    Function(FnDecl<Id>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expression<Id = Ident> {
    Ident(Id),
    Lit(Literal),
    Neg(Box<Expression<Id>>),
    Infix {
        infix: Id,
        left: Box<Expression<Id>>,
        right: Box<Expression<Id>>,
    },
    Tuple(Vec<Expression<Id>>),
    Array(Vec<Expression<Id>>),
    /// List comprehensions contain an expression and a list of statements
    /// consisting of *generators* and *predicates*.
    ///
    /// For example, if we suppose `f :: Int -> Int` is some integer-valued
    /// function, and `even :: Int -> Bool` is some integer-valued predicate
    /// testing for integer parity, then the following list expression would
    /// generate a list of the results of applying `f` to each even integer
    /// between `0` and `10` (not-inclusive).
    /// ```haskell
    ///     [ f x | x <- [0..10], even x ]
    /// ```
    /// In fact, the above expression would be equivalent to
    /// ```haskell
    ///     map f (filter even [0..10])
    /// ```
    /// and can be generalized to the following (inefficient) `let` expression,
    /// where we use `f`
    /// ```haskell
    /// let f :: a -> b
    ///     | a' = ...
    ///     g :: a -> Bool
    ///     | a'' = ...
    ///     h :: [a] -> [b]
    ///     | [] = []
    ///     | (a:as) if g a -> f a : h as
    ///     | (a:as) -> h as
    /// in ...
    /// ```
    ///
    /// In particular, we can view a list comprehension as syntactic sugar
    /// for
    ///
    List(Box<Expression<Id>>, Vec<Statement<Id>>),
    Dict(Record<Expression<Id>, Id>),
    Lambda(Pattern<Id>, Box<Expression<Id>>),
    Let(Vec<Binding<Id>>, Box<Expression<Id>>),
    App(Box<Expression<Id>>, Box<Expression<Id>>),
    Cond(Box<[Expression<Id>; 3]>),
    Case(Box<Expression<Id>>, Vec<Alternative<Id>>),
    Cast(Box<Expression<Id>>, Type<Id>),
    Do(Vec<Statement<Id>>, Box<Expression<Id>>),
    Range(Box<Expression<Id>>, Option<Box<Expression<Id>>>),
    Group(Box<Expression<Id>>),
}

impl<Id> Expression<Id> {
    pub const UNIT: Self = Self::Tuple(vec![]);
    pub const NULL: Self = Self::Array(vec![]);
    pub const VOID: Self = Self::Dict(Record::Anon(vec![]));
    pub fn is_unit(&self) -> bool {
        matches!(self, Self::Tuple(vs) if vs.is_empty())
    }
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Array(vs) if vs.is_empty())
    }
    pub fn is_void(&self) -> bool {
        matches!(self, Self::Dict(Record::Anon(vs)) if vs.is_empty())
    }
    pub fn is_empty_record(&self) -> bool {
        matches!(self, Self::Dict(Record::Anon(fs)|Record::Data(_, fs)) if fs.is_empty() )
    }
    pub fn mk_app(head: Self, tail: Self) -> Self {
        Self::App(Box::new(head), Box::new(tail))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement<Id = Ident> {
    // <PAT> <- <EXPR>
    Generator(Pattern<Id>, Expression<Id>),
    // <EXPR>
    Predicate(Expression<Id>),
    // let (<ID> <PAT>* = <EXPR>)+
    DoLet(Vec<Binding<Id>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern<Id = Ident> {
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
    pub fn is_unit(&self) -> bool {
        matches!(self, Self::Tup(vs) if vs.is_empty())
    }
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Lst(vs) if vs.is_empty())
    }
    pub fn is_void(&self) -> bool {
        matches!(self, Self::Rec(Record::Anon(vs)) if vs.is_empty())
    }
    pub fn is_empty_record(&self) -> bool {
        matches!(self, Self::Rec(Record::Anon(fs)|Record::Data(_, fs)) if fs.is_empty() )
    }
}
