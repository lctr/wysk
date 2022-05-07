use wy_common::{deque, Map};
use wy_intern::symbol::{self, Symbol};

pub use wy_lexer::{comment::Comment, Literal};

pub mod fixity;
pub mod ident;
pub mod tipo;
pub mod visit;

use fixity::*;
use ident::*;
use tipo::*;

// TODO: documentation; potential split-up of definitions into separate files?

wy_common::newtype!({ u64 in Uid | Show (+= usize |rhs| rhs as u64) });

#[derive(Clone, Debug)]
pub struct Program<Id = Ident> {
    pub module: Module<Id>,
    pub fixities: FixityTable,
    pub comments: Vec<Comment>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module<Id = Ident, Uid = Id> {
    pub modname: Chain<Uid>,
    pub imports: Vec<ImportSpec<Id>>,
    pub datatys: Vec<DataDecl<Id>>,
    pub classes: Vec<ClassDecl<Id>>,
    pub implems: Vec<InstDecl<Id>>,
    pub fundefs: Vec<FnDecl<Id>>,
    pub infixes: Vec<FixityDecl<Id>>,
    pub aliases: Vec<AliasDecl<Id>>,
}

impl Default for Module {
    fn default() -> Self {
        Self {
            modname: Chain::new(Ident::Upper(symbol::intern_once("Main")), deque![]),
            imports: vec![],
            datatys: vec![],
            classes: vec![],
            implems: vec![],
            fundefs: vec![],
            infixes: vec![],
            aliases: vec![],
        }
    }
}

/// Describe the declared dependencies on other modules within a given module.
/// Every import spec brings into scope the entities corresponding to the
/// identifiers included.
///
/// When a module `A` imports entities from another module `B`, the items
/// imported from `B` are brought into scope for module `A`. Additionally,
/// module `A` will export by default imports from `B` unless the `ImportSpec`
/// for imports from `B` has a `hidden` value of `true`.
///
/// The module from which items are imported from may be *qualified* and/or
/// *renamed*. When a module is *qualified*, its imports are no longer
/// accessible without prefixing the module name. When a module is *qualified*
/// __and__ *renamed*, the module prefix necessary to access its imports is
/// restricted to matching the new name only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportSpec<Id = Ident> {
    pub name: Chain<Id>,
    pub qualified: bool,
    pub rename: Option<Id>,
    pub hidden: bool,
    pub imports: Vec<Import<Id>>,
}

impl<Id> ImportSpec<Id> {
    pub fn get_imports(&self) -> &[Import<Id>] {
        self.imports.as_slice()
    }

    pub fn infix_deps(&self) -> impl Iterator<Item = &Import<Id>> {
        self.imports
            .iter()
            .filter(|imp| matches!(imp, Import::Operator(..)))
    }
}

/// Describe the named entity to be imported. When contained by an `ImportSpec`,
/// these imports may either be *public* if the `ImportSpec` has its `hidden`
/// field set to `false`. Otherwise, the imports will become accessible through
/// *multiple* namespaces. E.g., suppose module `A` imports the function `bar`,
/// the data type `Baz` along with all of its constructors from the module `B`,
/// and assume that the module `B` is not hidden. Then the function `bar` will
/// be accessible via the identifiers `B.bar` and `bar`, as well as having the
/// absolute path `A.B.bar`.
///
/// Note: At the parsing level, it is generally impossible to distinguish
/// between type imports, type constructor imports, and class imports, as they
/// all begin with uppercase letters. However, semantic context allows for bare
/// patterns that *may* indicate the specific kind an import may be. The terms
/// `Operator`, `Function`, `Abstract`, `Total`, and `Partial`
/// * Type aliases are always `Abstract`
///
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Import<Id = Ident> {
    /// Infix imports
    Operator(Id),
    Function(Id),
    /// Importing a type (without any of its constructors) or a class (without
    /// any of its methods).
    Abstract(Id),
    /// Data type imports that include *all* of their constructors
    Total(Id),
    /// Data type imports that include only the specified constructors, OR
    Partial(Id, Vec<Id>),
}

impl<Id> Import<Id> {
    /// If the import corresponds to an infix operator, then return the
    /// identifier wrapped in a `Some` variant. Otherwise, return `None`.
    pub fn infix_id(&self) -> Option<&Id> {
        if let Self::Operator(id) = self {
            Some(id)
        } else {
            None
        }
    }
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

impl<Id: Copy + Eq + std::hash::Hash> From<&[FixityDecl<Id>]> for FixityTable<Id> {
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

///
/// ```wysk
/// ~~        `name` `poly`
/// ~~           V   /
/// data |A a| Foo a
/// ~~    ^^^
/// ~~   `ctxt`
///     = Bar a
/// ~~    ^^^^^
/// ~~   `vnts[0]`
///     | Baz a (Foo a)
/// ~~    ^^^^^^^^^^^^^
/// ~~   `vnts[1]`
///     with (B, C, D);
/// ~~       ^^^^^^^^
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DataDecl<Id = Ident> {
    pub name: Id,
    pub poly: Vec<Tv>,
    pub ctxt: Vec<Context<Id>>,
    pub vnts: Vec<Variant<Id>>,
    pub with: Vec<Id>,
}

impl<Id> DataDecl<Id> {
    pub fn enumer_tags(mut self) -> Self {
        let mut i = 0;
        for Variant { tag, .. } in self.vnts.iter_mut() {
            *tag = Tag(i);
            i += 1;
        }
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variant<Id = Ident> {
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
    pub dict: Option<(Id, Signature)>,
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
    pub sign: Option<Signature<Id>>,
    pub defs: Vec<Match<Id>>,
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
    /// Identifier expressions; these can contain either *lowercase*-initial
    /// identifiers (corresponding to values), *uppercase*-initial identifiers
    /// (correstpondingo constructors), OR infix identifiers (corresponding to
    /// infixes used in non-infix nodes).
    ///
    /// Note that *qualified* identifiers are parsed as `Path`s! This is because
    /// `.` has record selection semantics, and namespaces are treated as
    /// records. Thus, the expression `f x` contains two `Ident` nodes, while
    /// the expression `F.x` contains a single `Path` node.
    Ident(Id),
    /// A combination of identifiers. The first identifier, coined the `root` is
    /// held separately from the rest, and it is *impossible* for a node of this
    /// variety to have an empty vector of identifiers (called the `tail`).
    ///
    /// A path `A.b.c` is represented as `Path::(A, [b, c])`, where the `tail`
    /// contains identifiers implicitly prefixed with a `.`.
    ///
    /// Path nodes are ultimately resolved to identifiers, and currently have
    /// two semantic uses:
    /// * identifier qualification; if a module `M` is
    /// imported and qualified as `N`, and `f` is exported from `M`, then `M.f`
    /// and `N.f` correspond to the same thing.
    /// * record selection; if a record `r` has field `f`, then `r.f` is
    ///   equivalent to the call `r f`
    Path(Id, Vec<Id>),
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
    /// ```wysk
    ///     [ f x | x <- [0..10], even x ]
    /// ```
    /// In fact, the above expression would be equivalent to
    /// ```wysk
    ///     map f (filter even [0..10])
    /// ```
    /// and can be generalized to the following (inefficient) `let` expression,
    /// where we use `f`
    /// ```wysk
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

    /// If an expression is a `Group` variant, return the inner node.
    /// Otherwise, returns `Self`.
    pub fn ungroup(self) -> Self {
        match self {
            Expression::Group(expr) => *expr,
            expr => expr,
        }
    }

    /// If an expression is a `Group` variant, return a reference to the inner
    /// node. Otherwise, return a reference to `Self`.
    pub fn ungroup_ref(&self) -> &Self {
        match self {
            Expression::Group(expr) => expr.as_ref(),
            expr => expr,
        }
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
    // `let` without the `in`;
    // let (<ID> <PAT>* = <EXPR>)+
    JustLet(Vec<Binding<Id>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern<Id = Ident> {
    /// Describes the wildcard pattern and is written `_`. Since it is a
    /// wildcard pattern, it matches against *any* pattern.
    Wild,
    /// Describes a named wildxard pattern and syntactically corresponds to *any
    /// lowercase-initial identifier*. The pattern `a` is a `Var` pattern and
    /// can be rewritten as the `At` pattern `a @ _`, so it follows that this
    /// pattern matches against *any* pattern, but *also* introduces a
    /// *binding* between the identifier and the element being matched on.
    Var(Id),
    /// Describes a literal as a pattern and is the one variant of patterns with
    /// specific restrictions.
    Lit(Literal),
    /// Describes the pattern formed by a data constructor and its arguments
    /// (data). In particular, the data constructor *must* be an
    /// uppercase-initial identifier.
    Dat(Id, Vec<Pattern<Id>>),
    Tup(Vec<Pattern<Id>>),
    /// Describes a list formed with array-like bracket syntax, e.g.,
    /// `[a, b, c]`. Syntactic sugar for lists.
    Vec(Vec<Pattern<Id>>),
    /// Describes a list formed with cons operator infix syntax, e.g.,
    /// `(a:b:c)`. Note that *as a pattern*, this *must* occur within
    /// parentheses, as *operator fixities are not observed in patterns*.
    Lnk(Box<Pattern<Id>>, Box<Pattern<Id>>),
    At(Id, Box<Pattern<Id>>),
    Or(Vec<Pattern<Id>>),
    Rec(Record<Pattern<Id>, Id>),
    Cast(Box<Pattern<Id>>, Type<Id>),
}

impl<Id> Pattern<Id> {
    pub const UNIT: Self = Self::Tup(vec![]);
    pub const NIL: Self = Self::Vec(vec![]);
    pub const VOID: Self = Self::Rec(Record::VOID);
    pub fn is_unit(&self) -> bool {
        matches!(self, Self::Tup(vs) if vs.is_empty())
    }
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Vec(vs) if vs.is_empty())
    }
    pub fn is_void(&self) -> bool {
        matches!(self, Self::Rec(Record::Anon(vs)) if vs.is_empty())
    }
    pub fn is_empty_record(&self) -> bool {
        matches!(self, Self::Rec(Record::Anon(fs)|Record::Data(_, fs)) if fs.is_empty() )
    }
}
