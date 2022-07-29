///! This module contains definitions modelling the semantic requirements on
///! syntactic structures for a program to be well-formed.
///!
///! Not all strutures accepted by the parser will be necessarily valid, so the
///! AST will be analyzed in a phase later than parsing -- but earlier than
///! type-checking --  to report syntactically valid but semantically invalid
///! programs.
///!
///! Additionally, lints and other meta-program reporting will branch off of a
///! similar set of definitions to the ones found in this crate.

/// Not all possible combinations of AST nodes are valid, and in fact many may
/// be accepted *syntactically* but not *semantically* by the parser (or later
/// phases of analysis). `SynRule` defines syntactic rules not caught during
/// parsing that either violate program invariants or otherwise generally render
/// a program as malformed, and hence describe a subset of errors caught by the
/// compiler in a post-parsing -- but pre-typechecking -- phase.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SynRule {
    /// Generalization of the rules requiring syntactic instance be unique.
    NoDuplicates,
    /// Each function declaration may contain multiple match arms, *however*
    /// these match arms must all appear contiguously within the function's
    /// declaration body. This rule is broken when more than one function
    /// declaration with the *same name* is found.
    NoDuplicateFuncs,
    /// As with `NoDuplicateFuncs`, this rule requires that no duplicate methods
    /// (either definitions or implementations) be found in any declaration that
    /// contains them, i.e., class or impl declarations.
    NoDuplicateMethods,
    /// All methods defined within the body of a class declaration are required
    /// to be annotated with their corresponding type signatures
    ClassMethodAnnotated,
    /// A more general version of the invariant requiring function declarations
    /// to preserve arities across match arms. Generalized since match arms are
    /// found not only in function declarations, but also in `let` expressions
    /// and `where` clauses.
    ///
    /// For example, the following `let`-declaration for `foo` contains two
    /// arms, the first with a single pattern (and hence arity `1`) and the
    /// second with two patterns (and hence arity `2`).
    /// ```wysk
    ///     let foo
    ///     | a = 3 ~~ 1 arg => arity = 1
    ///     | b c = 12 ~~ contradiction! 2 args => arity = 2 but arity = 1!
    ///     in ...
    /// ```
    /// Since the arities aren't equal for the same binding (`foo`), this would
    /// be a compile time error.
    ///
    /// NOTE: the same applies for types! A type constructor has an arity `A` if
    /// it is fully saturated with `A` type arguments, though this is caught in
    /// a rule specific to type application arities
    ///
    BindingAritiesEqual,
    /// A binding must not have more argument patterns than denoted by its type
    /// signature. Since *Wysk* uses *currying semantics*, it is possible for a
    /// function or binding to have a type signature indicating a function with
    /// arity `K` and have `N` arguments for `N < K`, though this *does* require
    /// that the right-hand side (= body definition) resolve to a function of `K
    /// - N` parameters.
    ///
    /// For example, a function `hello :: a -> b -> c -> (a, b, c)` may have a
    /// body accepting *1*, *2*, or *3* parameters:
    /// 1. if only 1 parameter is included in the binding then the right hand
    ///    side must output what resolves to being a function of the *rest* of
    ///    the arguments, such as in the declaration below
    /// ```wysk
    ///         fn hello :: a -> b -> c -> (a, b, c)
    ///         | x = \y z -> (x, y, z)
    /// ```
    ///
    /// If `f` is a function with a signature indicating an arity of *n*, i.e.
    /// ```wysk
    /// f :: a1 -> a2 -> ... -> an -> b
    /// ```
    /// then *the number of patterns* allowed in its bindings __must not
    /// exceed__ *n*. For example, the following function declaration for `foo`
    /// is invalid, as the signature `a -> b -> c` indicates an arity of 2,
    /// while the match arm `| x y z = ...` contains *3* argument patterns.
    ///
    /// ```wysk
    /// fn foo :: a -> b -> c
    /// | x y z = ... ~~ invalid!
    /// ```
    BindingAritiesMatchType,
    /// While *data constructors* may possess distinct arities (compare `Some ::
    /// a -> Option a` with `None :: Option a`), the *arity of a type
    /// application*, defined as the number of types over which a type
    /// constructor is parametrized, must stay the same!
    ///
    /// Consider the type `Result a b`
    /// ```wysk
    /// data Result a b = Ok a | Err b
    /// ```
    /// parameterized over the type variables `a` and `b`. We can see that its
    /// *data* constructors each have arity `1`, but as a *type application*
    /// `Result a b` has arity `2`. Thus the form `Result a` in any type
    /// signature is __invalid__, as it is missing the *second* type parameter.
    TyAppAritiesEqual,
    /// In a type signature with a non-trivial context (i.e., a context is
    /// included), *all* type variables in the context must appear at least once
    /// in the type annotation that follows.
    ///
    /// Note that type variables need not occur in the context! It is only for
    /// type variables in contexts that must occur in the type annotation.
    /// * `|Show a, Show b| a -> ()`
    ///    - Invalid due to `b` occurring in the context but not the annotation
    /// * Valid: `|Show a, Show b| a -> (a, b, c)
    ///   - Valid since all type variables (`a`, `b`) in the context `|Show a,
    ///   Show b|` occur in the type annotation `(a, b, c)`
    NoUnusedCtxTyVars,
    /// The contexts in a given type signature may include the same type
    /// variable ONLY IF the corresponding type classes are NOT repeated. It is
    /// invalid for the *same* context to appear more than once in a list of
    /// contexts.
    /// * `|Show a, Show a|`
    ///     - Invalid due to duplicate instances of `Show a`
    /// * `|Show a, Show a'|`
    ///     - Valid since `a` is lexicographically distinct from `a'`
    NoDuplicatesInCtx,
    /// Prohibits infinitely sized types introduced by
    /// self-referential/recursive type aliases. This is because type aliases
    /// are replaced with their definition at compile time, and with the same
    /// type on both sides of the equation, applkying substitution would fail to
    /// arrive at a solution due to an unbounded strictly monotonic increase in
    /// terms.
    ///
    /// For example, consider the alias `type Foo = Foo Bar`. Since type aliases
    /// are erased at compile time, we first derive the substitution `{ a := Foo
    /// }` and replace `Foo` with `a` on both sides to get `a = a Bar`, which is
    /// impossible since that would imply `a = a (a (a ... (a ...)))`, with
    /// `Bar` infinitely unattainable ad infinitum. The same does not hold
    /// however for `data` definitions, which provide a level of indirection
    /// necessary to deal with isorecursive types.
    NoRecursiveAliases,
    /// All declared fixities must have a corresponding function definition.
    NoActionlessFixities,
    /// Infixes declared with non-associative fixities may not be used
    /// sequentially in ungrouped expressions. Moreover, two infixes with the
    /// same precedence level but opposite associativities may not be used
    /// sequentially without parentheses to disambiguate groupings.
    ///
    /// For example, if the fixity for the operator `:=` is declared without any
    /// associativity, then the expression `a := b := c` would be invalid and
    /// would require parentheses to disambiguate their syntactic grouping,
    /// e.g., `(a := b) := c` or `a := (b := c)`.
    ///
    /// On the other hand, if the operators `:<` and `>:` are declared with the
    /// same precedence but differ in their associativities, then the expression
    /// `a :< b >: c` would be invalid and would require parentheses to
    /// disambiguate grouping, e.g., `(a :< b) >: c` or `a :< (b >: c)`, etc.
    NoAmbiguousFixities,
}

/// While `SynRule`s flag syntax-driven semantic errors *within* the contents
/// output by the parser, `ProgRule`s flag semantic errors at the level of
/// modules and across multiple outputs by the parser. This means that issues
/// flagged *within* a file (read: module) are described `SynRule`s -- such as
/// duplicate definitions or recursive type-aliases -- while issues at the
/// module level -- such as invalid module imports -- are described by
/// `ProgRule`s.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ProgRule {
    /// Data constructors alone may not be imported; in order to import a data
    /// constructor, their type must also be imported.
    NoConstructorImports,
    /// Imports from a given module must be exported by that module, i.e., a
    /// module must re-export the items being imported.
    ///
    /// For example, if module `C` exports the function `foo`, and module `B`
    /// imports `foo` from module `C`, then module `B` must re-export `foo` in
    /// order for module `A` to import it from module `B`.  
    NoProtectedImports,
    /// Emited when importing a non-existent *item* from a module. If the item
    /// in question *does* exist but is simply not exported from the module from
    /// which it is being imported, then the `NoProtextedImports` rule is
    /// violated and emitted instead.
    ///
    /// For example, suppose we had three modules `A`, `B`, and `C`, where
    /// module `A` imports `foo` from module `B`. Then if `foo` is not defined
    /// in module `B` and module `B` doesn't import `foo` from any other module,
    /// then this error is emitted. Likewise, suppose `B` imports `foo` from
    /// module `C`; then this error would be emitted if module `C` nether
    /// defines nor imports `foo` from any other module.
    ///
    /// On the other hand, if module `B` imports `foo` from module `C`, and
    /// `foo` is defined in module `C` but does not export it, then the
    /// `NoProtectedImport` rule is instead broken, as would be the case if
    /// module `C` did export `foo` but module `B` didn't.
    UnresolvedImport,
    /// Emitted when two files whose names differ only by the case of the first
    /// letter are found in the same directory. This is because the compiler
    /// internally transforms the first letter of a given filename to be to
    /// match the name of the declared module in the file, typically by changing
    /// the first letter to be uppercase.  
    ///
    /// Note that file and directory names should generally begin with a
    /// lowercase letter, but it is not an error for a file or directory name --
    /// excluding the reserved filenames `main.wy`, `lib.wy` and `mod.wy`, -- to
    /// begin with an uppercase letter.
    ///
    /// For example, if the directory `D` has the files `Foo.wy` and `foo.wy`,
    /// then the `NoFilenameAmbiguity` rule is violated since both files would
    /// correspond to the module `Foo`.
    NoFilenameAmbiguity,
    /// Module names need not have their paths qualified if the imported module
    /// is a sibling of the importing module in question. This means that the
    /// module `A` can only import the module `B` using the name `B` if both
    /// files for each modules are siblings. If the file for module `B` is the
    /// child of a directory `D` -- but there is no module `D` -- and `D` is in
    /// the same directory as the file for module `A`, then module `B` must be
    /// included in the project's manifest file using the path relative to the
    /// project root.
    ModuleNotInManifest,
    /// TODO: maybe this belongs in `SynRule` instead??
    /// TODO: renamed modules and imports
    ///
    /// Prevents defining top-level items with the same name as any unqualified
    /// imports. This does *not* apply to *hidden* (read: excluded) imports.
    ///
    /// Suppose module `A` exports the functions `foo`, `bar`, and `baz`, and
    /// suppose module `B` has the following imports:
    /// ```wysk
    /// module B where
    /// import A { foo, bar }
    /// ```
    /// Then it would be an error for module `B` to define a top-level function
    /// with the name `foo` or `bar`; note however that this *only* applies at
    /// the top-level: local bindings may freely shadow existing bindings
    /// defined at any level preceding them.
    ///
    /// Now -- using the same definition of module `A` from above -- suppose
    /// that module `B` has the following imports instead:
    /// ```wysk
    /// module B where
    /// import A hiding { foo } ~~ import everything BUT `foo`
    /// ```
    /// Then it would be perfectly fine for module `B` to define a binding named
    /// `foo` at the top-level since `foo` is excluded from the list of imports
    /// from module `A`.
    ///
    /// If instead we had one of the imports qualified as in
    /// ```wysk
    /// module B where
    /// import qualified A { foo } ~~ import `foo`, accessible ONLY as `A.foo`
    /// import A { bar } ~~ import `bar`, accessible as `bar`
    /// ```
    /// then module `B` would be free to define `foo` at the top-level, since
    /// the qualified import from module `A` only exposes `foo` but does *not*
    /// bring it into scope. On the other hand, `bar` would be brought into
    /// scope as an import and hence prevents any bindings of the same name from
    /// being defined.
    ///
    NoShadowingImports,
    /// Flags the instance in which a given import is not actually defined but
    /// is cyclically imported through a chain of module imports.
    ///
    /// For example, suppose we had the modules `A`, `B` and `C`, and suppose
    /// module `A` imports `foo` from module `B`, module `B` imports `foo` from
    /// module `C`, and module `C` imports `foo` from either module `A` or `B`.
    /// Then the definition of `foo` is actually non-existent (hence the term
    /// "rumored") and this rule is broken.
    ///
    /// Note that this rule is distinctly general cyclic dependencies. When
    /// supported by the compiler, cyclic dependencies do not necessarily break
    /// any rules (assuming their definitions are resolvable).
    NoRumoredImports,
    /// Emitted when no entry-point was found for a given project. This can be
    /// caused by the following scenarios, where the `src` directory referenced
    /// is in the same directory as the manifest file:
    /// * for executables
    ///     * the (exe) entry-point is not defined in the manifest and the `src`
    ///       directory does not have a (direct descendant) `main.wy` file
    ///     * the entry-point defined in the manifest exists but is not for an
    ///       executable
    ///     * the entry-point defined in the manifest exists but is an ancestor
    ///       of the project's root directory
    /// * for libraries
    ///     * the (lib) entry-point is not defined in the manifest and the `src`
    ///       directory does not have a (direct descendant) `lib.wy` file
    /// * for packages
    ///     * the package directory is not defined in the manifest
    ///     * the package directory does not have a child named `pkg.wy`
    /// * for scripts
    ///     * the file is named `main.wy` and is a child of the `src` directory
    ///     * the file is named `lib.wy` and is a child of the `src` directory
    NoEntryPoint,
    /// Emitted when a dependency in the manifest cannot be attained using the
    /// configurations listed.
    ///
    /// For example, a dependency in the manifest lists an invalid/non-existent
    /// git repository, or a filepath not found in the user's file system.
    BadResource,
}
