/// Not all possible combinations of AST nodes are valid, and in fact many may
/// be accepted *syntactically* but not *semantically* by the parser (or later
/// phases of analysis). `SynRule` ties in potential semantic errors
/// *stemming from* syntactic invariants not being upheld.
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
}
