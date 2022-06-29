# Wysk
A statically typed, functional language inspired by Haskell, ML, and Rust. This
language is effectively a rewrite and redesign of all the prior languages I've
(incompletely) implemented, but with an emphasis on modular (and ideally
non-monolithic) code. 

The *Wysk* language aims to eventually branch away from its admittedly
Haskell-heavy influence, and currently touts the following features (either
complete or as goals):
* algebraic data types
* static type inference via Hindley-Milner
* systematic overloading and polymorphism via type classes
* a flexible module system
* fearless concurrency afforded by lazy semantics and a run-time system written
  purely in Rust
* leveraging the low-level power of Rust with the high-level semantics of Haskell

I am still fairly inexperienced when it comes to compiler development, so it
follows that this project -- and its documentation -- is *very* much a work in
progress. 

Additionally, this compiler aims to use *as little dependencies as
possible*. The common exceptions to this are the `lazy_static`, `serde` and
`toml` crates; aside from these two, the lack of external dependencies allows
for a greater amount of flexibility and control over specific functions and
implementations used within the compiler, as well as proving to be a wonderful
exercise in learning how to truly appreciate what the *Rust* standard library
has to offer. With that being said, additional dependencies will likely be added
on an as-needed basis as the compiler itself matures -- but that'll have to wait
until I get tired of handrolling my own Rust :).

## [WIP] Examples
### Hello world
The entry point to every program, the function `main` operates within `IO`. The
actual return type of `main` is generally irrelevant, but *must* be contained
within the `IO` type.
```haskell,rust
fn main :: IO ()
  = printLine "Hello world!"
```

### Factorial
*Wysk* does not have traditional loops; instead it relies on recursion to
achieve the same effect. With tail-call optimization, this *generally* allows
for fearless recursion (assuming convergent tail recursion). This can be
exploited along with `case`-like syntax at the function definition level,
allowing for branches to be predicated upon from a function's top-most scope.
```haskell,rust
fn factorial :: Int -> Int
  | n if n < 2 = 1
  | n = n * factorial (n - 1)
```

## Todo
- [x] Implement project manifest serializer/deserializer
- [x] Design spans to allow for byte-indexing the source code
- [x] Thread-safe handwritten string interner.
- [x] Separate lexeme and token definitions to minimize footprint and facilitate error reporting
- [x] Modify lexer to depend on byte positions rather than character indices
- [x] Design module-friendly and polymorphic AST to facilitate later simplification and semantic analysis phases
- [x] Implement parser to allow for code-reuse in later syntactic analysis
- [x] Implement post-parse pass to reflect user-defined operator precedence and associativity (either from definitions within the same module or from dependencies)
- [ ] Implement identifier renaming pass to identify name clashes and generate unique names for entities involved
- [ ] Implement support for (hygienic) macros in lexing and parsing
- [x] Improve lexer error reporting to include context
- [ ] Unify error handling into its own library
- [x] Prettify error messages
- [ ] Add suggestions to error messages
- [ ] Implement optimizer passes, with importance on tail-call optimization(s).
- [x] Implement static type inference engine (Hindley-Milner+)
- [ ] Extend Hindley-Milner type inference to include type classes and
  polymorphic records
- [ ] Implement dependency analysis for global (module-level) and local (entity definition-level) scopes
- [x] Model entities as a graph and find strongly connected components (SCCs) to identify recursive dependencies
- [ ] Implement STG graph reduction scheme
- [ ] Model bytecode (and implement simple stack-based VM?)
- [ ] Implement REPL as bytecode interpreter 
- [ ] Implement primitives in Rust/C along with stdlib/prelude
- [ ] Implement spineless tagless G-machine (STG)
- [ ] Implement compiler interface 
- [ ] Add support for LLVM 
- [ ] Implement documentation generation and integrate with doc comments

## Some reading
The following may not necessarily be directly involved within the development of
this compiler, but have proven nonetheless to be valuable sources of
information. 
* [[1987] Simon Peton Jones. *The Implementation of Functional Programming Languages*](https://www.microsoft.com/en-us/research/uploads/prod/1987/01/slpj-book-1987.pdf)
* [[1992] Simon Peyton Jones. *Implementing lazy functional languages on stock
  hardware: the Spineless Tagless
  G-machine*](https://www.microsoft.com/en-us/research/wp-content/uploads/1992/04/spineless-tagless-gmachine.pdf)
* [[1997] Simon Peyton Jones, Jones & Meijer. *Type classes: an exploration of the design space*](https://www.microsoft.com/en-us/research/wp-content/uploads/1997/01/multi.pdf)
* [[1999] Simon Peyton Jones, Simon Marlow. *Secrets of the Glasgow Haskell
  Compiler
  inliner*](https://www.microsoft.com/en-us/research/wp-content/uploads/2002/07/inline.pdf)
* [[2000] Mark P. Jones, *Typing Haskell in Haskell*](https://web.cecs.pdx.edu/~mpj/thih/thih.pdf)
* [[2005] Daan Leijen. *Extensible records with scoped labels*](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/scopedlabels.pdf)
* [[2010] The Haskell Community. *The Haskell 2010 report*](https://www.haskell.org/definition/haskell2010.pdf)
* [[2011] Vytiniotis et al. *OutsideIn(X): Modular type inference with local assumptions*](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/jfp-outsidein.pdf)
* [[2013] Susan B. Horwitz. *UW CS704 notes*](https://pages.cs.wisc.edu/~horwitz/CS704-NOTES/)
* [[2013] Dunfield and Krishnaswami. *Complete and easy bidirectional typechecking for higher-rank polymorphism*](https://research.cs.queensu.ca/home/jana/papers/bidir/)
* [[2015] Stephen Diehl. *Write you a Haskell*](http://dev.stephendiehl.com/fun/WYAH.pdf)
* [[2020] Serrano, Have, Jones & Vytiniotis. *A Quick Look at Impredicativity*](https://www.microsoft.com/en-us/research/uploads/prod/2020/01/quick-look.pdf)
* [[2022] Gonglin Li. *An Affine Type System with Hindley-Milner Style Type Inference*](https://arxiv.org/pdf/2203.17125v1.pdf)