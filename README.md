# Wysk

A statically typed, functional language inspired by Haskell, ML, and Rust. This language is effectively a rewrite and redesign of all the prior languages I've (incompletely) implemented, but with an emphasis on modular (and ideally non-monolithic) code.

I am still fairly inexperienced when it comes to compiler development, so it follows that this project -- and its documentation -- is *very* much a work in progress. 

## Goals
Below are some of the things I'm hoping to implement. 
* Algebraic data types
* Typeclasses/systematic overloading 
* Hindley-Milner type inference
* Extensible records
* Interactive bytecode interpreter
* LLVM JIT compilation

## Todo
- [x] Implement project manifest serializer/deserializer
- [x] Design spans to allow for byte-indexing the source code
- [x] Thread-safe handwritten string interner.
- [x] Separate lexeme and token definitions to minimize footprint and facilitate error reporting
- [x] Modify lexer to depend on byte positions rather than character indices
- [x] Design module-friendly and polymorphic AST to facilitate later simplification and semantic analysis phases
- [ ] Implement parser to allow for code-reuse in later syntactic analysis
- [x] Implement post-parse pass to reflect user-defined operator precedence and associativity (either from definitions within the same module or from dependencies)
- [ ] Implement identifier renaming pass to identify name clashes and generate unique names for entities involved
- [ ] Implement support for (hygienic) macros in lexing and parsing
- [ ] Improve lexer error reporting to include context
- [ ] Unify error handling into its own library
- [ ] Prettify error messages
- [ ] Add suggestions to error messages
- [ ] Implement static type inference engine (Hindley-Milner+)
- [ ] Implement dependency analysis for global (module-level) and local (entity definition-level) scopes
- [x] Model entities as a graph and find strongly connected components (SCCs) to identify recursive dependencies
- [ ] Implement graph reduction scheme
- [ ] Model bytecode (and implement simple stack-based VM?)
- [ ] Implement REPL as bytecode interpreter 
- [ ] Implement primitives in Rust/C along with stdlib/prelude
- [ ] Implement spineless tagless G-machine (STG)
- [ ] Implement compiler interface 
- [ ] Add support for LLVM 
- [ ] Implement documentation generation and integrate with doc comments

## Some reading
The following may not necessarily be directly involved within the development of this compiler, but have proven nonetheless to be valuable sources of information.
* [[1992] Simon Peyton Jones. *Implementing lazy functional languages on stock hardware: the Spineless Tagless G-machine*](https://www.microsoft.com/en-us/research/wp-content/uploads/1992/04/spineless-tagless-gmachine.pdf)
* [[1999] Simon Peyton Jones, Simon Marlow. *Secrets of the Glasgow Haskell
  Compiler inliner*](https://www.microsoft.com/en-us/research/wp-content/uploads/2002/07/inline.pdf)
* [[2005] Daan Leijen. *Extensible records with scoped labels*](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/scopedlabels.pdf)
* [[2010] The Haskell Community. *The Haskell 2010 report*](https://www.haskell.org/definition/haskell2010.pdf)
* [[2011] Vytiniotis et al. *OutsideIn(X): Modular type inference with local assumptions*](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/jfp-outsidein.pdf)
* [[2013] Susan B. Horwitz. *UW CS704 notes*](https://pages.cs.wisc.edu/~horwitz/CS704-NOTES/)
* [[2013] Dunfield and Krishnaswami. *Complete and easy bidirectional typechecking for higher-rank polymorphism*](https://research.cs.queensu.ca/home/jana/papers/bidir/)
* [[2015] Stephen Diehl. *Write you a Haskell*](http://dev.stephendiehl.com/fun/WYAH.pdf)
* [[2020] Serrano, Have, Jones, Vytiniotis. *A Quick Look at Impredicativity*](https://www.microsoft.com/en-us/research/uploads/prod/2020/01/quick-look.pdf)
* [[2022] Gonglin Li. "An Affine Type System with Hindley-Milner Style Type Inference"](https://arxiv.org/pdf/2203.17125v1.pdf)