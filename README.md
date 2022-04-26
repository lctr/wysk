# Wysk

A statically typed, functional language inspired by Haskell, ML, and Rust. This language is effectively a rewrite and redesign of all the prior languages I've (incompletely) implemented, but with an emphasis on modular (and ideally non-monolithic) code.

I am still fairly inexperienced when it comes to compiler development, so it follows that this project -- and its documentation -- is *very* much a work in progress. 

## Goals
Below are some of the things I'm hoping to implement. 
* Algebraic data types
* Typeclasses 
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
- [ ] Design module-friendly and polymorphic AST to facilitate later simplification and semantic analysis phases
- [ ] Implement parser to allow for code-reuse in later syntactic analysis
- [ ] Implement post-parse pass to reflect user-defined operator precedence and associativity (either from definitions within the same module or from dependencies)
- [ ] Implement documentation generation and integrate with doc comments
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
- [ ] Add support for LLVM 
- [ ] Implement compiler interface 