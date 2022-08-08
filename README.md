# Wysk

A statically typed, functional language inspired by Haskell, ML, and Rust. This
language is effectively a rewrite and redesign of all the prior languages I've
(incompletely) implemented, but with an emphasis on modular (and ideally
non-monolithic) code.

The _Wysk_ language aims to eventually branch away from its admittedly
Haskell-heavy influence, and currently touts the following features (either
complete or as goals):

- algebraic data types
- static type inference via Hindley-Milner
- systematic overloading and polymorphism via type classes
- a flexible module system
- robust concurrency afforded by lazy semantics and a run-time system written
  purely in Rust
- leveraging the low-level power of Rust with the high-level semantics of
  Haskell

I am still fairly inexperienced when it comes to compiler development, so it
follows that this project -- and its documentation -- is _very_ much a work in
progress.

Additionally, this compiler aims to use _as little dependencies as possible_.
The common exceptions to this are the `lazy_static`, `serde` and `toml` crates;
aside from these two, the lack of external dependencies allows for a greater
amount of flexibility and control over specific functions and implementations
used within the compiler, as well as proving to be a wonderful exercise in
learning how to truly appreciate what the _Rust_ standard library has to offer.
With that being said, additional dependencies will likely be added on an
as-needed basis as the compiler itself matures -- but that'll have to wait until
I get tired of handrolling my own Rust :).

## [WIP] Examples

### Hello world

The entry point to every program, the function `main` operates within `IO`. The
actual return type of `main` is generally irrelevant, but _must_ be contained
within the `IO` type.

```haskell,rust
fn main :: IO ()
  = printLine "Hello world!"
```

### Factorial

_Wysk_ does not have traditional loops; instead it relies on recursion to
achieve the same effect. With tail-call optimization, this _generally_ allows
for fearless recursion (assuming convergent tail recursion). This can be
exploited along with `case`-like syntax at the function definition level,
allowing for branches to be predicated upon from a function's top-most scope.

```haskell,rust
fn factorial :: Int -> Int
  | n if n < 2 = 1
  | n = n * factorial (n - 1)
```

## Some reading

The following may not necessarily be directly involved within the development of
this compiler, but have proven nonetheless to be valuable sources of
information.

- [[1987] Simon Peton Jones. _The Implementation of Functional Programming Languages_](https://www.microsoft.com/en-us/research/uploads/prod/1987/01/slpj-book-1987.pdf)
- [[1992] Simon Peyton Jones. _Implementing lazy functional languages on stock hardware: the Spineless Tagless G-machine_](https://www.microsoft.com/en-us/research/wp-content/uploads/1992/04/spineless-tagless-gmachine.pdf)
- [[1997] Simon Peyton Jones, Jones & Meijer. _Type classes: an exploration of the design space_](https://www.microsoft.com/en-us/research/wp-content/uploads/1997/01/multi.pdf)
- [[1999] Simon Peyton Jones, Simon Marlow. _Secrets of the Glasgow Haskell Compiler inliner_](https://www.microsoft.com/en-us/research/wp-content/uploads/2002/07/inline.pdf)
- [[2000] Mark P. Jones, _Typing Haskell in Haskell_](https://web.cecs.pdx.edu/~mpj/thih/thih.pdf)
- [[2002] Paul Graham, _The Roots of Lisp_](languagelog.ldc.upenn.edu/myl/ldc/llog/jmc.pdf)
- [[2004] Luca Cardelli, _Type Systems_](http://lucacardelli.name/Papers/TypeSystems.pdf)
- [[2005] Daan Leijen. _Extensible records with scoped labels_](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/scopedlabels.pdf)
- [[2010] The Haskell Community. _The Haskell 2010 report_](https://www.haskell.org/definition/haskell2010.pdf)
- [[2011] Vytiniotis et al. _OutsideIn(X): Modular type inference with local assumptions_](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/jfp-outsidein.pdf)
- [[2013] Susan B. Horwitz. _UW CS704 notes_](https://pages.cs.wisc.edu/~horwitz/CS704-NOTES/)
- [[2013] Dunfield and Krishnaswami. _Complete and easy bidirectional typechecking for higher-rank polymorphism_](https://research.cs.queensu.ca/home/jana/papers/bidir/)
- [[2015] Stephen Diehl. _Write you a Haskell_](http://dev.stephendiehl.com/fun/WYAH.pdf)
- [[2020] Serrano, Have, Jones & Vytiniotis. _A Quick Look at Impredicativity_](https://www.microsoft.com/en-us/research/uploads/prod/2020/01/quick-look.pdf)
- [[2022] Gonglin Li. _An Affine Type System with Hindley-Milner Style Type Inference_](https://arxiv.org/pdf/2203.17125v1.pdf)
