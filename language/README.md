# Wysk
Source code written in Wysk lives here! 

## Directories
* The `examples` directory holds standalone files containing source code not
  included in the language implementation. These files are generally
  for demonstration purposes only and are entirely ignored by the compiler.
* The `prim` directory holds lower level code dealing with (but not
  limited to) language runtime and intrinsics, code generation and
  foreign function interfaces for use of packages not implemented in Wysk.
* The `prelude` holds higher level abstractions that the front-facing
  end of the language depend on, as well as providing a set of core
  libraries implicitly imported into every module by the compiler.
