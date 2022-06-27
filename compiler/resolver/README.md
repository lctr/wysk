# Wysk Resolver
This crate inspects all read/parsed modules and resolves transitive
dependencies. In the pipeline, this crate is used after parsing all target
files/modules within a project, and works in tandem with the `session` crate. 

The `resolver` prepares front-end data for the `typechecking` phase (from crate `check`) as well as
for the `simplifier` (from crate `simple`). 

This crate implements two main functionalities: 
* Dependency analysis
    - Module organization to form a module hierarchy and set the foundation for
      the global namespace
    - Dependency analysis and resolution to identify deadcode along with transitive and
      recursive dependencies (relying on the `graph` crate)
* Renaming and identifier resolution
    - Generating unique identifiers across modules for the compiler's global namespace
    - Sanitizing identifiers in preparation for representation lowering and
      preparation for assembly code generation

This crate depends on the following crates defined in the compiler:
* `common` - utils
* `span`
* `intern` - symbols
* `name` - identifiers
* `sources` - source files
* `graph` - data structure traversals
* `syntax` - ast 