# Wysk Syntax

## Outline
* Two kinds
    - Sugared
    - Desugared (equivalent to Haskell's *Core*)
* Infixes are initially parsed as though they were all *left associative* with *equal* precedence.
    - This is because a given module may import operators (and their associated
      fixities) from other modules, and since the parser is generalized to work
      on a *per module* basis, this would lead to imported operators being
      incorrectly parsed (or worse, rejected by the parser due to unknown
      fixities).
    - Then, when all source files have been parsed (and *before* proceeding to
      further analysis passes such as *desugaring*, *renaming*, and *type
      checking*) and all *fixities* are known.