# Wysk Syntax
This crate contains the definitions needed to build the abstract
syntax tree (AST) of a Wysk program, with the exception of `Literal`s, which are
defined in the `lexer` crate.

*Wysk* has a syntax very similar to that of *Haskell*, with a few differences.
Unlike in Haskell, *layout* is not implicit (it is still up in the air whether
I'm up for implementing this; there are some parsing considerations that still
need to be ironed out before resorting to implicit layout in the same vein as
*Haskell*'s).

Some key differences:
* top level function definitions are preceded by the `fn` keyword
* function signatures, if included, must follow the declared function name and
  *precede* the function definition body. This may be changed in future
  versions.
* like in *Haskell*, functions may be defined equationally by listing out their
  respective bodies in their own binding groups differentiated by the function's
  arguments. Unlike *Haskell* however, the function *name* is not repeated, and
  instead each sub-definition is separated by a vertical pipe `|` (as in `ML`).
  Thus while `|` indicates a pattern guard in Haskell, it is simply treated as a
  delimiter for function definition binding groups. 
* semicolons are generally expected to terminate a declaration, with the
  exception of top level function definitions and data declarations, where we
  are able to determine boundaries upon encountering the aforementioned vertical
  pipe `|`. In general, either a keyword, semicolon, or pipe must separate
  distinct declarations. 
* function definition argument patterns may be *guarded* by boolean predicates
  in a manner most similar to that of match arm predicates in *Rust*.
* the keyword `impl` is used for class instances over the `instance` keyword
  found in *Haskell*, weakly alluding to the `impl` blocks found in *Rust*. 
* curly braces are required in `class` and `impl` declarations, with semi-colons
  strictly necessary within these two syntactic contexts.
* class contexts are found in the same position in type signatures as their
  *Haskell* counterparts, but are wrapped in vertical pipes instead of relying
  on the implication arrow `:=>`. This makes parsing a bit easier. Additionally,
  syntax sugar is planned to shorten long and repetitive constraints such as
  `|Class a, Class b, Class c, Class d, ... |`. 

## Grammar
Below is the EBNF grammar for *Wysk*, with concatenative commas omitted for brevity.

**Note:** Lexical syntax may be found in the *README* for the `lexer` crate.

```ebnf
Program := "module" ModName "where" Imports Decls;
ModName := Upper {".", Upper};

Imports := {Import};
Import := "import" ImportSpec ["{" ImportList "}"];
ImportSpec := ["qualified"] ModName [Rename] ["hiding"];
Rename := "@" Upper;
ImportList := ImportItem ["," ImportList];
ImportItem := AbstractImport 
            | ValueImport 
            | DataImport;
AbstractImport := Upper ;
ValueImport := Lower | "(" Infix ")";
DataImport := Upper "(" ConstructorList ")" | Upper;
ConstructorList := Upper {"," Upper}
                 | "..";

Decls := {Decl};
Decl := FixityDecl 
      | DataDecl 
      | AliasDecl 
      | FnDecl
      | ClassDecl 
      | ImplDecl 
      | NewtypeDecl
      ;

FixityDecl := FixityKeyword FixityPrec Infix {Infix};
FixityKeyword := "infix" | "infixl" | "infixr";
FixityPrec := "0" | "1" | "2" | "3" | "4" 
            | "5" | "6" | "7" | "8" | "9";

DataDecl := "data" [Context] Upper {Lower} "=" Variants ["with" Derives];
Context := "|" Upper Lower {"," Upper Lower} "|";
Variants := Variant {"|" Variant};
Variant := Upper "{" FieldSigs "}" | Upper {Type};
FieldSigs := FieldSig {"," FieldSig};
FieldSig := (Lower | Label) "::" Type;
Derives := "(" Upper {"," Upper} ")" | Upper;

Type := TyCon | TyVar | TyApp | Ty;
TyCon := Upper;
TyVar := Lower;
TyApp := "(" Upper {TyArg} ")";
TyArg := TyCon | TyVar | ListTy | TupleTy | "(" TyApp | FunTy ")";
Ty := ListTy | TupleTy | FunTy;
ListTy := "[" Type "]";
TupleTy := "()" | "(" Type {"," Type} ")";
FunTy := Type "->" Type;

AliasDecl := "type" Upper {Lower} "=" Type;

FnDecl := "fn" Binding;
Binding := FnId [FnSig] FnArms;
FnId := Lower | "(" Infix ")";
FnSig := "::" TySig;
TySig := [Context] Type;
FnArms := FirstArm {RestArms};
FirstArm := ["|"] {Pat} [Pred] "=" FnRhs;
Pred := "if" Expr;
RestArms := {"|" FirstArm};
FnRhs := Expr [WhereDecls];
WhereDecls := "where" Binding [";"] | "{" Binding {"," Binding} "}";

ClassDecl := "class" [Context] Upper Lower ["where"] "{" ClassItems "}";
ClassItems := {ClassItem ";"};
ClassItem := FnId FnSig [FnArms];

ImplDecl := "impl" [Context] Upper Type "{" MethodImpls "}";
MethodImpls := {Binding ";"};

NewtypeDecl := "newtype" Upper {Lower} "=" (RecordNewtype | StackedNewtype);
RecordNewtype := Upper "{" Lower "::" Type "}";
StackedNewtype := Upper {Type});

Pat := WildPat
     | VarPat
     | Literal
     | TuplePat
     | ArrayPat
     | LinkPat
     | AtPat
     | OrPat
     | RecordPat
     | RangePat
     | CastPat
     ;
WildPat := "_";
VarPat := Lower;
TuplePat := "()" | "(" Pat {"," Pat} ")";
ArrayPat := "[]" | "[" Pat {"," Pat} "]";
LinkPat := "(" Pat ":" Pat ")";
AtPat := Lower "@" Pat;
OrPat := Pat {"|" Pat};
RecordPat := Upper "{}" | Upper "{" FieldPat {"," FieldPat} "}";
FieldPat := Lower ["=" Pat];
RangePat := "[" RangePatBound ".." [RangePatBound] "]";
RangePatBound := IntLiteral | CharLiteral;

Expr := LetExpr 
      | CaseExpr 
      | CondExpr 
      | LambdaExpr 
      | AppExpr 
      | CastExpr 
      | AtomExpr
      ;
LetExpr := "let" Binding "in" Expr;
CaseExpr := "case" Expr "of" "{" CaseArms "}";
CaseArms := {"|" CaseArm};
CaseArm := Pat [Pred] "->" FnRhs;
CondExpr := "if" Expr "then" Expr "else" Expr;
LambdaExpr := "\\" Pat {Pat} "->" Expr;
AppExpr := (Upper | Lower) {Expr} 
         | RecordExpr;
CastExpr := "(" Expr "::" Type ")";
AtomExpr := Upper 
          | Lower 
          | TupleExpr 
          | ArrayExpr 
          | ListExpr 
          | RangeExpr
          | RecordExpr 
          | FieldAccess 
          | Literal
          | "()" 
          | "[]"
          ;
TupleExpr := "(" Expr {"," Expr} [","] ")";
ArrayExpr := "[" Expr {"," Expr} [","] "]";
ListExpr := "[" Expr "|" Stmts "]";
RangeExpr := "[" RangeBound ".." [RangeBound] "]";
RangeBound := (Upper | Lower | IntLiteral | CharLiteral)
Stmts := {Stmt ","};
Stmt := Pat "<-" Expr | Expr | "let" Binding;
RecordExpr := (Upper | Lower) "{" FieldExpr {"," FieldExpr} "}";
FieldExpr := (Lower | Label) ["=" Expr];
FieldAccess := Lower {"." (Lower | Label)};
Literal := IntLiteral 
         | CharLiteral 
         | StringLiteral
         | ByteLiteral
         ;

```

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