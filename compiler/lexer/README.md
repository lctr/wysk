# Wysk Lexer

This library encompasses the lexical analysis phase of the compiler's front end.

# Lexical Syntax
The following describes the kinds of lexemes recognized by the lexer. Note that not *all* of the left-hand-side lexeme kinds correspond to their own lexical token when lexing source input.

```
Program := (Lexeme | Whitespace)*
Lexeme := Keyword | Punct | Name | Literal
Keyword := "case" | "class" | "data" | "do" | "else" 
         | "fn" | "hiding" | "if" | "import" | "impl" 
         | "in" | "infixl" | "infixr" | "let" | "module" 
         | "of" | "qualified" | "then" | "type" 
         | "where" | "with" | "_"

Name := Upper | Lower | Infix 
VarId := (VarStart (VarRest)*)\Keyword
VarStart := LowerChar
VarRest := LowerChar | UpperChar | Digit | "'" | "_"
ConId := UpperChar (ConRest | ":" InfixChar+)+
ConStart := UpperChar 
ConRest := LowerChar | UpperChar | Digit | "'" | "_"
ModId := (ConId ".")* ConId
TyVar := VarId
TyCon := ConId
Class := ConId

Infix := "`" VarId "`" | (InfixChar)+\Punct
InfixChar := "!" | "@" | "#" | "$" | "%" | "^" | "&" | "*" 
           | "-" | "+" | "?" | "/" | "|" | "\" | "~" | ":" 
Delim := "(" | ")" | "[" | "]" | "{" | "}"
Punct := "::" | "\" | "@" | "#" | "=" | "," | ";" 
       | "|" | ".." | "->" | "<-" | "=>"

Literal := Digit | Char | String 

Digit := Binary | Octal | Hexadecimal | Decimal 
Binary := "0b" (BinDigit)+
Octal := "0o" (OctDigit)+
Hexadecimal := "0x" (HexDigit)+
Decimal := ("0" | DecDigit) "." (DecDigit)+ 
         | (DecDigit)+ ("e" | "E") ("+" | "-")? (DecDigit)+
BinDigit := "0" | "1"
OctDigit := "0" | ... | "7"
DecDigit := "0" | ... | "9" 
HexDigit := DecDigit | "a" | ... | "f" | "A" | ... | "F"

Whitespace := Skipped (Skipped)+
Skipped := SpaceChar | Comment 
SpaceChar := Newline | VerticalTab | " " | "\t" | Unicode.Whitespace
Newline := "\n" | "\n\r"
Comment := LineComment | BlockComment | DocComment
LineComment := "~~" Any Newline
BlockComment := "~{" Any "}~"
DocComment := DocStart | DocInner | DocAfter | DocCode
DocStart := "~~>" Any Newline
DocInner := "~~|" Any Newline
DocAfter := "~~:" Any Newline
DocCode := "~~<" LangId ">" NewLine (DocInner)* "~~</>" 
         | "~~|" "```" (LangId)? Newline (DocInner)* "```"
         | "```" (LangId)? (Any\Newline) "```"

```
