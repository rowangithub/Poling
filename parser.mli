type token =
  | ACTION
  | AMPERAMPER
  | AS
  | ASSUME
  | BARBAR
  | BOOL of (bool)
  | BREAK
  | CLASS
  | COLON
  | COMMA
  | COMMENT
  | CONSTRUCTOR
  | CONTINUE
  | DISPOSE
  | DO
  | DOT
  | ELSE
  | EMPTY
  | ENSURES
  | EOF
  | EQUAL
  | IDENT of (string)
  | QIDENT of (string)
  | FIDENT of (string)
  | IF
  | INFIXOP1 of (string)
  | INFIXOP2 of (string)
  | INFIXOP3 of (string)
  | INTERFERE
  | INVARIANT
  | LBRACE
  | LBRACKET
  | LET
  | LPAREN
  | MINUSGREATER
  | NAT of (int)
  | NEW
  | PAR
  | POINTSTO
  | RBRACE
  | RBRACKET
  | REQUIRES
  | RESOURCE
  | RETURN
  | RPAREN
  | STRING of (string)
  | SEMI
  | STAR
  | THEN
  | TREE
  | UNARYOP of (string)
  | UNDERSCORE
  | VOID
  | WHEN
  | WHILE
  | WITH
  | QUALIF
  | SINGLE_QUALIF
  | SPEC
  | TILDE
  | LBRACELESS
  | GREATERRBRACE
  | WILD
  | IN
  | UNION
  | CONCAT
  | REC
  | PURESPEC
  | EFFSPEC
  | IMPLIES
  | SETDECL
  | TDESC

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Parsetree.p_program
val assn :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Parsetree.a_proposition
val qualifiers :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Parsetree.qualifier_declaration list
