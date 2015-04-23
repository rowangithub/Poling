{
(* Poling: Proof Of Linearizability Generator 
 * Poling is built on top of CAVE and shares the same license with CAVE 
 * See LICENSE.txt for license.
 * Contact: He Zhu, Department of Computer Science, Purdue University
 * Email: zhu103@purdue.edu
 *)	
(******************************************************************************)
(*   __               ___     CAVE: Concurrent Algorithm VErifier             *)
(*  /     /\  \    / |        Copyright (c) 2010, Viktor Vafeiadis            *)
(* |     /--\  \  /  |---                                                     *)
(*  \__ /    \  \/   |___     See LICENSE.txt for license.                    *)
(*                                                                            *)
(******************************************************************************)
open Lexing
open Parser

(* association list of keywords *)
let keyword_ht = Hashtbl.create 71

let _ =
  List.iter (fun (s,tok) -> Hashtbl.replace keyword_ht s tok)
    ["_",           UNDERSCORE;
     "action",      ACTION;
     "as",          AS;
     "assume",      ASSUME;
     "break",       BREAK;
     "class",       CLASS;
     "comment",     COMMENT;
     "constructor", CONSTRUCTOR;
     "continue",    CONTINUE;
     "dispose",     DISPOSE;
     "do",          DO;
     "else",        ELSE;
     "emp",         EMPTY;
     "ensures",     ENSURES;
     "if",          IF;
     "interfere",   INTERFERE;
     "invariant",   INVARIANT;
     "let",         LET;
     "new",         NEW;
     "par",         PAR;
     "requires",    REQUIRES;
     "resource",    RESOURCE;
     "return",      RETURN;
     "then",        THEN;
     "void",        VOID;
     "when",        WHEN;
     "while",       WHILE;
     "with",        WITH;
     "true" ,       BOOL true;
     "false",       BOOL false;
     "NULL",        NAT 0;
		 "qualif",      QUALIF;
     "squalif",     SINGLE_QUALIF;
		 "purespec",    PURESPEC;
		 "effspec",     EFFSPEC;
		 "setspec",     SETDECL;	
		 "thread_desc", TDESC;
		]

(* To store the position of the beginning of a string and comment *)
let string_start_loc = ref Location.none;;
let comment_start_loc = ref [];;
let in_comment () = !comment_start_loc <> [];;

let lexbuf_stack = ref []

(* Update the current location with absolute line number. *)
let update_currentline lexbuf line =
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_lnum = line }

(* Update the current location with file name. *)
let update_fname lexbuf fname =
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fname }

let update_newline lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with 
        pos_lnum = pos.pos_lnum + 1;
        pos_bol = pos.pos_cnum; }

(* Initialize file name and starting position *)
let init lexbuf fname =
  Location.lexbuf := Some lexbuf;
  update_fname lexbuf fname;
  update_currentline lexbuf 1;
  lexbuf.lex_start_p <- lexbuf.lex_curr_p

(* Initialize file name and starting position *)
let init_fname fname =
  let lexbuf = Lexing.from_channel (open_in fname) in
  Location.lexbuf := Some lexbuf;
  update_fname lexbuf fname;
  update_currentline lexbuf 1;
  lexbuf.lex_start_p <- lexbuf.lex_curr_p;
  lexbuf

let init_stdin () =
  let lexbuf = Lexing.from_channel stdin in
  Location.lexbuf := Some lexbuf;
  update_fname lexbuf "<stdin>";
  update_currentline lexbuf 1;
  lexbuf.lex_start_p <- lexbuf.lex_curr_p;
  lexbuf

let parse_eof k = 
  match !lexbuf_stack with 
    | [] -> EOF
    | b::l -> 
        Location.lexbuf := Some b;
        lexbuf_stack := l;
        k b

}
(* regular expressions *)

let newline = ('\010' | '\013' | "\013\010")
let blank = [' ' '\009' '\012']
let letter = ['A'-'Z' '_' 'a'-'z']
let digit = ['0'-'9']
let alphanum = digit | letter
let ident = letter alphanum*
let qident = '_' ident
let fident = '@' ident
let num = digit+
let str = '"' ([^'"' '\013' '\010'] | "\\\"")* '"'

(* entry points *)

rule token = parse
  | newline { update_newline lexbuf; token lexbuf }
  | blank   { token lexbuf }
  | '#'     { hash lexbuf }
  | "//" [^ '\010' '\013']* newline 
	  { update_newline lexbuf; token lexbuf }
  | "/*"  { comment_start_loc := [lexbuf.lex_curr_p];
            comment lexbuf;
            token lexbuf }
  | "|->" { POINTSTO }
  | ","   { COMMA }
  | "{"   { LBRACE }
  | "["   { LBRACKET }
  | "("   { LPAREN }
  | "->"  { MINUSGREATER }
  | "}"   { RBRACE }
  | "]"   { RBRACKET }
  | ")"   { RPAREN }
  | ";"   { SEMI }
  | "&&"  { AMPERAMPER }
  | "||"  { BARBAR }
  | ":"   { COLON } 
  | "="   { EQUAL }
  | "!"                     { UNARYOP(Lexing.lexeme lexbuf) }
  | "==" | "!=" 
  | "<" | "<=" | ">" | ">=" { INFIXOP1(Lexing.lexeme lexbuf) }
  | "+" | "-"               { INFIXOP2(Lexing.lexeme lexbuf) }
  | "/" | "%" | "^"         { INFIXOP3(Lexing.lexeme lexbuf) }
  | "*"    { STAR }
  | "."    { DOT }
	| "~"    { TILDE }
	| "{<"   { LBRACELESS }
  | ">}"   { GREATERRBRACE }
	| "@"    { WILD }
	| "<<"   { IN }
	| "++"   { UNION }
	| "::"   { CONCAT }
	| "$$"   { REC }
	| "=>"   { IMPLIES }
  | num    { NAT(int_of_string(Lexing.lexeme lexbuf)) }
  | ident  { let s = Lexing.lexeme lexbuf in
             try Hashtbl.find keyword_ht s
             with Not_found -> IDENT(s) }
  | qident { QIDENT(Lexing.lexeme lexbuf) }
  | fident { FIDENT(Lexing.lexeme lexbuf) }
  | str    { let s = Lexing.lexeme lexbuf in
	     STRING (String.sub s 1 (String.length s - 2)) }
  | eof    { parse_eof token }
  | _ { raise(Location.Parse_error 
		("Illegal character (" ^ Char.escaped (Lexing.lexeme_char lexbuf 0) ^ ").",
		 Location.mkloc(lexbuf.lex_start_p) (lexbuf.lex_curr_p))) }

and comment = parse
    "/*" { comment_start_loc := lexbuf.lex_curr_p :: !comment_start_loc;
           comment lexbuf }
  | "*/" { match !comment_start_loc with
             | [] -> assert false
             | [_] -> comment_start_loc := [];
             | _ :: l -> comment_start_loc := l; comment lexbuf }
  | eof { match !comment_start_loc with
            | [] -> assert false
            | loc :: _ -> comment_start_loc := [];
		raise(Location.Parse_error
			("Unterminated comment.",
			 Location.mkloc loc (lexbuf.lex_curr_p))) }
  | newline { update_newline lexbuf; comment lexbuf }
  | _       { comment lexbuf }

(* # <line number> <file name> ... *)
and hash = parse
    newline  { update_newline lexbuf; token lexbuf}
  | blank    { hash lexbuf}
  | num      { let s = Lexing.lexeme lexbuf in
               update_currentline lexbuf (int_of_string s - 1);
               file lexbuf }
(*  | "include" blank+ (str as fname)
             { lexbuf_stack := lexbuf :: !lexbuf_stack;
               let f = (String.sub fname 1 ((String.length fname) - 2)) in
               let newbuf =
                 try init_fname (Filename.concat (Filename.dirname lexbuf.lex_start_p.pos_fname) f)
                 with Sys_error _ ->
                 try init_fname f
                 with Sys_error s -> raise (Location.Parse_error
                   (s, Location.mkloc(lexbuf.lex_start_p) (lexbuf.lex_curr_p)))
               in
               token newbuf }
*)
  | _ { raise(Location.Parse_error 
		("Illegal character (" ^ Char.escaped (Lexing.lexeme_char lexbuf 0) ^ ") after #. Line number expected.",
		 Location.mkloc(lexbuf.lex_start_p) (lexbuf.lex_curr_p))) }

and file =  parse 
    newline  { update_newline lexbuf; token lexbuf }
  | blank    { file lexbuf }
  | str      { let n = Lexing.lexeme lexbuf in
               update_fname lexbuf (String.sub n 1 ((String.length n) - 2));
               endline lexbuf }
  | _        { endline lexbuf }

and endline = parse 
    newline  { update_newline lexbuf; token lexbuf }
  | eof      { parse_eof token }
  | _        { endline lexbuf }

{ (* trailer *)
}
