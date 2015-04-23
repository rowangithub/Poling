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

type t = 
  { file: string 
  ; line: int 
  ; end_line: int 
  ; start_char: int 
  ; end_char: int
  }

exception Parse_error of string * t

let none = 
  { file = ""
  ; line = 0
  ; end_line = 0
  ; start_char = 0
  ; end_char = 0
  }

let mkloc s e =
  { file = e.pos_fname
  ; line = s.pos_lnum
  ; end_line = e.pos_lnum
  ; start_char = s.pos_cnum - s.pos_bol
  ; end_char = e.pos_cnum - s.pos_bol
  }

let symbol_loc () = 
  mkloc (Parsing.symbol_start_pos()) (Parsing.symbol_end_pos())

let rhs_loc n = 
  mkloc (Parsing.rhs_start_pos n) (Parsing.rhs_end_pos n)

let sprint loc = 
  if loc == none then ""
  else if loc.line == loc.end_line then 
    Format.sprintf "File \"%s\", line %i, characters %i-%i:@."
      loc.file loc.line loc.start_char loc.end_char
  else 
    Format.sprintf "File \"%s\", lines %i-%i, characters %i-%i:@."
      loc.file loc.line loc.end_line loc.start_char loc.end_char

let lineno_to_string loc = 
  if loc == none then "???" else string_of_int loc.line
	
let lineno_to_int loc = 
	if loc == none then 0 else loc.line	

let print fmt loc = Format.pp_print_string fmt (sprint loc)

let lexbuf : Lexing.lexbuf option ref = ref None
