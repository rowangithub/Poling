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
(** Source file locations (for error messages) *)
open Lexing

type t 

exception Parse_error of string * t

val none : t
val mkloc : Lexing.position -> Lexing.position -> t
val symbol_loc : unit -> t
val rhs_loc : int -> t

val sprint : t -> string
val lineno_to_string : t -> string

val print : Format.formatter -> t -> unit
val lexbuf : Lexing.lexbuf option ref

val lineno_to_int : t -> int
