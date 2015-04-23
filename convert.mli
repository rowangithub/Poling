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
(** Translate parse tree into the intermediate abstract syntax tree *)
open Misc
open Parsetree
open Exp
open Assertions
open Commands

exception Undef_non_pure_expression 
exception Conversion_error of string * Location.t

(** Convert a [p_expression] to a [exp]. 
    Throws [Undef_non_pure_expression] if the expression contains indirections.
*)
val convert_exp : p_expression -> exp

(** [convert_exp_se pe stmts] returns the read side-effects required for
   the indirections in [pe] and a {!exp} representing [pe] *)
val convert_exp_se : 
  component list -> p_expression -> can_stmt list -> can_stmt list * exp

(** [convert_exp_list_se pel stmts] returns the read side-effects
   required for the indirections in [pel] and a {!exp list} representing
   [pel] *) 
val convert_exp_list_se :
  component list -> p_expression list -> can_stmt list -> can_stmt list * exp list

(** [convert_assume_exp e] returns the statements required to evaluate 
   [assume e] and [assume (not e)]. *)
val convert_assume_exp : component list -> p_expression -> can_stmt list * can_stmt list

val convert_prop : a_proposition -> Location.t -> cprop
val prop_to_ip_body : a_proposition -> Location.t -> (Pure.t * cform) list 

