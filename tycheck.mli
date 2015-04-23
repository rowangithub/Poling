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
(******************************************************************************)(** Type checking & conversion into command language *)
open Assertions
open Commands

(** Returns 
    [(globals, fun_specifications, resources, res_initializers, fun_proofs)] *)
val convert : Parsetree.p_item list -> 
  string list *
  Misc.StringSet.t *
  Exp.IdSet.t *
  (string, fun_info) Hashtbl.t *  
  (Misc.component, act list) Hashtbl.t * 
	(Misc.component, Predicate.t) Hashtbl.t *
  (Misc.component * res_init) list * 
  (string * can_entailment) list *
	(string * Predicate.t) option
