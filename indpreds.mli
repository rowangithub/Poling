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

(** User-defined inductive predicates *)
open Exp
open Assertions

(** User-defined predicates are ported over from Smallfoot, 
    but do not currently work because of the new assertion
    normalization implementation. *) 

exception Indpred_error of string * Location.t

(** Internal representation of inductive predicates *)
type ip_decl =
    {ip_id: string;
     ip_args: Id.t list;
     ip_body: (Pure.t * cform) list;
     ip_node: bool;
     ip_loc: Location.t}

(** Raises [Indpred_error] if an error occurs *)
val add_ip_decl : ip_decl -> unit

(** Raises [Indpred_error] if an error occurs *)
val check_ip_uses : unit -> unit

val instance_ip_lhs : string * exp list -> (Pure.t * cform) list
val instance_ip_rhs : string * exp list -> (Pure.t * cform) list
val init_ip_env : unit -> unit
val print_ip_env : Format.formatter -> unit

val add_ip_use : string * int * Location.t -> unit

(** unroll a node declaration in the lhs *) 
val unroll_node_lhs: 
  Misc.component -> exp ->
  exp * exp * Misc.component * Fld.t * Pure.t

(** unroll a node declaration in the rhs *)
val unroll_node_rhs: 
  Misc.component -> exp ->
  exp * exp * Misc.component * Fld.t * Pure.t
