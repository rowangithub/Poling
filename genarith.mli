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
(** Generation of arithmetic programs *)
open Exp
open Assertions

(** This module provides helper routines for generating arithmetic programs
    out of separation logic proofs following the work of Magill et al.
    Arithmetic program generation is turned off by default because it places a
    heavy burden on the garbage collector and, moreover, the generated programs
    are huge (mainly because the RGSep proof objects are huge). 
 *)

(** Is arithmetic program generation enabled? *)
val enabled : unit -> bool

val args : (Arg.key * Arg.spec * Arg.doc) list

(* -------------------------------------------------------------------------- *)
(** {2 Graphs} *)
(* -------------------------------------------------------------------------- *)

(** Nodes *)
type ga_node

(** Create a new node *)
val new_node : cform -> ga_node

(** Put an edge from [n1] to [n2] *)
val put_edge_skip : ga_node -> ga_node -> unit

(** Put an edge from [n1] to [n2] *)
val put_edge_implication : ga_node -> subst -> Pure.t -> ga_node -> unit

(** Pretty print the generated integer program reachable from a node *)
val pp_function : Format.formatter -> string * ga_node -> unit

(* -------------------------------------------------------------------------- *)
(** {2 Extended assertions} *)
(* -------------------------------------------------------------------------- *)

type eform = ga_node
type eprop = eform list

val cform_of_eform : eform -> cform

(** Generic constructor: create a new node for each disjunct *)
val eprop_of_cprop : cprop -> eprop

val eprop_of_cprop_at_start_node : cprop -> (ga_node * eprop)

val eprop_false : eprop
val eprop_star : cprop -> eprop -> eprop
val eprop_star_assume : cprop -> eprop -> eprop
val eprop_or   : eprop -> eprop -> eprop

val ext_append_return  : eprop -> unit
val ext_append_comment : (unit -> string) -> eprop -> eprop
val ext_append_assign  : (Id.t * exp option) list -> eprop -> eprop
val ext_append_case_split : eprop -> eprop * eprop

val ext_opt_transform1 : (cform -> cform list option) -> eform -> eform list option
val ext_transform : (cform -> cprop) -> eprop -> eprop

(** Remove syntactically identical disjuncts (and add edges to the
    generated arithmetic program where necessary). *)
val remove_eform_duplicates : eform list -> eform list

val map_eprop : (exp -> exp) -> eprop -> eprop
val naive_map_eprop : (exp -> exp) -> eprop -> eprop

val pp_eprop : Format.formatter -> eprop -> unit


(* -------------------------------------------------------------------------- *)
(** {2 Abstraction interface} *)
(* -------------------------------------------------------------------------- *)

(** Abstract domain corresponding to a disjunction of [uform]s for
    calculating fix-points.

    NB: The two components of [udom] are to work round the possible
    non-transitivity of the prover's entailment checking.
 *)
type udom = uform list * uform list

    
val udom_of_uform_list : uform list -> udom
val uform_list_of_udom : udom -> uform list

(** Interface provided by the abstraction module:
    - [uform_abs] is the analogue of [prop_abs] for formulas with no boxes. 
      See below.
      The boolean argument tells whether the abstraction should be aggressive
      (disregard sentinel values).
    - [uform_join] is the analogue of [prop_join] for formulas with no boxes. 
      See below.
    - [prop_abs cp] returns a [cp'] belonging to a smaller domain such that 
      [cp |- cp']
    - [prop_join cp1a cp1b cp2] assumes that [cp1a <==> cp1b] and returns 
    [(cpa,cpb,cp2')] such that [cpa <==> cpb] 
    and [cp1a |- cpa] and [cp2' |- cpa]
    and [(cp1b \/ cp2) ==> cpb] 
    and [cpb ==> (cp1b \/ cp2')]
*)
type abstraction =
  {
     uform_abs : bool -> uform list -> uform list;
     uform_join : udom -> uform list -> udom * uform list;
     prop_abs : eprop -> eprop;
     prop_join : eprop -> eprop -> eprop -> 
                  (eprop * eprop * eprop);
  }


