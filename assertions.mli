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
(** Separation logic assertions (symbolic heaps) *)

open Misc
open Parsetree
open Exp

(** 
  This module defines:
    - the internal representation of assertions & actions
    - constructors for such assertions
    - common operations (free variables, substitution, basic simplification)
    - interference computation (generalization of septraction)
    - the theorem prover interface

  TODO: Only |->'s and singly-linked lists are implemented properly.
  Doubly-linked lists and user-defined predicates are not.
*)

(** Kind of link for linked lists *)
type link_kind = 
  | SINGLE of component * Fld.t (** Node name, common fields *)
  | DOUBLE of component * component 
  | XOR of component

type can_isemp = 
  | Cem_PE (** possibly empty *) 
  | Cem_NE (** definitely non-empty *)

(** Tags for spatial predicates.
    (These are for internal use in this module only: use the default tag
     constructor, [default_tag], to get a tag.) *)
type tag

(** Canonical heap predicate.

  NB: Unlike Smallfoot, the list segments of CAVE ([Csp_listsegi]) are 
  "imprecise".  For justification, read the SAS 2007 paper on SmallfootRG.
 *)
type can_spred =
  | Csp_listsegi of tag * link_kind * exp * exp
                    * exp * exp * can_isemp * Dset.t
  | Csp_arr  of tag * exp * exp * exp * Fld.t * can_isemp * Dset.t
  | Csp_node of tag * component * exp * Fld.t
  | Csp_indpred of tag * string * exp list

(** Star-conjunction of heap predicates *)
type can_spatial = can_spred list

(** Canonical formulas without boxes *)
type uform = Pure.t * can_spatial

(** Canonical formulas with boxes *)
type cform = uform * (component, cprop) plist

(** Canonical proposition: disjunction of canonical formulas *)
and cprop = cform list

(** Type of RGSep actions used for interference calculations *)
type act

exception No_frame_found
exception Junk

(** {3 Operations on spatial formulas} *)
(* -------------------------------------------------------------------------- *)


val tag_default : tag

val spred_fold : (exp -> 'a -> 'a) -> can_spred -> 'a -> 'a

val spat_empty : can_spatial
val spat_one : can_spred -> can_spatial
val spat_star_one : can_spred -> can_spatial -> can_spatial
val spat_star : can_spatial -> can_spatial -> can_spatial
val spat_remove : can_spatial -> can_spred -> can_spatial
val spat_fold : (exp -> 'a -> 'a) -> can_spatial -> 'a -> 'a
val spat_fold_spred : (can_spred -> 'a -> 'a) -> can_spatial -> 'a -> 'a
val spat_get : exp -> can_spatial -> (can_spred * can_spatial) option

val compare_can_spred : can_spred -> can_spred -> int
val abs_compare_can_spred : can_spred -> can_spred -> int

val flatten_condition : cprop -> cprop list

(** {3 Constructors} *)
(* -------------------------------------------------------------------------- *)

val uform_false : uform
val cform_false : cform
val cprop_false : cprop

val uform_empty : uform
val cprop_empty : cprop
val is_cprop_empty : cprop -> bool
val cprop_pure: Pure.t -> cprop
val cprop_spred: can_spatial -> cprop
val cprop_uform: uform -> cprop
val cprop_cform: cform -> cprop

val mk_array : tag -> exp -> exp -> exp -> Fld.t -> Dset.t -> uform -> uform

(** [cform_star cf1 cf2] may return [None] if the result is inconsistent *)
val cform_star: cform -> cform -> cform option

val cprop_star: cprop -> cprop -> cprop
val and_cprop_pure : cprop -> Pure.t -> cprop
val cprop_or: cprop -> cprop -> cprop

val cprop_box: component -> cprop -> cprop

(** Removes duplicates and combines boxes *)
val aggr_remove_cform_duplicates: cprop -> cprop

(** {3 Comparisons} *)
(* -------------------------------------------------------------------------- *)

val compare_uform : uform -> uform -> int
val compare_cform : cform -> cform -> int
val compare_cprop : cprop -> cprop -> int
val compare_component_cprop : component * cprop -> component * cprop -> int

val remove_uform_duplicates : uform list -> uform list
val remove_cform_duplicates : cform list -> cform list

val can_spred_leq : can_spred -> can_spred -> exp

(** {3 Free variables} *)
(* -------------------------------------------------------------------------- *)

val uform_fhd : uform -> IdSet.t -> IdSet.t

(** Return the free variables of a spatial predicate *)
val spred_fv : can_spred -> IdSet.t -> IdSet.t
val spred_exfv : can_spred -> IdSet.t -> IdSet.t

(** Return the free variables of an assertion *)
val prop_fv : cprop -> IdSet.t -> IdSet.t

(** Return the non-existential free variables of an assertion *)
val fv_norm_cprop : cprop -> IdSet.t

(** Return the existential free variables of an assertion *)
val prop_exfv : cprop -> IdSet.t -> IdSet.t

val form_exfv : cform -> IdSet.t -> IdSet.t

(** Returns existential free variables in a canonical order *)
val abs_fv_uform : uform -> Id.t list

(** {3 Substitutions} *)
(* -------------------------------------------------------------------------- *)

val map_spat : (exp -> exp) -> can_spatial -> can_spatial
val map_uform : (exp -> exp) -> uform -> uform list
val map_cform : (exp -> exp) -> cform -> cprop
val map_cprop : (exp -> exp) -> cprop -> cprop
val map_ip_body : (exp -> exp) -> (Pure.t * cform) list -> (Pure.t * cform) list

val naive_map_cform : (exp -> exp) -> cform -> cform

(** {3 Normalization} *)
(* -------------------------------------------------------------------------- *)

val form_kill_hd_vars : cform -> cform

val prop_kill_can_return : cprop -> cprop

val normalize_uform : uform -> uform list

val normalize_cform : cform -> cprop

val normalize_cform_aggr : cform -> cprop

val normalize_cprop : cprop -> cprop

val kill_garbage_vars : cprop -> cprop
val kill_garbage_vars_ufl : uform list -> uform list
val aggr_kill_garbage_vars : cprop -> cprop

(** Kill the variables of [cp] that are not directly reachable from the set [s]
*)
val kill_dead_vars : IdSet.t -> cprop -> cprop


(* -------------------------------------------------------------------------- *)
(** {2 Theorem prover interface} *)
(* -------------------------------------------------------------------------- *)

(** Interface provided by the theorem provers:
     - [find_ptsto] and [expose_ptsto]: used by symbolic execution, but should
       be removed.
     - [nf_cprop sl_context eq cp = cp'] where [cp'] is a normal form
       of [cp].
     - [nf_cform cf] returns [cprop_false] if [cf] is inconsistent, 
       or [cp'] such that [cf <==> cp'] and
       [nf_cprop [] empty_eq cp' = cp']
     - [entails_cprop cp cp'] returns [inst] if [cp * inst |- cp']
     - [find_frame_cprop fr cp1 cp2] returns [res] such that [cp1 |- cp2 * res]
       in context [fr]
       (i.e. for all [R], [(fr /\ R) * cp1 |- (fr /\ R) * cp2 * res])
       or raises [No_frame_found]
 *)
type prover =
   { find_ptsto : Misc.component -> exp -> can_spatial -> Fld.t * can_spatial
   ; expose_ptsto : cprop -> exp -> cprop
   ; nf_cprop :  can_spatial -> cprop -> cprop
   ; nf_cform : cform -> cprop
   ; entails_cprop : cprop -> cprop -> Pure.t list
   ; find_frame_cprop : can_spatial -> cprop -> cprop -> cprop
   ; adv_entails_atom : cprop -> exp -> bool
   }

(* -------------------------------------------------------------------------- *)
(** {2 Actions} *)
(* -------------------------------------------------------------------------- *)

(** Create a new set of actions: [new_acts name ctx pre post] *)
val new_acts : string -> cprop -> cprop -> cprop -> act list

(** Return the name of an action *)
val act_name : act -> string

(** [interfere_once prover act cp] calculate the effect of applying
    interference [act] to [cp]. *)
val interfere_once: prover -> act -> cprop -> cprop

(* -------------------------------------------------------------------------- *)
(** {2 Pretty printing} *)
(* -------------------------------------------------------------------------- *)

val pp_spred : Format.formatter -> can_spred -> unit
val pp_uform : Format.formatter -> uform -> unit
val pp_cform : Format.formatter -> cform -> unit
val pp_cprop : Format.formatter -> cprop -> unit
val pp_act : Format.formatter -> act -> unit

(* -------------------------------------------------------------------------- *)
(** {2 Configuration parameters} *)
(* -------------------------------------------------------------------------- *)

val allow_leaks : bool ref

val args : (Arg.key * Arg.spec * Arg.doc) list
