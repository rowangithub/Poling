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
(** Operations on pure formulae *)
open Misc
open Exp

(** The type of non-disjunctive pure formulae *)
type t

val compare : t -> t -> int


(** {3 Constructors} *)
(* -------------------------------------------------------------------------- *)

val ptrue : t
val pfalse : t
val one : exp -> t
val conj_one : exp -> t -> t 
val conj : t -> t -> t


(** {3 Tests} *)
(* -------------------------------------------------------------------------- *)

val is_true : t -> bool
val is_sat : t -> bool
val is_false : t -> bool
val has_unsat_eq : t -> bool
val has_neql : t -> bool

(** If this returns [true] then [pure1.eq == pure2.eq]. *)
val identical_eq : t -> t -> bool

(** {3 Destructors} *)
(* -------------------------------------------------------------------------- *)

val to_exp : t -> exp
val to_sub : t -> subst

val only_inst_eqs : t -> t
val remove_eqs : t -> t

(** {3 Free variables / substitutions} *)
(* -------------------------------------------------------------------------- *)

val no_s : string -> t -> bool

val fv : t -> IdSet.t -> IdSet.t
val exfv : t -> IdSet.t -> IdSet.t
val fhd : t -> IdSet.t -> IdSet.t
val map : (exp -> exp) -> t -> t

(** Return a weaker assertion that does not mention the killed variables. *)
val kill_vars : IdSet.t -> t -> t

(** Return a weaker assertion that does not have any [can_return]s. *)
val kill_can_return : t -> t


(** {3 Pure prover} *)
(* -------------------------------------------------------------------------- *)

val normalize : t -> t list

val normalize_aggr : t -> t list

(** [entails_exp pl e] returns [true] if [pl |- e]. *)
val entails_exp : t -> exp -> bool

(** Find a simpler [pl3] such that [pl1 |- pl3] iff [pl1 |- pl2]. *)
val simplify : t -> t -> t

(** [entails pl pl'] returns [true] if [pl |- EX exfv(pl'). pl']. *)
val entails : t -> t -> bool


(** {3 Other operations} *)
(* -------------------------------------------------------------------------- *)

val eq_length : t -> int
val fold : (exp -> 'a -> 'a) -> t -> 'a -> 'a
val filter : (exp -> bool) -> t -> t

val has_can_return : t -> bool

(** [common p1 p2 = p] such that [p1 => p] and [p2 => p]. *)
val common : t -> t -> t

val mcpa_common : t -> t -> t

(** Return the list of equalities between set expressions
    in the pure formula. *)
val get_set_eqs : t -> (exp list * exp list) list

(** Returns the set of expresssions that are not equal to e in pl *)
val get_uneql : exp -> t -> Dset.t

(** Pretty-print a pure assertion *)
val pp : Format.formatter -> t -> unit


(** {3 Disjunctive pure assertions} *)
(* -------------------------------------------------------------------------- *)

val list_conj : t list -> t list -> t list
val lifted_list_conj : t list -> (unit -> t list) 
  -> t list
	



