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
(** Symbolic execution *)

(** This module implements symbolic execution for RGSep assertions 
    with and without action inference, and a linearizability verifier.

    References:
     - Vafeiadis, V.: Automatically proving linearizability.
       In: CAV 2010. Springer, Heidelberg (2010)
     - Vafeiadis, V.: RGSep action inference. In: Barthe, G., Hermenegildo, M.
       (eds.) VMCAI 2010.
       LNCS, vol. 5944, pp. 345-361. Springer, Heidelberg (2010)
     - Calcagno, C., Parkinson, M., Vafeiadis, V.: Modular safety checking for 
       fine-grained concurrency. In: Riis Nielson, H., File, G. (eds.) SAS 2007. 
       LNCS, vol. 4634, pp. 233-248. Springer, Heidelberg (2007)
 *)

(** Check validity of program specifications. *)
val check_props : 
  Assertions.prover -> Genarith.abstraction ->
  string list *
  Misc.StringSet.t *
  Exp.IdSet.t *
  (string, Commands.fun_info) Hashtbl.t *
  (Misc.component, Assertions.act list) Hashtbl.t *
	(Misc.component, Predicate.t) Hashtbl.t * 
  (Misc.component * Commands.res_init) list *
  (string * Commands.can_entailment) list *
	(string * Predicate.t) option ->
	Assertions.cform list (** user provided shape qualifiers *) ->
	Qualifier.pure_qualifier_t list (** user provided pure qualifiers *) -> bool 

(* -------------------------------------------------------------------------- *)
(** {2 Configuration parameters & statistics} *)
(* -------------------------------------------------------------------------- *)

val stabilisation_iterations: int ref
  (** Total number of iterations for all the calls to [mk_stable_single] *)

val verbose : int ref
val infer : int ref

(** if shape qualifiers are given *)
val qs_given : bool ref
(** if pure qualifiers are given *)
val ps_given : bool ref

val inv_given : bool ref

val args : (Arg.key * Arg.spec * Arg.doc) list
