(* Poling: Proof Of Linearizability Generator 
 * Poling is built on top of CAVE and shares the same license with CAVE 
 * See LICENSE.txt for license.
 * Contact: He Zhu, Department of Computer Science, Purdue University
 * Email: zhu103@purdue.edu
 *)

(**
   This module implements our main algorithm based on CAVE
	 Read qualifiers from file
	 Qulifier Elimination 
*)

open Assertions
open Genarith
open Exp
open Misc


(**********************************************************)
(***************** Shape Qualifier API ********************)
(**********************************************************)

(** Load user provided shape predicate from given qualifier file *)
val convert : Parsetree.a_proposition -> cform list

val compare : (Misc.component, cform list) Hashtbl.t -> (Misc.component, cform list) Hashtbl.t -> bool

(** Qualifier elimination: use prover to select qualifiers that overapproximates intermediate state *)
val eliminate1 : prover -> (Misc.component, cform list) Hashtbl.t -> eprop -> 
									(Misc.component, cform list) Hashtbl.t
									
val eliminate_inplace : prover -> (Misc.component, cform list) Hashtbl.t -> eprop -> unit

val eliminate : prover -> cform list -> eprop -> eprop

val subtract : prover -> cform list -> cform list -> cform list

val subtract1 : prover -> cform list -> cform list -> bool

(** Qualifiers should be instantiated by context variables before use *)
val instantiate: cform list -> IdSet.t -> cform list

(** Expand user provided cform to cprop *)
val expand_shape_qualifier : cform -> cform list

(**********************************************************)
(***************** Pure Qualifier API *********************)
(**********************************************************)

type pure_qualifier_t = string * string * Predicate.t

val transl_pure_qualifiers : Parsetree.qualifier_declaration list -> pure_qualifier_t list

val print_pure_qual : pure_qualifier_t -> unit

(**********************************************************)
(***************** Specification API **********************)
(**********************************************************)

type spec_t = string * Predicate.t

val transl_specifications : Parsetree.specification_declaration list -> spec_t list

val print_spec : spec_t -> unit

(** Intepretation of specification:
 Idea: map  *)

