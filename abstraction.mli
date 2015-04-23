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

(** Shape abstraction of assertions 
  * We do not perform value abstraction
	*)

(** 
   The original imported from CAVE module implements shape-value abstraction, 
	 which includes an adaptation of Distefano's simple list segment domain and 
	 custom abstractions for possibly sorted sequences and multiset values.

   References:
    - Vafeiadis, V.: Shape-value abstraction for verifying linearizability. 
      In: Jones, N.D., Mueller-Olm, M. (eds.) VMCAI 2009.
      LNCS, vol. 5403, pp. 335-348. Springer, Heidelberg (2009)
    - Distefano, D., O'Hearn, P.W., Yang, H.: A local shape analysis based
      on separation logic. In: Hermsnnd, H., Palsberg, J. (eds.) TACAS 2006.
      LNCS, vol. 3920, pp. 287-302. Springer, Heidelberg (2006)

	 Our adaptation only targets on shape abstraction.
	 Our implementation is more like a separation logic prover which delay
	 the value analysis to heap theorem prover. See the following referenee:
	 References:
	  - Madhusudan, P., Qiu, X., Stefanescu, A.: Recursive Proofs for 
		  Inductive Tree Data-structures. In Proc. 39th ACM SIGPLAN-SIGACT 
			Symposium on Principles of Programming Languages (POPL '12), 2012.
 *)

val mk_abstraction : Assertions.prover -> Genarith.abstraction
  (** Main entry point. *)

val mk_abs_set_sub : Exp.IdSet.t -> Exp.exp list list -> Exp.subst
  (** Return a substitution that abstracts set values in the assertion. *)

val mk_abs_list_sub : Exp.exp list list -> Exp.subst
  (** Return a substitution that abstracts list values in the assertion. *)

(* -------------------------------------------------------------------------- *)
(** {2 Configuration parameters & statistics} *)
(* -------------------------------------------------------------------------- *)

val prover_calls : int ref
  (** Number of calls to the theorem prover during abstraction *)

val verbose : int ref

val args : (Arg.key * Arg.spec * Arg.doc) list
