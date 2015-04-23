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

(** Must-subtraction implementation *)
open Exp
open Assertions

(** This module implements the Must-subtraction algorithm, also known as
    frame inference, which is a generalization of entailment checking.

    For efficiency purposes, the implementation differs substantially from
    (Berdine, Calcagno, O'Hearn, 2005). 
*)

val default_prover : prover

val verbose : int ref
val args : (Arg.key * Arg.spec * Arg.doc) list
