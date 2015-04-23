(* Poling: Proof Of Linearizability Generator 
 * Poling is built on top of CAVE and shares the same license with CAVE 
 * See LICENSE.txt for license.
 * Contact: He Zhu, Department of Computer Science, Purdue University
 * Email: zhu103@purdue.edu
 *)

open Format
open Exp

type binop =
    Plus
  | Minus
  | Times
  | Div

type binrel =
    Eq
  | Ne
  | Gt
  | Ge
  | Lt
  | Le 

type patpexpr =
    PPInt of int list
  | PVar of Id.t list
  | PFunApp of string * patpexpr list 
  | PBinop of patpexpr * binop list * patpexpr
  | PField of string * patpexpr
  | PProj of int * patpexpr
	| PUnion of patpexpr * patpexpr 
	| PConcat of patpexpr * patpexpr

type tpat =
    PTrue
  | PAtom of patpexpr * binrel list * patpexpr
  | PIff of patpexpr * tpat
  | PNot of tpat
  | PAnd of tpat * tpat
  | POr of tpat * tpat
	| PIn of patpexpr * patpexpr
	| PRecpred of string * patpexpr

type pexpr =   
    PInt of int 
  | Var of Id.t
  | FunApp of string * pexpr list (* Support both uninterpreted function and recursive function  *)
  | Binop of pexpr * binop * pexpr 
  | Field of string * pexpr     (* INVARIANT: disjoint fields in same module *)
  | Proj of int * pexpr
	| Union of pexpr * pexpr (* Support set union operation *)
	| Concat of pexpr * pexpr (* Support concatation operation *)

type t =  
    True
  | Atom of pexpr * binrel * pexpr 
  | Iff of pexpr * t
  | Not of t
  | And of t * t 
  | Or of t * t
	| In of pexpr * pexpr (* Support set in operation *)
	| Recpred of string * pexpr (* Support recursive predicate *)

exception Unfold_ex

val pprint_rel: binrel -> string
val pprint: formatter -> t -> unit
val pprint_pexpr: formatter -> pexpr -> unit

val big_and: t list -> t
val big_or: t list -> t
val equals: (pexpr * pexpr) -> t
val implies: (t * t) -> t
val int_true: pexpr
val int_false: pexpr
val expand_iff: t -> t

val (==.): pexpr -> pexpr -> t
val (!=.): pexpr -> pexpr -> t
val (<=.): pexpr -> pexpr -> t
val (<.): pexpr -> pexpr -> t
val (>=.): pexpr -> pexpr -> t
val (>.): pexpr -> pexpr -> t
val (&&.): t -> t -> t
val (||.): t -> t -> t
val (!.): t -> t
val (=>.): t -> t -> t
val (<=>.): pexpr -> t -> t
val (+-): pexpr -> pexpr -> pexpr
val ( *-): pexpr -> pexpr -> pexpr
val ( /-): pexpr -> pexpr -> pexpr
val (--): pexpr -> pexpr -> pexpr
val (?.): pexpr -> pexpr -> t (* Ask if px is \in qx *)

val subst: pexpr -> Id.t -> t -> t
val apply_substs: (Id.t * pexpr) list -> t -> t
val vars: t -> Id.t list

val map_fields : (string -> string) -> t -> t
val map_vars : (Id.t -> pexpr) -> t -> t

val instantiate_named_vars: (string * Id.t) list -> t -> t

(** Flatten the Union elmements *)
val flatten_union: pexpr -> pexpr list
val flatten_and: t -> t list

val transl_op: Parsetree.predexp_op -> binop                                                             
val transl_rel: Parsetree.pred_rel -> binrel

(** unfolding based on separation logic formula *)
val unfold_recursive_defnition : t -> (string -> pexpr -> pexpr) -> (string -> pexpr -> t) 
																		-> (pexpr -> pexpr) -> t

val transl_pexp : Exp.exp -> pexpr

val transl_pred : Exp.exp -> t

val transl_exp : pexpr -> Exp.exp

val transl_subs : t -> subst

val is_concat_pred : t -> bool

val transl_concat_union : t -> t