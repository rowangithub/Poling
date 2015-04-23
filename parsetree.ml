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
open Misc

type p_type = string

(** // MCPA takes user specifications & qualifiers into verification *)

(* Predicate Declaration *)

type predicate_pattern =
    { ppredpat_desc: predpat_desc;
      ppredpat_loc: Location.t }

and predpat_desc =
    Ppredpat_true
  | Ppredpat_atom of predpatexp * pred_rel list * predpatexp
  | Ppredpat_not of predicate_pattern
  | Ppredpat_and of predicate_pattern * predicate_pattern
  | Ppredpat_or of predicate_pattern * predicate_pattern
	| Ppredpat_in of predpatexp * predpatexp
	| Ppredpat_predrec of string * predpatexp

and predpatexp =
  { ppredpatexp_desc: predpatexp_desc;
    ppredpatexp_loc: Location.t }

and predpatexp_desc =
    Ppredpatexp_int of int list
  | Ppredpatexp_any_int              
  | Ppredpatexp_var of string list
  | Ppredpatexp_mvar of string
  | Ppredpatexp_funapp of string * predpatexp list
  | Ppredpatexp_binop of predpatexp * predexp_op list * predpatexp
  | Ppredpatexp_field of string * predpatexp
  | Ppredpatexp_proj of int * predpatexp
	| Ppredpatexp_union of predpatexp * predpatexp
	| Ppredpatexp_concat of predpatexp * predpatexp

and pred_rel = Pred_eq | Pred_ne | Pred_gt | Pred_lt | Pred_le | Pred_ge

and predexp_op = Predexp_plus | Predexp_minus | Predexp_times | Predexp_div

(* Qualifier declarations *)

and qualifier_declaration = string * qualifier_pattern

and qualifier_pattern =
    { pqual_pat_desc: qual_pat_desc;
      pqual_pat_loc: Location.t }

and qual_pat_desc = string * qual_pat_type_anno * predicate_pattern 
and qual_pat_type_anno = (string * p_type) list

(* Specification declarations *)

and specification_declaration = string * predicate_pattern
(** // *)

type p_expression =
  { pexp_desc: p_expression_desc;
    pexp_loc: Location.t }

and p_expression_desc =
  | Pexp_ident of string
  | Pexp_num of int
  | Pexp_bool of bool
  | Pexp_prefix of string * p_expression
  | Pexp_infix of string * p_expression * p_expression
  | Pexp_cast of p_expression * p_type       (** impure *)
  | Pexp_fld of p_expression * component     (** impure *)
  | Pexp_new of p_type * p_expression        (** impure *)
  | Pexp_fun of string * p_expression list
  | Pexp_fcall of string * actual_params     (** impure *)

and actual_params = (string * Location.t) list * p_expression list 

type a_expression = p_expression
  (** without the impure cases *)

type dlink_kind = DL | XL

type a_proposition =
  | Aprop_exp of a_expression
  | Aprop_node of component * a_expression * (component * a_expression) list
  | Aprop_indpred of string * (string * Location.t) list * a_expression list
      * Location.t
  | Aprop_ifthenelse of a_expression * a_proposition * a_proposition
  | Aprop_star of a_proposition * a_proposition
  | Aprop_barbar of a_proposition * a_proposition
  | Aprop_box of component * a_proposition

type a_invariant = a_proposition option

type p_statement =
  { pstm_desc: p_statement_desc;
    pstm_loc: Location.t }

and p_statement_desc =
  | Pstm_exp of p_expression
  | Pstm_assign of string * p_expression option
  | Pstm_fldassign of (p_expression * component * p_expression) list
  | Pstm_dispose of p_expression * p_expression
  | Pstm_block of p_statement list
  | Pstm_assume of p_expression
  | Pstm_if of p_expression option * p_statement * p_statement
  | Pstm_while of a_invariant * p_expression option * p_statement
  | Pstm_withres of component * p_expression * p_statement * string
      * p_expression list
  | Pstm_action of p_statement * component * string * p_expression list
  | Pstm_parblock of (string option * string * actual_params) list
  | Pstm_interfere of component * string
  | Pstm_return of p_expression option
  | Pstm_break
  | Pstm_continue
  | Pstm_comment of string

type p_action = 
    string * (string * Location.t) list 
      * a_proposition * a_proposition * a_proposition
      * p_statement list * Location.t

type p_vars = (string * p_type * Location.t) list

type p_item =
  | Pdec_class of string * predicate_pattern option * p_vars * Location.t
  | Pdec_var of string * p_type * Location.t
  | Pdec_fun of string * p_type * (p_vars * p_vars)
      * (a_invariant * a_invariant * 
					(string * predicate_pattern) option * (string * predicate_pattern) option) 
			* (p_vars * p_statement list) * Location.t
  | Pdec_resource of component * (string * Location.t) list * a_invariant
      * (p_vars * p_statement list) * p_statement list option * p_action list
      * predicate_pattern * Location.t
  | Pdec_indpred of string * (string * Location.t) list
      * a_proposition * Location.t
  | Pdec_comment of string

type p_program = p_item list


let iter f =
  let rec loop = function
    | [] -> ()
    | {pstm_desc=stm; pstm_loc=loc} :: stms ->
	f loc stm;
	match stm with
	  | Pstm_block(stm_l) -> loop (stm_l @ stms)
	  | Pstm_if(_,s0,s1) -> loop (s0 :: s1 :: stms)
	  | Pstm_while(_,_,s) -> loop (s :: stms)
	  | Pstm_withres(_,_,s,_,_) -> loop (s :: stms)
	  | Pstm_action(s,_,_,_) -> loop (s :: stms)
	  | _ -> loop stms
  in loop

let a_prop_empty =
  Aprop_exp ({pexp_desc = Pexp_bool true; pexp_loc = Location.none})

let rec exp_is_pure e = match e.pexp_desc with
  | Pexp_prefix (_,e1) -> exp_is_pure e1
  | Pexp_infix (_,e1,e2) -> exp_is_pure e1 && exp_is_pure e2
  | Pexp_fun (_, el) -> List.for_all exp_is_pure el
  | Pexp_ident _ | Pexp_num _ | Pexp_bool _ -> true
  | Pexp_fld _ | Pexp_new _ | Pexp_fcall _ | Pexp_cast _ -> false

