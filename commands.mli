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
(** Representation of program commands *)
open Misc
open Parsetree
open Exp
open Pure
open Assertions

(** Kind of branches *) 
type can_goto = Cgo_break | Cgo_continue | Cgo_return

(** Field assignments *)
type fld_assignments = (exp * component * exp) list

(** Canonical statement *)
type can_stmt =
  { can_st_desc: can_st_desc    (** statement descriptor *);
    mutable can_st_lv: IdSet.t  (** set of live variables *);
    can_st_loc: Location.t      (** location for error messages *);
  }

(** Canonical command: sequence of statements *)
and can_cmd = can_stmt list

(** Statement descriptor *)
and can_st_desc =
  | Cst_nondet of can_cmd * can_cmd
  | Cst_kill of IdSet.t
  | Cst_assign of Id.t * exp
  | Cst_fldlookup of component list * Id.t * exp * component
  | Cst_fldassign of component list * fld_assignments * (string * cprop) list ref
  | Cst_new of Id.t * exp
  | Cst_dispose of exp * exp
  | Cst_pfcall of (Id.t option * string * Id.t list * exp list) list
  | Cst_fcall2 of IdSet.t * cprop * cprop * string
  | Cst_assume of cprop
  | Cst_assume_exp of exp
  | Cst_assert_exp of exp
  | Cst_interfere of component * string
  | Cst_stabilize of component
  | Cst_action_begin of component * cprop * cprop * cprop * IdSet.t
  | Cst_action_end of component * IdSet.t (** free vars of postcondition *)
  | Cst_loop of can_cmd * cprop option
                             (** infinite loop -- exit with break/return *)
  | Cst_goto of can_goto
  | Cst_comment of string

(** Canonical entailments *)
type can_entailment = 
  cprop * can_cmd * can_cmd * cprop * IdSet.t * Location.t

(** Information about function declarations *)
type fun_info =
    { fun_param: Id.t list * Id.t list 
                            (** formal parameters (by reference, by value) *);
      fun_modif: IdSet.t    (** modified variables *);
      fun_pre: cprop     (** precondition *);
      fun_post: cprop    (** postcondition *);
      fun_loc: Location.t   (** location for error messages *);
			fun_purespec : (string * Predicate.t);
			fun_effspec : (string * Predicate.t);
			fun_returns : (Location.t, Predicate.t) Hashtbl.t;
			fun_lbs : (Id.t * string) list }

(** Resource initialization *)
type res_init = 
  | Cri_inv of cprop * Location.t
  | Cri_code of IdSet.t * can_cmd * Location.t

(* -------------------------------------------------------------------------- *)
(** {3 Constructors} *)
(* -------------------------------------------------------------------------- *)

val mk_cmd : can_st_desc -> Location.t -> can_cmd
val mk_assume : exp -> Location.t -> can_cmd
val mk_loop : can_cmd -> cprop option -> Location.t -> IdSet.t -> can_cmd
val mk_nondet : can_cmd -> can_cmd -> Location.t -> IdSet.t -> can_cmd

(** Make a deep copy of a command *)
val cmd_copy : can_cmd -> can_cmd

(* -------------------------------------------------------------------------- *)
(** {3 Inferred actions annotations} *)
(* -------------------------------------------------------------------------- *)

val actlr_clear : (string * can_entailment) list -> unit 
val actlr_iter : 
  (string * cprop -> unit) -> (string * can_entailment) list -> unit 
val actlr_print : (string * can_entailment) list -> unit 

(* -------------------------------------------------------------------------- *)
(** {3 Linearizability} *)
(* -------------------------------------------------------------------------- *)

val ident_lin_res : Id.t
val linear_fun_pre : cprop
val linear_fun_post : cprop

(** Check that a linearizability specification contains no loops
    and return its effectful & pure execution paths *)
val linear_parse_spec : can_cmd -> can_cmd list * can_cmd list

(** [insert_pure_code pure_code c] copies [c] and insert [pure_code] before
    every atomic_block exit *)
val insert_pure_code : can_cmd -> can_cmd -> can_cmd 

(* -------------------------------------------------------------------------- *)
(** {3 Other operations} *)
(* -------------------------------------------------------------------------- *)

val pp_cmd : Format.formatter -> can_cmd -> unit
val pp_linear_annot : Format.formatter -> can_cmd -> unit

(** [mark_live_vars fv_post c] updates [c] in place by marking its
    live variables at each program point. *)
val mark_live_vars : IdSet.t -> can_cmd -> unit

val insert_kill_dead_vars : can_cmd -> IdSet.t -> can_cmd

val clarify_cmd : can_cmd -> can_cmd

(** Unroll the last iteration of all the loops in [c] *)
val unfold_loops : can_cmd -> can_cmd

val actlr_merge_linear :
  (cprop -> can_cmd -> 'a) ->
  ('a -> cprop -> cprop) ->
  can_cmd ->
  (string * can_entailment) ->
  (string * can_entailment) list

val left_mover_optimization :
  (string * can_entailment) list -> (string * can_entailment) list
	
val cmd_lookup_rgnl : can_cmd -> component list

