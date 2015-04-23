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
(** Representation of expressions *)

open Misc

(** Built-in functions with one argument *)
type sfn1 = 
  | Sfn_NOT
  | Sfn_item
  | Sfn_sorted
  | Sfn_hd
  | Sfn_tl
  | Sfn_set_of_list
  | Sfn_can_return

(** Built-in functions with two arguments *)
type sfn2 =
  | Sfn_list_lt
  | Sfn_subset
  | Sfn_set_minus

(** Built-in functions with a variable number of arguments *)
type sfn =
  | Sfn_list
  | Sfn_set
  | Sfn_AND
  | Sfn_OR
  | Sfn_XOR
  | Sfn_undef

type sfn_grp =
  | Sfn_plus
  | Sfn_pos

type id_internal1
type id_internal2
type id_internal3

(** Canonical expressions *)
type exp = private
  | Enum of int
  | Eident of id_internal1 * id_internal2 * id_internal3
  | Eeq of exp  * exp
  | Efun1 of sfn1 * exp
  | Efun2 of sfn2 * exp * exp
  | Efun of sfn * exp list
  | Egrp of sfn_grp * int * ie_list (** Abelian groups *)

and ie_list = private
  | IEnil
  | IEcons of exp * int * ie_list

(** Substitutions *)
type subst = exp -> exp

(* -------------------------------------------------------------------------- *)
(** {2 Standard functions} *)
(* -------------------------------------------------------------------------- *)

val string_of_sfn1 : sfn1 -> string
val string_of_sfn2 : sfn2 -> string
val string_of_sfn : sfn -> string
val string_of_sfn_grp : sfn_grp -> string

(* -------------------------------------------------------------------------- *)
(** {2 Identifiers} *)
(* -------------------------------------------------------------------------- *)

(** Identifiers *)
module Id : sig
  type t

  val tid    : t
  val mytid  : t
  val result : t
  val junk   : t
  val create : string -> t
  val tempid : unit -> t

  val gensym_str : string -> t
  val gensym_str_ex : string -> t
  val gensym_norm: t -> t
  val gensym_garb: t -> t

  val of_exp : exp -> t
    (** unsafe constructor *) 

  val compare : t -> t -> int

  val is_existential : t -> bool
  val is_no_junk_var : t -> bool

  val to_string : t -> string
	
	val to_unex_string : t -> string
end

module IdSet : Set.S with type elt = Id.t
module IdMap : Map.S with type key = Id.t

(* -------------------------------------------------------------------------- *)
(** {2 Expressions} *)
(* -------------------------------------------------------------------------- *)

module E : sig
  val zero : exp
  val one : exp
  val tid : exp
  val empty_list : exp
  val empty_set : exp
  val undef : exp
  val num : int -> exp
  val id  : Id.t -> exp

  val band : exp list -> exp
  val bnot : exp -> exp
  val fun1 : sfn1 -> exp -> exp
  val fun2 : sfn2 -> exp -> exp -> exp
  val funn : sfn -> exp list -> exp
  val xor : exp list -> exp
  val add : exp -> exp -> exp
  val sub : exp -> exp -> exp
(*  val mk_grp : sfn_grp -> int -> ie_list -> exp *)
  val list : exp list -> exp
  val set : exp list -> exp
  val item : exp -> exp

  val eq  : exp -> exp -> exp
  val neq : exp -> exp -> exp
  val ltn : exp -> exp -> exp
  val leq : exp -> exp -> exp

  (** [fv e s = fv(e) ++ s] *)
  val fv : exp -> IdSet.t -> IdSet.t
  
  val fhd : exp -> IdSet.t -> IdSet.t
  
  (** [fv e s = IdSet.filter is_existential (fv(e)) ++ s] *)
  val exfv : exp -> IdSet.t -> IdSet.t

  val gensym_str : string -> exp
  val gensym_str_ex : string -> exp

  val forall_fv : (Id.t -> bool) -> exp -> bool
end

val equal_exp : exp -> exp -> bool
val compare_exp : exp -> exp -> int
val compare_exp_list : exp list -> exp list -> int
val abs_compare_exp : exp -> exp -> int

val mem_exp : exp -> exp list -> bool

val remdup_exp : exp list -> exp list

(** return true if exp of the form _x *)
val existential_id : exp -> bool

val exp_fold : (exp -> 'a -> 'a) -> exp -> 'a -> 'a
val ie_fold : (exp -> int -> 'a -> 'a) -> ie_list -> 'a -> 'a
val ie_fold_exp : (exp -> 'a -> 'a) -> ie_list -> 'a -> 'a


(* -------------------------------------------------------------------------- *)
(** {2 Substitutions} *)
(* -------------------------------------------------------------------------- *)

val mk_fun_subst: subst -> subst
val mk_id_subst: (Id.t -> exp) -> subst
val mk_subst: (Id.t, exp) plist -> subst
val mk_single_subst : Id.t -> exp -> subst
val mk_gensym_garb_subst : Id.t -> subst
val mk_gensym_garb_subst_idset : IdSet.t -> subst
val mk_gensym_garb_subst_idset2 : IdSet.t -> subst * subst

(** Replace existentials with gensym'd normal vars. *)
val existentials_rename_tonormal_sub : IdSet.t -> subst * subst

(** Replace existentials with gensym'd existential vars. *)
val existentials_rename_sub : IdSet.t -> subst

val map_sub : ('a -> 'a) -> 'a list -> 'a list

val map_id_exp_sub : (exp -> exp option) -> exp -> exp

val map_idset : subst -> IdSet.t -> IdSet.t

val exp_no_s : string -> exp -> bool

(* -------------------------------------------------------------------------- *)
(** {2 Disjoint sets} *)
(* -------------------------------------------------------------------------- *)

(** Disjoint sets *)
module Dset : sig
  type t
  val emp: t
  val add: exp -> t -> t
  val remove: exp -> t -> t
  val mem: exp -> t -> bool
  val from_list: exp list -> t
  val to_list: t -> exp list 
  val inter: t -> t -> t
  val union: t -> t -> t
  val subset: t -> t -> bool
  val partition: (exp -> bool) -> t -> exp list * t
  val filter : (exp -> bool) -> t -> t
  val fold : (exp -> 'a -> 'a) -> t -> 'a -> 'a
  
  val compare : t -> t -> int
  val abs_compare : t -> t -> int

  val map : subst -> t -> t
  val no_s : string -> t -> bool
end

(* -------------------------------------------------------------------------- *)
(** {2 Fields} *)  
(* -------------------------------------------------------------------------- *)

module Fld : sig
(** Finite map from components to expressions *)
  type t 

  val emp : t
  val one : component -> exp -> t
  val two : component -> exp -> component -> exp -> t
  val from_list : (component * exp) list -> t
  val inter : t -> t -> t
  val union : t -> t -> t
  val hasfld : component -> t -> bool
  val try_get : component -> t -> exp option
  val get : component -> t -> exp
  val get_extend : component -> t -> exp * t
  val set : component -> exp -> t -> t
  val mem : component -> exp -> t -> bool
  val containing : exp -> t -> component
  val exists : (component -> exp -> bool) -> t -> bool
  val filter : (component -> exp -> bool) -> t -> t
  val remove : component -> t -> t
  val fold : (component -> exp -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_val : (exp -> 'a -> 'a) -> t -> 'a -> 'a
  val iter_val : (exp -> unit) -> t -> unit

  (** [components_equal fld1 fld2] returns a conjuction of equalities for
      each component that is defined in both [fld1] and [fld2] *)
  val components_equal : t -> t -> exp * t

  val subset : t -> t -> exp

  val compare : t -> t -> int
  val abs_compare : t -> t -> int

  val map : subst -> t -> t
  val no_s : string -> t -> bool
end

(* -------------------------------------------------------------------------- *)
(** {2 Pretty printing} *)
(* -------------------------------------------------------------------------- *)

val pp_ident : Format.formatter -> Id.t -> unit
val pp_idset : Format.formatter -> IdSet.t -> unit
val pp_exp : Format.formatter -> exp -> unit
val pp_fld : Format.formatter -> Fld.t -> unit

(* -------------------------------------------------------------------------- *)
(** {2 Identifier pools} *)
(* -------------------------------------------------------------------------- *)

type idpool

val idpool_new : (string -> Id.t) -> string -> idpool
val idpool_combine : idpool -> 'a list -> ('a, exp) plist
val idpool_combine2 : idpool -> IdSet.t -> subst * subst
