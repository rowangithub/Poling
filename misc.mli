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

(** Library functions and miscellaneous routines *)

val formatter : Format.formatter ref

val pp : ('a, Format.formatter, unit) format -> 'a

module StringSet : Set.S with type elt = string
module StringMap : Map.S with type key = string

val identity : 'a -> 'a
  (** The identity function *)

val (|>) : 'a -> ('a -> 'b) -> 'b
  (** Reverse function application *)

val (|>>) : 'a -> ('a -> unit) -> 'a
  (** Reverse function application and return its argument *)

val (>>) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
  (** Reverse function composition *)

val (>>=) : 'a option -> ('a -> 'b option) -> 'b option
  (** Option monad bind *)

(** copy the content of tb2 to tb1 *)
val mergeHashtbl : ('a, 'b) Hashtbl.t -> ('a, 'b) Hashtbl.t -> ('a, 'b) Hashtbl.t

(** Transform a hashtable to list *)
val hashtbltoList : ('a, 'b) Hashtbl.t -> ('a * 'b) list

(** Operations on linked lists *)
module List : sig 

  val length : 'a list -> int
  val hd : 'a list -> 'a
  val tl : 'a list -> 'a list
  val nth : 'a list -> int -> 'a
  val rev : 'a list -> 'a list
  val append : 'a list -> 'a list -> 'a list
  val rev_append : 'a list -> 'a list -> 'a list

  val concat : 'a list list -> 'a list
  val flatten : 'a list list -> 'a list

  val iter : ('a -> unit) -> 'a list -> unit
  val map : ('a -> 'b) -> 'a list -> 'b list
	val map_i : (int -> 'a -> 'b) -> 'a list -> 'b list
  val rev_map : ('a -> 'b) -> 'a list -> 'b list
  val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b

  val iter2 : ('a -> 'b -> unit) -> 'a list -> 'b list -> unit
  val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val rev_map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
  val fold_right2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  
  val for_all : ('a -> bool) -> 'a list -> bool
  val exists : ('a -> bool) -> 'a list -> bool
  val for_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  val exists2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
  
  val mem : 'a -> 'a list -> bool
  val memq : 'a -> 'a list -> bool

  val find : ('a -> bool) -> 'a list -> 'a
  val filter : ('a -> bool) -> 'a list -> 'a list
  val find_all : ('a -> bool) -> 'a list -> 'a list
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list

  val assoc : 'a -> ('a * 'b) list -> 'b
  val assq : 'a -> ('a * 'b) list -> 'b
  val mem_assoc : 'a -> ('a * 'b) list -> bool
  val mem_assq : 'a -> ('a * 'b) list -> bool
  val remove_assoc : 'a -> ('a * 'b) list -> ('a * 'b) list
  val remove_assq : 'a -> ('a * 'b) list -> ('a * 'b) list

  val split : ('a * 'b) list -> 'a list * 'b list
  val combine : 'a list -> 'b list -> ('a * 'b) list

  val sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val stable_sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val fast_sort : ('a -> 'a -> int) -> 'a list -> 'a list
  val merge : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list

  (** New operations *)

  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val fold_cons : ('a -> 'b) -> 'a list -> 'b list -> 'b list
  val fold_append : ('a -> 'b list) -> 'a list -> 'b list -> 'b list
  val lifted_fold : ('a -> 'b -> 'b option) -> 'a list -> 'b -> 'b option

  val reduce : ('a -> 'b list -> 'b list) -> 'a list -> 'b list
  val reduce_append : ('a -> 'b list) -> 'a list -> 'b list
  
  val filter_not : ('a -> bool) -> 'a list -> 'a list
  
  val map_partial: ('a -> 'b option) -> 'a list -> 'b list
  val map_option : ('a -> 'b option) -> 'a list -> 'b list option
	
	val power_set  : 'a list -> ('a list) list 
  
	val remove_duplicates : 'a list -> 'a list
	
	val expand : ('a -> 'a list * 'b list) -> 'a list -> 'b list -> 'b list
	
	val to_string : string -> ('a -> string) -> 'a list -> unit
	
	val flap : ('a -> 'b list) -> 'a list -> ' b list 
	
	val lflap : 'a list list -> 'a list list
	
	val tflap2 : 'a list * 'b list -> ('a -> 'b -> 'c) -> 'c list
	
	val tflap3 : 'a list * 'b list * 'c list -> ('a -> 'b -> 'c -> 'd) -> 'd list
	
	val isPrefix : ('a -> 'a -> int) -> 'a list -> 'a list -> bool
	
	val isSuffix : ('a -> 'a -> int) -> 'a list -> 'a list -> bool

	val perms : 'a list -> ('a list) list

	val intersect : 'a list -> 'a list -> ('a -> 'a -> bool)-> 'a list
	
	val copy : 'a list -> 'a list
end


(* -------------------------------------------------------------------------- *)
(** {2 Components} *)
(* -------------------------------------------------------------------------- *)

(** Components can be compared using pointer equality *)

type component

val component_is_field : component -> bool
val component_of_string : string -> component
val string_of_component : component -> string
val string_of_field_component : component -> string
val compare_component : component -> component -> int

val node_component : component
val list_link_tag : component
val list_data_tag : component
val dl_Llink_tag : component
val dl_Rlink_tag : component
val tree_link_tags : component * component
val tree_data_tag : component

val is_value_field : component -> bool
val is_lock_field : component -> bool

val possible_link_fields : component list ref

module CompSet : Set.S with type elt = component


(* -------------------------------------------------------------------------- *)
(** {2 Packed association lists} *)
(* -------------------------------------------------------------------------- *)

type ('a, 'b) plist =
    PNil 
  | PCons of 'a * 'b * ('a, 'b) plist

(** Packed association lists *)
module PList : sig

  val nil : ('a, 'b) plist
  val cons : 'a -> 'b -> ('a, 'b) plist -> ('a, 'b) plist
  val rev_append : ('a, 'b) plist -> ('a, 'b) plist -> ('a, 'b) plist

  val for_all  : ('a -> 'b -> bool) -> ('a, 'b) plist -> bool
  val exists   : ('a -> 'b -> bool) -> ('a, 'b) plist -> bool
  val fold     : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) plist -> 'c -> 'c
  val fold_val : ('b -> 'c -> 'c) -> ('a, 'b) plist -> 'c -> 'c
  val lifted_fold : ('a -> 'b -> 'c -> 'c option)
                     -> ('a, 'b) plist -> 'c -> 'c option
  val iter     : ('a -> 'b -> unit) -> ('a, 'b) plist -> unit
  val iter_val : ('b -> unit) -> ('a, 'b) plist -> unit
  val length   : ('a, 'b) plist -> int
  val filter   : ('a -> 'b -> bool) -> ('a, 'b) plist -> ('a, 'b) plist
  val rev_partition : ('a -> 'b -> bool) -> ('a, 'b) plist
                     -> ('a, 'b) plist * ('a, 'b) plist

  val map_val  : ('b -> 'b) -> ('a, 'b) plist -> ('a, 'b) plist

  val mem_assq : 'a -> ('a, 'b) plist -> bool

  (** [assq k l] raises [Not_found] if there is no mapping for the key
      [k] in the list [l] *)
  val assq : 'a -> ('a, 'b) plist -> 'b

  val try_assq : 'a -> ('a, 'b) plist -> 'b option

  val remove_assq : 'a -> ('a, 'b) plist -> ('a, 'b) plist

  (** [findq l e x] returns the first mapping of [x] in [l];
      or the default_value [e], if there is none. Pointer equality
      is used to compare keys in the association list. *)
  val findq : ('a, 'b) plist -> 'b -> 'a -> 'b

  val merge : ('a -> 'a -> int) -> ('a, 'b) plist
              -> ('a, 'b) plist -> ('a, 'b) plist

  val get_first : ('a -> 'b -> 'c option) -> ('a, 'b) plist -> 'c option

  val combine : 'a list -> 'b list -> ('a, 'b) plist
end
