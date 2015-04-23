(* Poling: Proof Of Linearizability Generator 
 * Poling is built on top of CAVE and shares the same license with CAVE 
 * See LICENSE.txt for license.
 * Contact: He Zhu, Department of Computer Science, Purdue University
 * Email: zhu103@purdue.edu
 *)

(** This is the pool for recording completion condition which is data abstraction *)

(** completion codition *)
type completion = Predicate.t

type semaphore = bool

(** The spec pool: an event name and completion condition *)
type t = (string * Location.t * completion * semaphore) list ref

(** helping launch *)
type hp_launch = (string, Predicate.t list) Hashtbl.t

val funname : string ref

(** embedded return representation*)
val return_v : Exp.Id.t

val parse_thread_descriptor : (string * Predicate.t) -> unit

(** These funtion are used to facilitate symbsimp for specpool use *)

val getNode : Assertions.cprop -> Exp.exp -> Assertions.can_spred

val getNodeExps : Assertions.cprop -> Exp.exp list

val remove_ex : Predicate.t -> Predicate.t

(** Aritecture based implementation: Determine whether a local variable is typed of 
  * thread descriptor. *)
val is_thread_desc : (Exp.Id.t * String.t) list -> Exp.Id.t -> bool

(** Adding
 * pool is spec pool
 * evname is the name of the executing thread
 * p_st is the program state when executing thread is witnessed

val add : t -> Exp.exp -> Assertions.cprop -> Exp.exp -> unit*)

val print_pool : t -> hp_launch -> unit

(** Checking for when query 
  * pool is spec pool
	* evname is the name of the querying thread
	* t_desc is the thread descirptor of the querying thread
	* concurr_st is the program state when querying
	*)
val when_query : t -> Exp.exp -> Assertions.cprop -> 
		(Exp.Id.t * String.t) list -> bool

(** Checking for whether query
 * pool is the spec pool
 * evname is the name of the querying thread
 * t_desc is the thread descriptor of the querying thread
 * concurr_st is the program state when querying
 * seq_st is the sequential program state when querying (assuming no interference)
 *)
val whether_query :  t -> Predicate.t -> Predicate.t -> Assertions.cprop -> Assertions.cprop -> 
		(Exp.Id.t * String.t) list -> bool
 
(** if verifying thread is linearized
						    Simply return true else false 
 *  loc is the verifying return site
 *  t_descs is the set of thread descriptors found
 *  t_desc_mapping is how thread descripotr understands return_v and parameters
 *  specs is all the programmer provided specifications.
 *  check checks the pre- and post- shape abstraction are consistent to sequential specification 
 *)	
val check_by_t_descs : Location.t -> Assertions.cprop -> Assertions.cprop -> t -> hp_launch -> 
			Exp.exp list ->
	 		(string, Commands.fun_info) Hashtbl.t -> 
				(Assertions.cprop -> Assertions.cprop -> (string * Predicate.t) -> bool) -> bool
				
(** Given the set of updates along a program path, checks well-formness constraint.
 *  Two important condition: helping launch and helping completion
 *  1) If an instruction is to set program state implying helping launch then the state
 *  before cannot imply helping launch;
 *  2) If an instruction is to set program state implying hleping completion then the state
 *  before cannot imply helping completion;
 *  3) The states after witness cannot imply helping launch
 *)					
val check_well_formness : string -> Location.t -> 
		((Location.t * (Predicate.t list * Assertions.cprop * Commands.fld_assignments * Exp.IdSet.t * bool)) list) 
		-> Location.t -> hp_launch -> (string, Commands.fun_info) Hashtbl.t
		-> (Commands.fld_assignments -> Genarith.eprop -> Genarith.eprop option)
		-> bool