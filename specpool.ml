(* Poling: Proof Of Linearizability Generator 
 * Poling is built on top of CAVE and shares the same license with CAVE 
 * See LICENSE.txt for license.
 * Contact: He Zhu, Department of Computer Science, Purdue University
 * Email: zhu103@purdue.edu
 *)

(** This is the pool for recording completion condition which is data abstraction *)

open Misc
open Assertions
open Exp
open Commands

(** completion codition *)
type completion = Predicate.t

(** helping launch *)
type hp_launch = (string, Predicate.t list) Hashtbl.t

type semaphore = bool

(** The spec pool: an event name and completion condition *)
type t = (string * Location.t * completion * semaphore) list ref

(** The function under verifying *)
let funname = ref ""

(** The specification, when given, should be carefully understood by the checker 
 * 1) We allow programmer to use return_v to represent the return value and orginial parameters
 * in the specification.
 * 2) We maintain t_desc_mapping as we want to know how thread descirptors know the 
 * mapping from return_v and parameters to their fields.
 *)

(*let op = ".op"*)
(*let tid = ".val"*)
(*let tid = ".val"*)
let op = ref ""
let tid = ref ""
let tid_str = ref ""
let t_desc_str = ref ""
let return_v = Exp.Id.create "return_v"
(*let tid_str = "mytid"		*)
(*let tid_str = "TID"*)
(*let t_desc_str = "ThreadInfo" *)
(*let t_desc_str = "ThreadDescriptor"*)
let t_desc_mapping = Hashtbl.create 5
(*let _ = (Hashtbl.replace t_desc_mapping return_v "data";
				Hashtbl.replace t_desc_mapping (Exp.Id.create "v") "data";
				
				Hashtbl.replace t_desc_mapping (Exp.Id.create "po") "o";
				Hashtbl.replace t_desc_mapping (Exp.Id.create "pn") "n") *)
				
(** Parse thread descriptor *)
let parse_thread_descriptor (sid, tdesc) = 
	let _ = (t_desc_str := sid) in
	let conditions = Predicate.flatten_and tdesc in
	List.iter (fun condition -> match condition with
		| Predicate.Atom (Predicate.Var v1, Predicate.Eq, Predicate.Var v2) ->
			if (String.compare "tid" (Id.to_string v1) = 0) then
				tid := "." ^ (Id.to_string v2)
			else if (String.compare "tid" (Id.to_string v2) = 0) then
				tid := "." ^ (Id.to_string v1)
			else if (String.compare "mytid" (Id.to_string v1) = 0) then
				tid_str := Id.to_string v2
			else if (String.compare "mytid" (Id.to_string v2) = 0) then
				tid_str := Id.to_string v1
			else if (String.compare "tname" (Id.to_string v1) = 0) then
				op := "." ^ (Id.to_string v2)
			else if (String.compare "tname" (Id.to_string v2) = 0) then
				op := "." ^ (Id.to_string v1) 
			else if (String.compare "return_v" (Id.to_string v1) = 0) then
				Hashtbl.replace t_desc_mapping return_v (Id.to_string v2)
			else if (String.compare "return_v" (Id.to_string v2) = 0) then
				Hashtbl.replace t_desc_mapping return_v (Id.to_string v1)
			else Hashtbl.replace t_desc_mapping v2 (Id.to_string v1)
		| _ -> ()
		) conditions				

(** ==================== Util Function ======================*)
let remove_ex pred = 
	let ids = Predicate.vars pred in
	let tb = Hashtbl.create 7 in
	let _ = List.iter (fun id ->
		let idstr = Exp.Id.to_string id in
		let id' = try if (String.get idstr 0 = '_') then
			let second_underline = String.index_from idstr 1 '_' in
			let idstr' = String.sub idstr 1 (second_underline-1) in
			if (String.compare idstr' "?" = 0) then id
			else (Exp.Id.create idstr')
		else id
		with _ -> id in
		if (Hashtbl.mem tb id') then 
			Hashtbl.replace tb id' (id :: (Hashtbl.find tb id'))
		else Hashtbl.add tb id' [id]
		) ids in
	Hashtbl.fold (fun id' ids res -> 
		if (List.length ids = 1) then
			let id = List.hd ids in
			Predicate.subst (Predicate.Var id') id pred
		else pred
		) tb pred

let getNode st exp = 
	try 
		(*let _ = Misc.pp "@.st=%a@." pp_cprop st in
		let _ = Misc.pp "@.exp=%s@." (Exp.Id.to_string (Exp.Id.of_exp exp)) in*)
		let st = snd (fst (List.hd st)) in
		List.find (fun csp -> match csp with
			| Csp_node (_, _, e, _) -> (Exp.compare_exp e exp = 0) 
			| _ -> false
			) st
	with _ -> ((*Misc.pp "@.Spec pool finding thread identifier error@."; *)
						assert false)
						
let getNodeExps st = 
	try
		let st = snd (fst (List.hd st)) in
		List.map_partial (fun csp -> match csp with
			| Csp_node (_, _, e, _) -> Some e
			| _ -> None) st
	with _ -> (Misc.pp "@.Spec pool finding node error@."; 
						assert false)
	
let getEvName node = match node with
	| Csp_node (_, _, e, fld) -> 
		(try
		let nodestr = Exp.Id.to_string (Exp.Id.of_exp e) in
		let i = String.index nodestr '_' in
		String.sub nodestr 0 i
		with _ -> !funname)
		(*let nameexp = Fld.get (Misc.component_of_string op) fld in
		let nameid = Exp.Id.of_exp nameexp in
		Exp.Id.to_string nameid*)
	| _ -> (Misc.pp "@.Thread indentifier ill-formed@."; assert false)
		
let getTID node = match node with
	| Csp_node (_, _, e, fld) -> Fld.get (Misc.component_of_string !tid) fld 
	| _ -> (Misc.pp "@.Thread indentifier ill-formed@."; assert false)


(** Aritecture based implementation: Determine whether a local variable is typed of 
  * thread descriptor. *)
let is_thread_desc locals variable =
	try 
		(* locals : (Id.t * typ * Location.t) list *)
		let (_, ty) = List.find (fun (id', ty) -> 
			((Exp.Id.compare variable id') = 0)) locals in
		((String.compare ty !t_desc_str) = 0)
	with _ -> false
	
	
(** check if the verifying thread has thread descriptor and return it *)												
let getMyDescNode st locals = 
	let st = snd (fst (List.hd st)) in
		List.find (fun csp -> match csp with
			| Csp_node (_, _, e, _) when (is_thread_desc locals (Exp.Id.of_exp e)) ->
				let tid = getTID csp in 
				(Exp.Id.compare (Exp.Id.of_exp tid) (Exp.Id.create !tid_str) = 0) 
			| _ -> false
			) st
	
(** Proper substitution: Given a thread descriptor subsitute it for a normal value *)	
let norm_val = Predicate.Var (Exp.Id.create "tdcmp")

let subst completion t_desc = 
	try Predicate.subst norm_val (Exp.Id.of_exp t_desc) completion
	with _ -> (Misc.pp "@.Completion substitution error. Please report@."; assert false)
	
(** ==================== End Util Function ======================*)
	
(** Abstract a program state into data abstraction formula 
 * locals are local variables, i.e., only variables are typed of thread descriptor are
 * of interests.
 *)
let data_abstract cp keys purepreds locals =
	let keys = List.remove_duplicates keys in 
	let rec data_abstract_rec takein (cp : cprop) = 
		let key e fld = List.exists (fun key -> 
			Exp.compare_exp key e = 0 || (
				Fld.fold_val (fun ee res -> 
					if (res) then res
					else Exp.compare_exp ee key = 0) fld false
				)
		) keys in
		let rec extend pred splist = match splist with
			| PNil -> pred
			| PCons (rid, cp', splist') ->
				let pr = data_abstract_rec true cp' in
				let pr = Predicate.big_and (pred :: pr) in
				extend pr splist' in
		List.map (fun ((pure, csps), scpl) -> 
				let p = 
					if (takein) then begin 
						(*let _ = Misc.pp "@.csp=%a@." Assertions.pp_cform ((pure, csps), scpl) in
						let _ = Misc.pp "@.purepred=%a@." 
																Predicate.pprint (Predicate.big_and purepreds) in
						let _ = Misc.pp "@.keys=%s@." (List.fold_left (fun res key -> 
							res ^ " " ^ (Id.to_string (Exp.Id.of_exp key))
							) "" keys) in*)
						let freevars = Hashtbl.create 15 in
						let p1 = List.map_partial (fun csp -> match csp with
							| Csp_node (_,_,e,fld) when key e fld -> 
								Some (
								let vs = 
									if (is_thread_desc locals (Exp.Id.of_exp e)) then
										Fld.fold (fun com exp l -> 
										if (com = Misc.list_data_tag || com = Misc.list_link_tag ||
												Hashtbl.fold (fun k v res -> 
													if (res) then res
													else com = (component_of_string ("." ^ v)) 
													) t_desc_mapping false) then l
										else (com, exp) :: l) fld [] 
									else [(Misc.list_data_tag, Fld.get Misc.list_data_tag fld)]	in 
								let pvs = List.map (fun (com, exp) -> 
									(* check the vadility of p: if p contains variable a which does not
									   sytactically reside in completion keys; then we search the pure
										 pred to find some pred p' that refer to a and the rest of variables
										 are also in p'. If we cannot find such p' we abort.
									 *)
									let uninterfun = Predicate.FunApp (string_of_field_component com, 
										[Predicate.Var (Exp.Id.of_exp e)]) in
									let keys = List.map Exp.Id.of_exp keys in
									let exp = (Pure.to_sub pure) exp in
									match exp with 
										| Exp.Eident _ -> 
											let vexp = Exp.Id.of_exp exp in
											if (List.exists (fun key -> Id.compare key vexp = 0) keys) then
												Predicate.Atom (
												Predicate.transl_pexp exp, 
												Predicate.Eq, 
												uninterfun)
											else begin
												try let purepred = List.find (fun purepred -> 
													let purepred_vars = Predicate.vars purepred in
													(List.exists (fun var -> Id.compare var vexp = 0) purepred_vars) 
														&& (List.for_all (fun var -> Id.compare var vexp = 0 || 
															List.exists (fun key -> 
															Id.compare key var = 0) keys) purepred_vars) 
													) purepreds in
												Predicate.subst uninterfun vexp purepred
												with _ -> ((*Misc.pp "The predicate contain free variable\n"; 
												Misc.pp "vexp=%s@." (Id.to_string vexp);*)
												Hashtbl.replace freevars exp ();
												Predicate.Atom (
												Predicate.transl_pexp exp, 
												Predicate.Eq, 
												uninterfun)) end
										| Exp.Enum _ -> 
											Predicate.Atom (
											Predicate.transl_pexp exp, 
											Predicate.Eq, 
											uninterfun)
										| _ -> (Misc.pp "The heap is not well formed to abstraction\n"; assert false)
									) vs in
								Predicate.big_and pvs
								) 
							| _ -> None
							) csps in
						let nodes = List.map_partial (fun csp -> match csp with
							| Csp_node (_,_,e,fld) when (key e fld || Hashtbl.mem freevars e) -> 
								Some e
							| _ -> None) csps in
						let (p2, _) = List.fold_left (fun (p, ls) node ->
							(List.fold_left (fun p l -> 
								Predicate.And (
									Predicate.Atom (Predicate.transl_pexp node, Predicate.Ne, 
									Predicate.transl_pexp l), p)
								) p ls, node :: ls)
							) 
							(Predicate.True, []) 
							nodes in
						let p3 = Predicate.big_and (List.map (fun node -> 
							Predicate.Atom (Predicate.transl_pexp node, Predicate.Ne,
							Predicate.PInt 0)) nodes) in
						(** Safe feature: p2 and p3 is useful when p1 is non-empty *)
						if (List.for_all (fun p -> 
							match p with 
								| Predicate.True -> true
								| _ -> false
							) p1) then Predicate.Not (Predicate.True)
						else	
						Predicate.big_and (p3 :: (p2 :: p1))
					end
					else Predicate.True in
				extend p scpl
			) cp in
	let result = data_abstract_rec true cp in
	Predicate.big_or result

(** Adding
 * pool is spec pool
 * evname is the name of the executing thread
 * p_st is the program state when executing thread is witnessed
 *)
let add pool hp_launch evname loc pre_st p_st semaphore t_desc locals = 
	let keys = 
		let st = snd (fst (List.hd pre_st)) in
		List.map_partial (fun csp -> match csp with
			| Csp_node (_, _, e, fld) -> 
				if (Fld.fold_val (fun e res -> 
					if (res) then res
					else (Exp.compare_exp e t_desc = 0)
					) fld false) then Some e
				else None
			| _ -> None
			) st in
	let _ = (** If this is a helped event, then record its helping launch *)
		if (not semaphore) then begin
			if (Hashtbl.mem hp_launch evname) then
				Hashtbl.replace hp_launch evname 
				(subst (data_abstract pre_st (t_desc::keys) [] locals) t_desc ::
				Hashtbl.find hp_launch evname) 
			else 
				Hashtbl.replace hp_launch evname
		    [(subst (data_abstract pre_st (t_desc::keys) [] locals) t_desc)] 
		end in
	let completion = data_abstract p_st (t_desc::keys) [] locals in
	let completion = subst completion t_desc in
	(*let _ = Misc.pp "@.completion=%a@." Predicate.pprint completion in*)
	(pool := (evname, loc, completion, not semaphore) :: (!pool))
	
(*let print_t_desc str t_desc = 
	Misc.pp "@.%s checking t_desc=%s@." str (Exp.Id.to_string (Exp.Id.of_exp t_desc))*)
	
	
let print_pool pool hp_launch = (
	(*List.iter (fun (ev, loc, completion, semaphore) -> 
		Misc.pp "pool item iwth name ev as %s, loc as %s, completion as %a and semaphore as %b\n"
		ev (Location.lineno_to_string loc) Predicate.pprint completion semaphore 
		) (!pool);
	Hashtbl.iter (fun evname launches -> 
		Misc.pp "hp_launch: ev as %s can be helped if %a is met@." evname Predicate.pprint
		(Predicate.big_or launches) 
		) hp_launch	*)
	) 
	
(** Check whether a completion compatible with existing pool items 
  * pool is spec pool
	* t_desc is the thread descirptor of the querying thread
	* concurr_st is the program state when querying
	*)
let when_query pool t_desc concurr_st locals =
	try
		(*let _ = print_t_desc "when query" t_desc in*)
		let node = getNode concurr_st t_desc in
		
		let evname = getEvName node in
	
		let tid = getTID node in 
		if (Exp.Id.compare (Exp.Id.of_exp tid) (Exp.Id.create !tid_str) = 0) then true
		else List.for_all (fun (ev, loc, completion, _) ->
			if (String.compare ev evname = 0) then (
				let pre = Predicate.True in
				
				let vars = List.map Exp.E.id (Predicate.vars completion) in
				let dabs_concurr_st = data_abstract concurr_st (t_desc::vars) [] locals in
				let dabs_concurr_st = subst dabs_concurr_st t_desc in
				
				let vc = Predicate.Not (Predicate.And (completion, dabs_concurr_st)) in
				(*let _ = Misc.pp "vc is %a\n" Predicate.pprint vc in*)
				let result = TheoremProver.implies pre vc in
				(*let _ = Misc.pp "The checking result is %b\n" result in*)
				(TheoremProver.finish (); result)	
				)
			else true
			) (!pool)
	with _-> ((*Misc.pp "@.when checking query soundly assumes false@.";*) false)

(** Check whether a completion implied by an existing pool item 
 * pool is the spec pool
 * evname is the name of the querying thread
 * t_desc is the thread descriptor of the querying thread
 * concurr_st is the program state when querying
 * seq_st is the sequential program state when querying (assuming no interference)
 *)
let whether_query pool purepred returnpred concurr_st seq_st locals =
	try 
		(*let _ = Misc.pp "=============Begin Whether Query==============\n" in*)
		let node = getMyDescNode concurr_st locals in
		let t_desc = match node with Csp_node (_, _, e, _) -> e | _ -> assert false in
		let evname = getEvName node in
		
		let checkreturn = match returnpred with
			| Predicate.Not Predicate.True -> true
			| _ -> 
				if (Hashtbl.mem t_desc_mapping return_v) then
					let should_pred = Predicate.Atom (Predicate.Var (Id.create("Result")), Predicate.Eq,
						Predicate.FunApp (Hashtbl.find t_desc_mapping return_v, [Predicate.Var (Exp.Id.of_exp t_desc)])) in
					(should_pred = returnpred) 
				else true in
		if not (checkreturn) then false
		else
		(** Be Careful: Also the pure information at concurr_st is needed. *)
		let witpure = fst (fst (List.hd concurr_st)) in
		let witexplist = Pure.to_exp witpure in
		let witpurepred = Predicate.transl_pred witexplist in
		(*let purepred = Predicate.And (witpurepred, purepred) in*)
		let purepred = witpurepred in
		
		let r = List.exists (fun (ev, loc, completion, semaphore) ->
			(*let _ = Misc.pp "===========checking pool item=============\n" in*)
			let r = if (semaphore) then
				if (String.compare ev evname = 0) then 
					(*let purepred = remove_ex purepred in*)
					let vars = List.map Exp.E.id (Predicate.vars completion) in
					let dabs_concurr_st = data_abstract concurr_st (t_desc::vars) 
							(Predicate.flatten_and purepred) locals in
					let dabs_concurr_st = subst dabs_concurr_st t_desc in
					let dabs_seq_st = data_abstract seq_st (t_desc::vars) 
							(Predicate.flatten_and purepred) locals in
					let dabs_seq_st = subst dabs_seq_st t_desc in
					
					let result_1 = TheoremProver.implies (Predicate.And (purepred, completion)) 
													dabs_concurr_st in
					(*let _ = Misc.pp "The checking result_1 is %b\n" result_1 in*)
					let _ = TheoremProver.finish () in
					let pre = Predicate.True in
					let vc = Predicate.Not (Predicate.And (completion, dabs_seq_st)) in
					let result_2 = TheoremProver.implies pre vc in
					(*let _ = Misc.pp "The checking result_2 is %b\n" result_2 in*)
					(TheoremProver.finish (); result_1 & result_2)
				else false
			else false in
			(*let _ = Misc.pp "============checked pool item==============\n" in*)
			r
			) (!pool) in
		(*let _ = Misc.pp "=============End Whether Query==============\n" in*)
		r
	with _ -> (false)
		
		
(** if verifying thread is linearized
						    Simply return true else false 
 *  loc is the verifying return site
 *  funinfo is the verifying event
 *  t_descs is the set of thread descriptors found
 *  t_desc_mapping is how thread descripotr understands return_v and parameters
 *  specs is all the programmer provided specifications.
 *  check checks the pre- and post- shape abstraction are consistent to sequential specification 
 *)		
let check_by_t_descs loc precondition postcondition pool hp_launch t_descs g_fun_ht check = 		
	(** 1) Map t_descs to specification formula *)
	let specs = List.map (fun t_desc -> 
		(*let _ = Misc.pp "@.checking spec=%s@." (Exp.Id.to_string (Exp.Id.of_exp t_desc)) in*)
		let node = getNode precondition t_desc in
		(*let _ = Misc.pp "@.prepared node@." in*)
		let tdvar = Predicate.Var (Exp.Id.of_exp t_desc) in
		(*let _ = Misc.pp "@.prepared tdvar@." in*)
		let evname = getEvName node in
		(*let _ = Misc.pp "@.prepared evname@." in*)
		let ctid = getTID node in
		(*let _ = Misc.pp "@.prepared ctid@." in*)
		let funinfo = Hashtbl.find g_fun_ht evname in
		(*let _ = Misc.pp "@.prepared funinfo@." in*)
		let spec = snd (funinfo.fun_effspec) in
		(*let _ = Misc.pp "@.prepared spec@." in*)
		(* Here we would like to modify the specification for verifying thread *)
		if (Exp.Id.compare (Exp.Id.of_exp ctid) (Exp.Id.create !tid_str) = 0) then 
			(*let _ = Misc.pp "@.This is verifying thread@." in*)
			let returnpred = Hashtbl.find funinfo.fun_returns loc in
			try let returnpexp = match returnpred with
				| Predicate.Atom (_, Predicate.Eq, pexp) -> pexp
				| _ -> ((*Misc.pp "@.Ill-formed return experssion%a@." Predicate.pprint returnpred;*) assert false) in
			(true, evname, t_desc, fst (funinfo.fun_effspec), Predicate.subst returnpexp return_v spec, funinfo.fun_lbs)
			with _ -> (true, evname, t_desc, fst (funinfo.fun_effspec), spec, funinfo.fun_lbs)
		else (* This is thread other than verifying thread *)
			(*let _ = Misc.pp "@.This is other thread@." in*)
			let spec = 
				if (Hashtbl.mem t_desc_mapping return_v) then
					Predicate.subst 
						(Predicate.FunApp (Hashtbl.find t_desc_mapping return_v, [tdvar])) 
						return_v spec 
				else spec	in
			let spec = List.fold_left (
				fun res funparam -> 
					if (Hashtbl.mem t_desc_mapping funparam) then
						Predicate.subst 
						(Predicate.FunApp (Hashtbl.find t_desc_mapping funparam, [tdvar])) 
						funparam res
					else res
					) spec (fst funinfo.fun_param @ snd funinfo.fun_param) in
			(false, evname, t_desc, fst (funinfo.fun_effspec), spec, funinfo.fun_lbs) 
		) t_descs in
	(*let _ = Misc.pp "@.prepared specifcations@." in*)
	(** 2) Check each of them *) 
	let (checking_result, specs) = 
		List.fold_left (fun (cr, res) (b, evname, t_desc, rid, spec, lbs) -> 
			let r = check precondition postcondition (rid, spec) in 
				if (r) then begin
					(* adding to pool *) 
					add pool hp_launch evname loc precondition postcondition b t_desc lbs;
					if (b) then (true, res)
					else (cr, res) 
				end else (cr, res @ [(b, evname, t_desc, rid, spec, lbs)])
				) (false, []) specs in
	(*let _ = Misc.pp "@.Individual checing result is %b@." checking_result in*)
	if (checking_result) then true
	(** 3) Check them together *)
	else if (List.length specs > 1) then begin
		let spec_perms = List.perms specs in
		(*let _ = Misc.pp "@.prepared spec_perms@." in*)
		List.exists (fun spec_perm ->
			let allspecs = (
				(** The composed specification must be based on proper vocabulary *)
				List.map_i (fun i (_, _, _, _, spec, _) -> 
					(*let _ = Misc.pp "@.Considering spec=%a@." Predicate.pprint spec in*)
					if (i = 0) then
						Predicate.map_fields
							(fun x -> 
								if (String.length x >= 4 && String.compare (String.sub x 0 4) "post" = 0) then
									(Pervasives.string_of_int 1)
								else x)
							spec
					else if (i = List.length spec_perm-1) then
						Predicate.map_fields
							(fun x -> 
								if (String.length x >= 3 && String.compare (String.sub x 0 3) "pre" = 0) then
									(Pervasives.string_of_int (List.length spec_perm-1))
								else x)
							spec
					else
						Predicate.map_fields
							(fun x -> 
								if (String.length x >= 4 && String.compare (String.sub x 0 4) "post" = 0) then
									(Pervasives.string_of_int (i+1))
								else x)
								(Predicate.map_fields
								(fun x -> 
								if (String.length x >= 3 && String.compare (String.sub x 0 3) "pre" = 0) then
									(Pervasives.string_of_int i)
								else x)
								spec) 
					) spec_perm
				) in
			let composed_spec = List.fold_left (fun res sp -> 
				Predicate.implies (res, sp)) (List.hd allspecs) (List.tl allspecs) in
			(*let _ = Misc.pp "@.prepared composed spec %a@." Predicate.pprint composed_spec in*)
			let (_, _, _, rid, _, _) = List.hd specs in 
			let checking_result = check precondition postcondition (rid, composed_spec) in
			if (checking_result) then
				List.iter (fun (b, evname, t_desc, rid, spec, lbs) ->
					add pool hp_launch evname loc precondition postcondition b t_desc lbs 
					) specs
			else ();
			checking_result
			) spec_perms
	end else false
	
	
(** Given the set of updates along a program path, checks well-formness constraint.
 *  Two important condition: helping launch and helping completion
 *  1) If an instruction is to set program state implying helping launch then the state
 *  before cannot imply helping launch;
 *  2) If an instruction is to set program state implying helping completion then the state
 *  before cannot imply helping completion;
 *  3) The states after witness cannot imply helping launch
 *)	
let check_well_formness evname returnloc effs witloc hp_launch g_fun_ht exe = 
	let imply p1 p2 = 
		let result = TheoremProver.implies p1 p2 in
		(*let _ = Misc.pp "The implying result is %b\n" result in*)
		(TheoremProver.finish (); result) in
	
	let un_intersect p1 p2 = 
		let p = Predicate.Not (Predicate.And (p1, p2)) in
		let result = TheoremProver.implies Predicate.True p in
		(*let _ = Misc.pp "The un_intersection result is %b\n" result in*)
		(TheoremProver.finish (); result) in
	
	(*let _ = Misc.pp "Validating the wellformness for %s at
		return loc %s\n" evname (Location.lineno_to_string returnloc) in*)
		
	
	if (Hashtbl.mem hp_launch evname) then 		
	let hp_launch = Predicate.big_or (Hashtbl.find hp_launch evname) in	
	List.for_all (fun (loc, (_, pre, fld_assignments, lives, lp)) -> 
		let witloc = Location.lineno_to_int witloc in
		let loc = Location.lineno_to_int loc in 
		(*let _ = Misc.pp "Validating at loc %d\n"loc in*)
		
		let preconditions = flatten_condition pre in
		List.for_all (fun precondition -> 
			(*let _ = Misc.pp "checking a precondition at this site\n" in*)
			let postcondition = 
				match exe fld_assignments (Genarith.eprop_of_cprop precondition) with
			  | Some cq -> cq
			  | None -> (pp "@.Failed to prove linearizability@."; assert false) in
			let postcondition = List.map Genarith.cform_of_eform postcondition in
			
			let fi = Hashtbl.find g_fun_ht evname in
			let locals = fi.fun_lbs in
			
			let node = 
				try Some (getMyDescNode precondition locals )
				with _ -> None in
			match node with
			| None -> true
			| Some node -> begin
			let t_desc = match node with Csp_node (_, _, e, _) -> e | _ -> assert false in
			(*let vars = Exp.IdSet.inter 
								 (Assertions.prop_fv precondition Exp.IdSet.empty)
								 (Assertions.prop_fv postcondition Exp.IdSet.empty) in
			let vars = List.map E.id (Exp.IdSet.elements vars) in*)
			
			let vars = List.map E.id (Predicate.vars hp_launch) in
			
			let precondition = data_abstract precondition (t_desc::vars) [] locals in
			let precondition = subst precondition t_desc in
			let postcondition = data_abstract postcondition (t_desc::vars) [] locals in
	    let postcondition = subst postcondition t_desc in		
	
			if (loc > witloc) then (** prove no path after witness should set hp_launch *)
				let r = (not (imply hp_launch precondition)) && (not (imply hp_launch postcondition)) in
				(if (not r) then Misc.pp "Fail to check wellformness at loc %d for returnloc %d with wit as %d@." 
				loc (Location.lineno_to_int returnloc) witloc; r)
			else if (loc = witloc) then true 
			else begin
				(*let _ = Misc.pp "checking launch property for the precondition\n" in*)
				let r1 = 
					if (imply hp_launch postcondition) then
						if (un_intersect hp_launch precondition) then true
						else false
					else true in
				(*let _ = Misc.pp "checking completion proprty for the precondition\n" in*)
				let r2 = 
					if (imply (Predicate.Not hp_launch) postcondition) then
						if (un_intersect (Predicate.Not hp_launch) precondition) then true
						else false
					else true in
				(** if one of r1 and r2 are not true report false *)
				let r = r1 && r2 in
				(if (not r) then Misc.pp "Fail to check wellformness at loc %d for returnloc %d@." 
				loc (Location.lineno_to_int returnloc); r)
			end	end
		) preconditions
	) effs
	else true (* This is never helped so no check needed *)
	