(* Poling: Proof Of Linearizability Generator 
 * Poling is built on top of CAVE and shares the same license with CAVE 
 * See LICENSE.txt for license.
 * Contact: He Zhu, Department of Computer Science, Purdue University
 * Email: zhu103@purdue.edu
 *)

open Convert
open Assertions
open Exp
open Misc

(** Load user provided shape predicate from given qualifier file *)
let convert q (**: Parsetree.a_proposition*) = 
	let qs = Convert.convert_prop q Location.none
	in qs
	
let compare rtb1 rtb2 = 
	if (Hashtbl.length rtb1 = Hashtbl.length rtb2) then
		Hashtbl.fold (fun rid1 qs1 res ->
			if (res) then
				if (Hashtbl.mem rtb2 rid1) then
					let qs2 = Hashtbl.find rtb2 rid1
					in List.length qs1 = List.length qs2 
				else false
			else res
			) rtb1 true
	else false
	
(** Expand user provided cform to cprop *)
let expand_shape_qualifier cq = 
	let ((pl, sl),_) = cq in
	let rec expand sr sl = 
		match sl with
			| [] -> sr (* list of (can_spred list) *)
			| (sl_prefix, sl_suffix) :: sl -> (
					match sl_suffix with
						| [] -> expand ((sl_prefix) :: sr) sl
						| s :: sl_suffix -> (
								match s with
									| Csp_listsegi (tag, (SINGLE _ as k),e1,f1,e2,f2,Cem_PE,ds) -> 
										let s' = Csp_listsegi (tag,k,e1,f1,e2,f2,Cem_NE,ds) in
										let st = Exp.mk_single_subst (Exp.Id.of_exp e1) f1 in
										let s1 = (sl_prefix @ [s'], sl_suffix) in
										let s2 = (map_spat st sl_prefix, map_spat st sl_suffix) in
										expand sr (s1 :: (s2 :: sl))
									| _ -> expand sr ((sl_prefix @ [s], sl_suffix) :: sl)
							)
				) in 
	let sls = expand [] [([], sl)] in
	let result = List.map (fun sl -> ((pl, sl), PNil)) sls in
	let _ = pp "@.The expanded result is @.%a@." pp_cprop result in
	result
	

(**
   cp is provided by programmers.
	 cq is the symbolic execution result.
   Compute [cr] such that [cp |- eq * cr] 
*)
let subtract prover cp cq =
	(*let _ = pp "@.Qualifier subtracting cp @.%a@." pp_cprop cp in
	let _ = pp "@.Qualifier subtracting cq @.%a@." pp_cprop cq in*)
  let rec go l cf = match l with
    | [] -> raise No_frame_found
    | x::xl ->
			let cp1 = cprop_cform cf in
			let cp2 = cprop_cform x  in
			try
	  		let res = prover.find_frame_cprop [] cp1 cp2 in
	  		res
			with No_frame_found -> go xl cf in
  		aggr_remove_cform_duplicates (List.reduce_append (go cq) cp)	
			
let subtract1 prover cp cq =
	(*let _ = pp "@.Qualifier subtracting cp @.%a@." pp_cprop cp in
	let _ = pp "@.Qualifier subtracting cq @.%a@." pp_cprop cq in*)
  let rec go l cf = match l with
    | [] -> false
    | x::xl ->
			let cp1 = cprop_cform cf in
			let cp2 = cprop_cform x  in
			try
	  		let _ = prover.find_frame_cprop [] cp1 cp2 in
	  		true
			with No_frame_found -> go xl cf in	
	List.exists (go cq) cp
						
			
(** Qualifier elimination1 
*)
let eliminate1 prover rtb symb_eprop = 
	let cp = List.map (Genarith.cform_of_eform) symb_eprop in
	let rtbcopy = Hashtbl.copy rtb in
	Hashtbl.iter (fun rid cand_cforms -> 
		let cand_cforms = List.filter (fun ccf -> 
			try 
				let _ = pp "@.ccf as @.%a@." pp_cform ccf in
				let ccp = cprop_cform ccf in
				let gccp = cprop_cform (uform_empty, PCons (rid, ccp, PNil)) in
				(ignore (subtract prover cp gccp); true) 
			with _ -> false
		) cand_cforms in
		Hashtbl.replace rtbcopy rid cand_cforms
	) rtb;
	rtbcopy	

(** In place qualifier elimination *)		
(** @deprecated temporarily *)
let eliminate_inplace prover rtb symb_eprop = 
	let cp = List.map (Genarith.cform_of_eform) symb_eprop in
	let rtbcopy = Hashtbl.copy rtb in
	Hashtbl.iter (fun rid cand_cforms -> 
		let cand_cforms = List.filter (fun ccf -> 
			try 
				let _ = pp "@.ccf as @.%a@." pp_cform ccf in
				let ccp = cprop_cform ccf in
				let gccp = cprop_cform (uform_empty, PCons (rid, ccp, PNil)) in
				(ignore (subtract prover cp gccp); true) 
			with _ -> (pp "@.remove ccf @.%a@." pp_cform ccf; 
			false)
		) cand_cforms in
		Hashtbl.replace rtb rid cand_cforms
	) rtbcopy
		
		
(** Qualifier elimination 2
 *  Assumption: 
 *  1) qualifiers only specify possible bahaviors of global heap
 *  2) symb_eprop specify both the local and global heap
 *)		
let eliminate prover cand_cforms symb_eprop =  (*: cprop list -> eprop -> cprop list *)
	(** Test if p is an overapproximation of symb_eprop *)
	let test_cand cp1 cp2 = 
		let _ = pp "@.cp1:@.%a@." pp_cprop cp1 in
		let _ = pp "@.cp2:@.%a@." pp_cprop cp2 in
		try 
			let _ = subtract prover cp1 cp2 in 
			true
		with Assertions.No_frame_found -> (pp "@.test_cand failed@."; false) 
	in
	(** cp1 is made of user-provided shape qualifiers 
      cp2 is made of symbolic execution
		*)
	let rec rec_eliminate cps cp2 = 
		match cps with
			| [] -> cp2
			| cp :: cps' -> (
					if (test_cand cp cp2) then cp
					else rec_eliminate cps' cp2
				) 
	in
	let cand_cf_powerset = List.tl (Misc.List.power_set cand_cforms) in
	let cand_props = 
		List.map (fun cfl -> prover.nf_cprop [] (remove_cform_duplicates cfl)
			(*List.fold_left (fun res cf -> Assertions.cprop_star res cf) Assertions.cprop_empty cfl*)) 
		cand_cf_powerset in
	Genarith.ext_transform (fun cf ->
		(** FIXME: Local heap is ignored *)
		let (uf, scpl) = cf in
		let scpl = PList.map_val (fun cp ->
				rec_eliminate cand_props cp
			) scpl in
		cprop_cform (uf, scpl)
		) symb_eprop
		
(** Qualifiers should be instanitated before use *)
let instantiate cand_forms lv_vars = cand_forms
	(*let allvars = prop_fv cand_forms in
	let subvars = IdSet.elements (
		IdSet.filter (fun v -> (Char.compare "@" (Id.to_string v).[0] = 0)) allvars) in
	let sub_permutation = List.permute sub_vars in
	let sub = fun cf ->
		List.map (sub_permutation, fun perm ->
			Assertions.map_cform (mk_subst ()) cf
			) in
	let q_transform fn cp =
	  let transf cf res =
	  	match (fn cf) with
				| [cf] -> cf :: res
	      | cfl -> cfl @ res 
		in
	  	remove_eform_duplicates (List.reduce transf cp)
	in q_transform sub cand_forms*)
	
	
	
	
	
(**********************************************************)
(***************** Pure Qualifier API *********************)
(**********************************************************)

type pure_qualifier_t = string * string * Predicate.t

let transl_pure_qualifiers ps = 
	List.flatten (List.map (fun (name, p) -> (** ps' type is Parsetree.qualifier_declaration list *)
			Qualdecl.transl_pattern_valu name p
		) ps)
	
let print_pure_qual (name, valu, pred) = 
	Misc.pp "@.Qualifier %s with value %s: @.%a@." name valu Predicate.pprint pred

(**********************************************************)
(***************** Specification API **********************)
(**********************************************************)

type spec_t = string * Predicate.t

let transl_specifications specs = 
	List.map (fun (name, spec) -> (** spec's type is string * predicate_pattern *)
			(name, Qualdecl.transl_patpred_single spec)
		) specs
		
let print_spec (name, pred) = 
	Misc.pp "@.Function %s Specification: @.%a@." name Predicate.pprint pred
 
