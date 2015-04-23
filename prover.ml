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
open Exp
open Assertions
open Indpreds

(* -------------------------------------------------------------------------- *)
(** {2 Print debug information} *)
(* -------------------------------------------------------------------------- *)

let verbose = ref 0

let args =
  [("-vProver", Arg.Set_int verbose, "<n> Display internal information (prover)")]


let using_induction () =
  if !verbose > 1 then pp "USING INDUCTION@."

let print_entailment uf1 uf2 =
  if !verbose > 0 then
    pp "Entailment:@.@[<hv>@[<hov 2>%a@]@ |-@ @[<hov 2>%a@]@]@."
      pp_uform uf1 pp_uform uf2

let print_subtraction_entailment p1 sl1 p2 sl2 =
  if !verbose > 2 then
    pp "Subtraction Entailment:@.@[<hv>@[<hov 2>%a@]@ |-@ @[<hov 2>%a@]@]@."
      pp_uform (p1,sl1) pp_uform (p2,sl2)

let print_rule s =
  if !verbose > 1 then pp "[RULE %s]@." s

(* -------------------------------------------------------------------------- *)
(** {2 Helper routines} *)
(* -------------------------------------------------------------------------- *)

let split_spatial filter sl =
  match spat_fold_spred (fun x res -> match res with None -> filter x >>= fun y -> Some(x,y) | Some _ -> res) sl None with
  | None -> raise Not_found
  | Some (sp,y) -> (y, spat_remove sl sp)

let node_filter nid e = function
  | Csp_node(_,nid',e',el') when nid'==nid && equal_exp e e' -> Some el'
  | _ -> None

let may_alloc_filter e = function
  | (Csp_listsegi(_,SINGLE _,e',_,_,_,Cem_PE,_) as sp) when equal_exp e e' -> Some sp
  | _ -> None

let ( @* ) = spat_star_one
let ( @& ) = Pure.conj_one
let ( @&& ) = Pure.conj

let node_component = component_of_string "Node"

(** Do not do any case splits *)
let easy_unroll epto sp pl sl = match sp with
   | Csp_node (_,s,_,fld) -> Some (s,epto,fld,pl,sl)
   | Csp_listsegi (tag,SINGLE (snode,cel),e1,f1,e2,f2,Cem_NE,el) ->
			assert (equal_exp e1 epto);
			let (e3,e4,nid,cel',pl') = unroll_node_lhs snode e1 in
			let e5 = E.gensym_str "myval" in
			let pl = E.eq e2 (E.list [e4;e5]) @& pl' @&& pl in
			if Pure.is_false pl then None 
			else
				Some (nid, epto, Fld.union cel' cel, pl,
	      	Csp_listsegi (tag,SINGLE(snode,cel),e3,f1,e5,f2,Cem_PE,el) @* sl)
   | Csp_listsegi (tag,k,e1,f1,e2,f2,Cem_NE,el) ->
      if equal_exp e1 epto then 
				begin (* unroll from lhs *)
					let split_id = E.gensym_str "split" in
					let cel = match k with 
	  				| SINGLE _ -> assert false
	  				| DOUBLE(t1,t2) -> Fld.two t1 split_id t2 e2
	  				| XOR(t1) -> Fld.one t1 (E.xor [split_id; e2]) in
					Some (node_component, epto, cel, pl, Csp_listsegi (tag,k, split_id, f1,e1,f2,Cem_PE,el) @* sl)
      	end 
			else 
				begin assert(equal_exp f2 epto); (* unroll from rhs *)
					let _ = using_induction () in
					let split_id = E.gensym_str "split" in
					let cel = match k with 
	  				| SINGLE _ -> assert false
	  				| DOUBLE(t1,t2) -> Fld.two t1 f1 t2 split_id 
	  				| XOR(t1) -> Fld.one t1 (E.xor [split_id; f1]) in
					Some (node_component, epto, cel, pl, Csp_listsegi (tag,k,e1,f2,e2,split_id,Cem_PE,el) @* sl)
      	end
  | Csp_arr (tag,e1,e2,ev,fld,_,ds) ->
      assert (equal_exp e1 epto);
      let ev1 = E.gensym_str "myval" in
      let ev2 = E.gensym_str "myval" in
      let ev3 = E.gensym_str "myval" in
      let pl = E.eq ev (E.list [ev1;E.item ev2;ev3]) @& E.leq e1 epto @& E.ltn epto e2 @& pl in
      if Pure.is_false pl then None else
      Some (node_component, epto, Fld.union (Fld.one Misc.list_data_tag ev2) fld, pl,
            Csp_arr (tag,e1,epto,ev1,fld,Cem_PE,ds) @*
            Csp_arr (tag,E.add epto E.one,e2,ev3,fld,Cem_PE,ds) @* sl)
  | _ -> None

let easy_ptsto e (pl,sl) =
  let e = (Pure.to_sub pl) e in
  spat_get e sl >>= fun (sp,sl) ->
  easy_unroll e sp pl sl

let cons_opt ao b = match ao with None -> assert false | Some a -> Some (a::b)

let cmap_option f l =
  let add ao b = 
    ao >>= fun a -> 
    f b >>= fun x ->
    Some (List.rev_append x a) in
  List.fold_left add (Some []) l >>= fun l' ->
  Some (List.rev l')

let rec aggr_expose_ptsto e (pl,sl) =
  let e = (Pure.to_sub pl) e in
  spat_get e sl >>= fun (sp,sl) ->
  match sp with
    | Csp_listsegi(tag,(SINGLE _ as k),x,y,v,w,Cem_PE,ds) ->
			let pl' = E.eq x y @& E.eq v E.empty_list @& pl in
			cmap_option (aggr_expose_ptsto e) (normalize_uform (pl', sl))
				>>= cons_opt (easy_unroll e (Csp_listsegi(tag,k,x,y,v,w,Cem_NE,ds)) pl sl)
    | Csp_listsegi(tag,((DOUBLE _ | XOR _) as k),x,y,x',y',Cem_PE,ds) ->
			let pl' = E.eq x y @& E.eq x' y' @& pl in
			cmap_option (aggr_expose_ptsto e) (normalize_uform (pl', sl))
				>>= cons_opt (easy_unroll e (Csp_listsegi(tag,k,x,y,x',y',Cem_NE,ds)) pl sl)
    | _ -> easy_unroll e sp pl sl >>= fun res -> Some [res]

let (@@) (x1,y1) (x2,y2) = (Pure.conj x1 x2,spat_star y1 y2)
let (%) ((pl,sl),scpl) pl' = ((Pure.conj pl' pl,sl),scpl)


(* give priority to psto's with existential lhs *)
let compare_can_spred csp1 csp2 =
  let lhs = function
    | Csp_listsegi (_,_,e,f,_,_,_,_) -> if existential_id f then (existential_id e, 2) else (existential_id e, 3)
    | Csp_node (_,_,e,_) -> (existential_id e, 1)
    | Csp_arr (_,e,_,_,_,_,_) -> (existential_id e, 3)
    | Csp_indpred (_,_,el) -> (List.exists existential_id el, 3)
  in compare (lhs csp1) (lhs csp2) 

(* unroll inductive predicates in sl using consequences of pl *)
let unroll_ip ~is_lhs pl sl =
  let rec g body = match body with
		| [] -> None
   	| (pl',(uf,PNil))::body -> (
			try
	  		if Pure.entails pl pl'
	  		then Some uf
	  		else g body
			with Not_found -> g body
		)
		| (pl',(uf,PCons _))::body -> assert false (* No boxes in inductive predicates *) 
	in
  let rec f sp = match sp with
    	| Csp_indpred (_,i,el) ->
				let body = (if is_lhs then instance_ip_lhs else instance_ip_rhs) (i,el) in
				(match g body with
	  			| None -> (Pure.ptrue,spat_one sp)
	  			| Some uf -> f_uf uf)
    	| sp -> (Pure.ptrue,spat_one sp)
  	and f_uf (p1,sl1) = 
    	spat_fold_spred (fun sp cf -> f sp @@ cf) sl1 (p1,spat_empty)
  in
  f_uf (Pure.ptrue,sl)

let unroll_ip_lhs pl sl =
  unroll_ip ~is_lhs:true pl sl

let unroll_ip_rhs pl sl =
  let (p1,sl1) = unroll_ip ~is_lhs:false pl sl
  in (p1, (*List.stable_sort compare_can_spred*) sl1)

(* -------------------------------------------------------------------------- *)
(** {2 Formula Normalization} *)
(* -------------------------------------------------------------------------- *)

let compare_component_cprop (s1,p1) (s2,p2) =
  let n = compare_component s1 s2 in if n <> 0 then n else
  compare_cprop p1 p2

let check_atom_entailment pl sl ca =
  Pure.entails_exp pl ca ||
  (match ca with
  | Efun1(Sfn_NOT,(Eeq _ as e)) ->
      normalize_uform (e @& pl, sl) = []
  | _ -> false)

let remove_derivable_neql sl pl =
  let neq_filter ca = not (check_atom_entailment Pure.ptrue sl ca) in
  Pure.filter neq_filter pl

let is_uneq pl e1 e2 = Pure.entails_exp pl (E.neq e1 e2)

let dset_notmem pl e ds = List.for_all (is_uneq pl e) (Dset.to_list ds)

let update_nonemp_and_disjoint_sets pl sl =
  let rec has_item = function
    | Efun1 (Sfn_item, _) -> true
    | Efun (Sfn_list, el) -> List.exists has_item el
    | _ -> false in    
  let rec f_sp res sp = match sp with
    | Csp_node(_,_,e1,_) -> e1::res
    | Csp_listsegi(_,SINGLE _,e1,_,_,_,_,_) -> e1::res
    | Csp_listsegi(_,(DOUBLE _ | XOR _),e1,_,e2,_,_,_) -> e1::e2::res
    | _ -> res in
  let rec go_sp what sp = match sp with
    | Csp_listsegi(tag,(SINGLE _ as k),e1,f1,e2,f2,ie,ds) ->
				let ie' = match ie with Cem_PE when is_uneq pl e1 f1 || has_item e2 -> Cem_NE | _ -> ie in
        let ds' = Dset.filter (fun x -> equal_exp x e1 || not (mem_exp x what)) ds in
				if ie' == ie && ds' == ds then sp 
				else Csp_listsegi(tag,k,e1,f1,e2,f2,ie',ds')
    | Csp_listsegi(tag,k,e1,f1,e2,f2,ie,ds) ->
				let ie = match ie with Cem_PE when is_uneq pl e1 f1 -> Cem_NE | _ -> ie in
        let ds = List.fold_left 
				(fun ds x -> if equal_exp e1 x || equal_exp e2 x then ds else Dset.add x ds) ds what in
        Csp_listsegi(tag,k,e1,f1,e2,f2,ie,ds)
    | sp -> sp in
  let alloc = List.fold_left f_sp [] sl in 
  map_sub (go_sp alloc) sl


(** [normal_form sl_frame cf] normalizes [cf] assuming that [sl_frame] holds separately. *)
let rec normal_form sl_frame ((pl,sl),scpl) : cprop =
  let (pl,sl) = (pl,spat_empty) @@ unroll_ip_lhs pl sl in
  match
    let sl = update_nonemp_and_disjoint_sets pl sl in
    let pl = remove_derivable_neql sl pl in
    let big_frame = (pl, spat_star sl sl_frame) in
    let fvsl = List.fold (spred_fold E.exfv) sl IdSet.empty in
    let f x p (pl, scpl) =
      match normal_cprop_inner big_frame p with
      | [] -> None 
      | ((pl',_),_)::cfl as p' ->
	  		let pl' = Pure.filter (fun e -> IdSet.subset (E.exfv e IdSet.empty) fvsl) pl' in
	  		let pl' = List.fold_left (fun pl' ((pl,_),_) -> Pure.common pl pl') pl' cfl in
	  		Some (pl' @&& pl, PCons (x, p', scpl))
				(*      | p' -> Some (pl, (x,p')::scpl) *) 
		in
    (* let scpl = PList.stable_sort compare_component_cprop scpl in ____________ TODO ___________________ *)
    PList.lifted_fold f scpl (pl, PNil) >>= fun (pl,scpl) -> Some (((pl,sl),scpl))
  with 
    | None -> cprop_false
    | Some cf -> normalize_cform cf

(** [normal_cprop sl_frame cp] normalizes [cp] assuming that [sl_frame] holds separately. *)
and normal_cprop sl_frame (cp : cprop) =
  aggr_remove_cform_duplicates
    (List.fold_append (normal_form sl_frame) cp [])

(** [normal_form_inner uf_frame cf] normalizes [cf] assuming that [uf_frame] holds separately. *)
and normal_form_inner (p_frame, sl_frame) ((p,sl),scpl) =
  let cp = normalize_cform ((p @&& p_frame,sl),scpl) in
  let cp = normal_cprop sl_frame cp in
  List.map (fun ((p,sl),scpl) -> ((Pure.simplify p_frame p,sl),scpl)) cp

(** [normal_cprop_inner uf_frame cp] normalizes [cp] assuming that [uf_frame] holds separately. *)
and normal_cprop_inner uf_frame (cp : cprop) =
  aggr_remove_cform_duplicates
    (List.fold_append (normal_form_inner uf_frame) cp [])

(** Entry point: normalize cform *)
let normal_cform cf = 
  normal_form spat_empty cf


(* -------------------------------------------------------------------------- *)
(** {2 Subtraction (frame inference)} *)
(* -------------------------------------------------------------------------- *)

let (@>) cel t =
  try Fld.get t cel
  with Not_found -> E.gensym_str_ex (string_of_component t)

let (@@&) e (p,sl) = normalize_uform (Pure.conj_one e p, sl)

let can_spred_leq csp1 csp2 =
  match can_spred_leq csp1 csp2 with
  | Enum 0 -> None
  | e -> Some e

(** Count the number of definitely allocated cells *)
let rec count_NE n sl = match sl with
  | [] -> 0 
  | (Csp_node _ | Csp_listsegi (_,_,_,_,_,_,Cem_NE,_)) :: sl -> count_NE (n + 1) sl
  | _ :: sl -> count_NE n sl 

(* Disjunction on the right *)
let rec subtract_right fr uf1 ufl2 = 
	(*let _ = pp "@.In subtract_right uf1:@.%a@." pp_uform uf1 in
	let _ = List.iter (pp "@.In subtract_right uf2:@.%a@." pp_uform) ufl2 in*)
	match ufl2 with 
  | [] -> raise No_frame_found
  | [(p2,sl2)] -> subtract_pre fr uf1 p2 [] sl2
  | (p2,sl2)::ufl2 ->
      (try subtract_pre fr uf1 p2 [] sl2
       with No_frame_found -> subtract_right fr uf1 ufl2)

(* Applies the cheap rules (those not involving case splits) first. *)
and subtract_pre fr uf1 p2 sl2a sl2b = match sl2b with
  | [] ->
      (* No more cheap rules, apply the more expensive rules... *)
      let (p1,sl1) = uf1 in
      let (p2,sl2a) = (p2,[]) @@ unroll_ip_rhs p1 sl2a in
      let p2 = if Pure.has_neql p2 then remove_derivable_neql (fr @ sl1) p2 else p2 in
      let sl2a = List.stable_sort compare_can_spred sl2a in
      subtract_slow fr p1 sl1 p2 sl2a
  | (Csp_node(_,nid,e,el) as sp)::sl' when not (existential_id e) ->
      begin match easy_ptsto e uf1 with
			| Some (nid',_,el',p1b,sl1b) when nid'==nid ->
			    print_rule "ptsto";
			    let fr = sp :: fr in
			    let ufl1 = normalize_uform (p1b,sl1b) in
			    let ufl2 = (Fld.subset el' el @@& (p2, List.rev_append sl' sl2a)) in
			    List.reduce_append
			      (fun uf1 -> 
				 			let sub = map_uform (Pure.to_sub (fst uf1)) in
				 			let ufl2 = List.reduce_append sub ufl2 in
				 			subtract_right fr uf1 ufl2)
			      ufl1
			| _ -> (* Fail immediately if the memory location is not present in the LHS *)
			    if List.for_all (function 
					       | Csp_node (_,_,e',_) | Csp_listsegi (_,_,e',_,_,_,_,_) -> not (equal_exp e e')
					       | _ -> true) (snd uf1) then
			      raise No_frame_found
			    else
			      subtract_pre fr uf1 p2 (sp::sl2a) sl'
      end
  | ((Csp_listsegi _ | Csp_arr _) as csp)::sl' 
      when List.exists (fun csp' -> can_spred_leq csp' csp <> None) (snd uf1) ->
      print_rule "frame"; (* Frame rule for lseg's and trees *)
      let (p1,sl1) = uf1 in
      let (ca,sl1b) = split_spatial (fun csp' -> can_spred_leq csp' csp) sl1 in
      subtract_right (csp::fr) (p1,sl1b) (ca @@& (p2, List.rev_append sl' sl2a))
  | sp::sl' -> subtract_pre fr uf1 p2 (sp::sl2a) sl'

(* Main subtraction function *)
and subtract_slow fr p1 sl1 p2 sl2 =
  print_subtraction_entailment p1 sl1 p2 sl2;
  match sl2 with
    | [] ->
			print_rule "try_axiom";
  		let p2 = Pure.simplify p1 p2 in
			if Pure.is_sat p2 then begin
	  		print_rule "axiom";
        cprop_uform (p2 @&& p1, sl1)
			end else
	  		let total = fr @ sl1 in
	  		let p2 = Pure.filter (fun e -> not (check_atom_entailment p1 total e)) p2 in
	  		if Pure.is_sat p2 then begin
	    		print_rule "axiom";
          cprop_uform (p2 @&& p1, sl1)
	  		end else if !verbose > 2 then begin
	    		pp "Total: %a@." pp_uform (p1,total);
	    		pp "Rest:  %a@." Pure.pp p2;
	    		raise No_frame_found
	  		end else
					(raise No_frame_found)
    | Csp_node (_,_,e,_) :: _ ->
			let (sp,sl1b) = 
			  try split_spatial (may_alloc_filter e) sl1
			  with Not_found -> raise No_frame_found
			in
			begin match sp with
			  | Csp_listsegi(tag,SINGLE (snode,fld),e1,f1,e2,f2,Cem_PE,ds) ->
			      print_rule "ptsto_expose";
			      let ufl1 = 
							(p1, Csp_listsegi(tag,SINGLE (snode,fld),e1,f1,e2,f2,Cem_NE,ds)::sl1b)
								:: normalize_uform (E.eq e1 f1 @& E.eq e2 E.empty_list @& p1,sl1b) in
			      let uf2 = (p2,sl2) in
			      List.reduce_append
							(fun uf1 ->
				   			let ufl2 = map_uform (Pure.to_sub (fst uf1)) uf2 in
				   			subtract_right fr uf1 ufl2) ufl1
			  | _ -> raise No_frame_found
			end
    | Csp_listsegi(tag,SINGLE(snode,cel0),e1,f1,e2,_,isEmp,ds)::sl' ->
			let ds = Dset.filter 
	  		(fun e -> 
	     		not (List.exists (function Csp_node(_,_,e1,_) -> equal_exp e e1 | _ -> false) fr))
	  		ds 
			in
			let rec g sl1a sl1b = match sl1b with
	  		| sp::sl1b ->
	      	begin match sp with
						| Csp_node(tag',nid,e,cel)
		    			when equal_exp e1 e (*&& dset_notmem p1 e ds*) ->
		    				print_rule "lseg_ptsto";
		    				let (e3,e4,nid',cel',pl_new) = unroll_node_rhs snode e 
								in
		    					if nid'==nid then begin
		      					let e5 = E.gensym_str_ex "VAL" in
		      					let pl_new = E.eq e2 (E.list [e4;e5]) @& pl_new @&& p2 in
		      					let cel' = Fld.union cel' cel0 in
		      					let sl_new = 
											Csp_node(tag',nid,e,cel') :: 
											Csp_listsegi (tag,SINGLE(snode,cel0),e3,f1,e5,E.zero,Cem_PE,ds) :: sl' 
										in
		      						subtract_right fr (p1,sl1) (normalize_uform (pl_new, sl_new))
		    					end else (* TODO -- List is empty *)
		      					assert false
						| Csp_listsegi(tag',SINGLE(snode',cel0'),e1',f1',e2',_,isEmp',ds')
            	when equal_exp e1' e1 && snode'==snode && Dset.subset ds ds' ->
		    				print_rule "lseg_lseg3";
		    				using_induction ();
		    				let e5 = E.gensym_str_ex "VAL" in
		    				let isEmp'' = match isEmp, isEmp' with Cem_NE, Cem_PE -> Cem_NE | _ -> Cem_PE in
		    				let pl_new = Fld.subset cel0' cel0 @& E.eq e2 (E.list [e2';e5]) @& p2 in
		    				let sl_new = Csp_listsegi(tag',SINGLE(snode,cel0),f1',f1,e5,E.zero,isEmp'',ds) ::sl' in
		    				subtract_right ((*sp::*)fr) (p1,List.rev_append sl1a sl1b) (normalize_uform (pl_new,sl_new))
						| _ -> g (sp::sl1a) sl1b
	      	end
	 		 | [] -> raise No_frame_found
			in
				if equal_exp e1 f1 then begin
	  			print_rule "emp_lseg";
	  			subtract_right fr (p1,sl1) (E.eq e2 E.empty_list @@& (p2, sl'))
				end
				else if existential_id e1 then raise No_frame_found
				else if existential_id f1 then 
	  			try  g [] sl1
	  			with No_frame_found ->
	    			print_rule "lseg_inst_guess";
            subtract_right fr (p1,sl1) (E.eq e1 f1 @@& (p2,sl2))
				else g [] sl1
    | Csp_listsegi(_,(DOUBLE _|XOR _),e1,f1,e2,f2,Cem_PE,_)::sl' when equal_exp e1 f1 && equal_exp e2 f2 ->
			print_rule "emp_lseg2";
			subtract_slow fr p1 sl1 p2 sl'
    | Csp_listsegi(tag,DOUBLE(t1,t2),e1,f1,e2,f2,isEmp,ds)::sl' ->
			let rec g sl1a sl1b = match sl1b with
	  	| sp::sl1b ->
	      begin match sp with
					| Csp_node(_,what,e,cel)
		    		when what==node_component && equal_exp e1 e && Fld.mem t2 e2 cel && is_uneq p1 e2 f2 && dset_notmem p1 e ds ->
		    		let e3 = cel @> t1 in
		    		subtract_slow fr p1 (List.rev_append sl1a sl1b) p2 (Csp_listsegi (tag,DOUBLE(t1,t2),e3,f1,e1,f2,Cem_PE,ds)::sl')
					| Csp_node(_,what,e,cel)  (* |-> on the rhs *)
		    		when what==node_component && equal_exp f2 e && Fld.mem t1 f1 cel && dset_notmem p1 e ds ->
		    		using_induction ();
		    		let e3 = cel @> t2 in
		    		subtract_slow fr p1 (List.rev_append sl1a sl1b) p2 (Csp_listsegi (tag,DOUBLE(t1,t2),e1,f2,e2,e3,Cem_PE,ds)::sl')
					| Csp_listsegi(_,DOUBLE(t1',t2'),e1',f1',e2',f2',isEmp',ds')
		    		when t1==t1' && t2==t2' && equal_exp e1 e1' && equal_exp e2 e2' && Dset.subset ds ds' ->
		    		using_induction ();
		    		let isEmp'' = match isEmp, isEmp' with Cem_NE, Cem_PE -> Cem_NE | _ -> Cem_PE in
		    		subtract_slow fr p1 (List.rev_append sl1a sl1b) p2 (Csp_listsegi(tag,DOUBLE(t1,t2),f1',f1,f2',f2,isEmp'',ds)::sl')
					| _ -> g (sp::sl1a) sl1b
	      end
	  	| [] -> raise No_frame_found
			in g [] sl1
    | Csp_listsegi(tag,XOR t1,e1,f1,e2,f2,isEmp,ds)::sl' ->
			let rec g sl1a sl1b = match sl1b with
	  		| sp::sl1b ->
	      	begin match sp with
						| Csp_node(_,what,e,cel)
		    			when what==node_component && equal_exp e1 e && is_uneq p1 e2 f2 && dset_notmem p1 e ds ->
		    			let e3 = cel @> t1 in
		    			subtract_slow fr p1 (List.rev_append sl1a sl1b) p2 (Csp_listsegi (tag,XOR t1,E.xor [e3; e2],f1,e1,f2,Cem_PE,ds)::sl')
						| Csp_node(_,what,e,cel)  (* |-> on the rhs *)
		    			when what==node_component && equal_exp f2 e && dset_notmem p1 e ds ->
		    			using_induction ();
		    			let e3 = cel @> t1 in
		    			subtract_slow fr p1 (List.rev_append sl1a sl1b) p2 (Csp_listsegi (tag,XOR t1,e1,f2,e2,E.xor [e3; f1],Cem_PE,ds)::sl')
						| Csp_listsegi(_,XOR t1',e1',f1',e2',f2',isEmp',ds')
		    			when t1==t1' && equal_exp e1 e1' && equal_exp e2 e2' && Dset.subset ds ds' ->
		    			using_induction ();
		    			let isEmp'' = match isEmp, isEmp' with Cem_NE, Cem_PE -> Cem_NE | _ -> Cem_PE in
		    			subtract_slow fr p1 (List.rev_append sl1a sl1b) p2 (Csp_listsegi(tag,XOR t1,f1',f1,f2',f2,isEmp'',ds)::sl')
						| Csp_listsegi(_,XOR t1',f2',e2',f1',e1',isEmp',ds') (* or the wrong way round *)
		    			when t1==t1' && equal_exp e1 e1' && equal_exp e2 e2' && Dset.subset ds ds' ->
		    			using_induction ();
		    			let isEmp'' = match isEmp, isEmp' with Cem_NE, Cem_PE -> Cem_NE | _ -> Cem_PE in
		    			subtract_slow fr p1 (List.rev_append sl1a sl1b) p2 (Csp_listsegi(tag,XOR t1,f1',f1,f2',f2,isEmp'',ds)::sl')
						| _ -> g (sp::sl1a) sl1b
	      	end
	  		| [] -> raise No_frame_found
			in g [] sl1
    | Csp_arr _ ::sl' -> raise No_frame_found (* TODO!!!!!!!!! FIXME *)
    | Csp_indpred (_,id,el)::sl' -> raise No_frame_found

(** [find_frame_uform fr uf1 uf2] returns [res] such that [cf * uf1 |- fr * uf2 * res] *)
let find_frame_uform fr uf1 uf2 =
  print_entailment uf1 uf2;
  let (p1, sl1) = uf1 in
  let (p2, sl2) = uf2 in
  (* 1. Fail if pure part unsatisfiable. *)
  let p2 = Pure.simplify p1 p2 in
  let _ = if Pure.is_false p2 || Pure.has_unsat_eq p2 then raise No_frame_found in
  (* 2. Fail if spatial part too long. *)
  let _ = if count_NE 0 sl1 < count_NE 0 sl2 then raise No_frame_found in
  aggr_remove_cform_duplicates
    (subtract_right fr uf1 (map_uform (Pure.to_sub p1) (p2,sl2)))


(** [find_frame_cprop fr cp1 cp2] returns [res] such that [fr * cp1 |- fr * cp2 * res] *)
let rec find_frame_cprop fr cp1 cp2 =
  let ff  ((pl1,sl1),scpl1) =
    let cp2 = map_cprop (Pure.to_sub pl1) cp2 in
    match List.reduce (fun (uf2,scpl2) res ->
			try 
		    let new_res = find_frame_uform fr (pl1,sl1) uf2 in
			  if PList.exists (fun s _ -> not (PList.mem_assq s scpl1)) scpl2 then
			    res
			  else 
			    let sl1fr = sl1 @ fr in
			    let go s cp res =
			      Pure.lifted_list_conj res 
						(fun () -> entails_cprop sl1fr (and_cprop_pure cp pl1) (PList.assq s scpl2)) 
					in
			    let (scpl3,scpl4) = PList.rev_partition (fun s _ -> PList.mem_assq s scpl2) scpl1 in
			    let pl = PList.fold go scpl3 [Pure.ptrue] in
			    let cfl = List.map (fun p -> ((p,spat_empty),scpl4)) pl 
					in
			    (cprop_star new_res cfl) @ res
			with No_frame_found -> res) cp2
    with [] -> raise No_frame_found | x -> x
  in
  aggr_remove_cform_duplicates
    (List.reduce_append ff (normal_cprop fr cp1))

(** [entails_cprop fr cp1 cp2] returns true if [cp1 * fr |- cp2 * fr] *)
and entails_cprop fr cp1 cp2 =
  try
    let res = find_frame_cprop fr cp1 cp2 in
    if !allow_leaks || is_cprop_empty res then
      List.map (fun ((p,_),_) -> p) res
    else []
  with No_frame_found -> []


(** [adv_entails_atom cp ca] *)
let adv_entails_atom (cp : cprop) ca =
  let ff ((pl1,sl1),scpl1) =
    check_atom_entailment pl1 sl1 ca
    || PList.exists (fun _ cp -> 
         List.for_all (fun ((pl2,sl2),_) -> 
           check_atom_entailment (Pure.conj pl1 pl2) (List.rev_append sl1 sl2) ca) cp) scpl1
  in
  List.for_all ff cp

(** Fresh universally quantified variables for use in the prover. *)
let normal_ids = idpool_new Id.gensym_str "!"

(** Return substitutions [(sub_unex,sub_toex)] to turn the existential
    variables of [cp] into normal variables and the converse. *)
let remove_reinstate_existentials_sub cp =
  idpool_combine2 normal_ids (prop_exfv cp IdSet.empty)

(** [find_frame_cprop fr cp1 cp2] returns [res] such that [cp1 * fr |- cp2 * fr * res]
    or raises No_frame_found *)
let find_frame_cprop fr cp1 cp2 =
	(*let _ = pp "@.In prover cp1:@.%a@." pp_cprop cp1 in
	let _ = pp "@.In prover cp2:@.%a@." pp_cprop cp2 in*)
  let (sub_unex,sub_toex) = remove_reinstate_existentials_sub cp1 in
  let cp1 = map_cprop sub_unex cp1 in
	(*let _ = pp "cp1 as @.%a@." pp_cprop cp1 in
	let _ = pp "cp2 as @.%a@." pp_cprop cp2 in *)
  let res = find_frame_cprop fr cp1 cp2 in
	(*let _ = pp "res as @.%a@." pp_cprop res in*)
  map_cprop sub_toex res

let expose_ptsto2 cp e =
  let gof (uf,scpl) res =
    match aggr_expose_ptsto e uf with 
      | None -> (uf,scpl)::res
      | Some l' -> List.fold (fun (s,e,fld,pl,sl) res -> ((pl,Csp_node(tag_default,s,e,fld) @* sl),scpl)::res) l' res in
(*  let cp = normal_cprop [] cp in *)
  let cp = List.reduce gof cp in
  (*normal_cprop []*) cp

let default_prover =
  { find_ptsto = (fun s e -> split_spatial (node_filter s e));
    expose_ptsto = expose_ptsto2;
    nf_cprop = normal_cprop;
    nf_cform = normal_cform;
    entails_cprop = entails_cprop [];
    find_frame_cprop = find_frame_cprop;
    adv_entails_atom = adv_entails_atom }

