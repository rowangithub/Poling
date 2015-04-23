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
(** Symbolic execution *)
open Misc
open Exp
open Assertions
open Commands
open Genarith

(* -------------------------------------------------------------------------- *)
(** {2 Shorthands} *)
(* -------------------------------------------------------------------------- *)

let (@%) ((pl,sl),scpl) pl' = ((Pure.conj pl' pl,sl),scpl)
let (@&) = Pure.conj_one
let (@@***) x y = eprop_star_assume x y
let (@@**) x y = eprop_star x y
let (@@&&) x y = cprop_pure x @@** y
let (@@&)  x y = Pure.one x @@&& y

let print loc = Location.print (!Misc.formatter) loc; pp 

let pp_generated_function fname n =
  if Genarith.enabled () then pp_function !Misc.formatter (fname,n)

let cform_to_sub ((p,_),_) = Pure.to_sub p

(* -------------------------------------------------------------------------- *)
(** {2 Arguments} *)
(* -------------------------------------------------------------------------- *)

(**
   If [verbose >= 1] 
   If [verbose >= 2], print loop invariants & actions inferred.
   If [verbose >= 3], print verification condition & action inference.
   If [verbose >= 4], print intermediate states.
   If [verbose >= 5], print stabilizations.
   If [verbose >= 6], print inferred frames.
*)
let verbose = ref 1

let left_mover_opt = ref false

(**
   If [infer >= 1], perform action inference.
   If [infer >= 2], perform linearization point inference. *)
let infer = ref 1

(** If [mcpa_infr >= 1], perform mcpa linearization point inference *)
let mcpa_infer = ref 0

let args = 
  [("-v",            Arg.Set_int verbose, "<n> Display internal information (symbolic execution)");
   ("-lm",           Arg.Set left_mover_opt, " Enable left mover optimization");
   ("-no_infer_RG",  Arg.Unit (fun () -> infer := 0), " Do not infer rely/guarantee specifications");
   ("-infer_RG",     Arg.Unit (fun () -> infer := 1), " Infer rely/guarantee specifications");
   ("-linear_reuse", Arg.Unit (fun () -> infer := 2), " Infer linearization points");
   ("-linear",       Arg.Unit (fun () -> infer := 3), " Infer linearization points");
	 ("-mcpa_linear",  Arg.Unit (fun () -> mcpa_infer := 1), " MCPA Infer linearization points")]
	
let qs_given = ref false
		
let ps_given = ref false

let inv_given = ref false


let pp_line () =
  if !verbose >= 1 then
    pp "----------------------------------------------------------------------------@."

let pp_comment s =
  if !verbose >= 1 then begin
    pp "@.";
    if Genarith.enabled () then pp "// ";
    pp "%s@." s
  end

let pp_internal_error () =
  pp "@.Internal error: please report.@."

(* -------------------------------------------------------------------------- *)
(** {2 Error handling} *)
(* -------------------------------------------------------------------------- *)

(** Internal exception *)
exception Symbolic_execution_error

let error_noframe loc s cp1 cp2 =
  if !verbose >= 1 then 
    print loc "ERROR cannot find frame: %s@.@[<hv>@[<hov 2>%a@]@ |-@ @[<hov 2>%a@]@]@." s 
      pp_cprop cp1 pp_cprop cp2;
  raise Symbolic_execution_error

let error_noframe_ext loc s ep1 cp2 =
  error_noframe loc s (List.map cform_of_eform ep1) cp2

let test_leakmem ?(warn=true) loc cp =
  if is_cprop_empty cp then ()
  else if !allow_leaks then begin
    if !verbose >= 1 && warn then
      (*print loc "WARNING memory leak:@.%a@." pp_cprop cp*) ()
    else ()
  end else begin
    if !verbose >= 1 then print loc "ERROR memory leak:@.%a@." pp_cprop cp;
    raise Symbolic_execution_error
  end

let error_heap loc e ep =
  if !verbose >= 1 then
    print loc "ERROR: %a is possibly unallocated in@.%a@." 
      pp_exp e pp_eprop ep;
  raise Symbolic_execution_error

let error_heap2 loc s ep =
  if !verbose >= 1 then 
    print loc "ERROR: %s with precondition@.%a@." s pp_eprop ep;
  raise Symbolic_execution_error


(* -------------------------------------------------------------------------- *)
(** {2 Global variables} *)
(* -------------------------------------------------------------------------- *)

type global_env = 
  { g_prover : prover
  ; g_abstraction : abstraction
  ; g_globals : IdSet.t
  ; g_fun_ht : (string, fun_info) Hashtbl.t
  ; g_res_ht : (component, act list) Hashtbl.t
  ; g_renv   : (component, cprop) Hashtbl.t
  ; mutable g_guarantee : 
      (component * (string * Pure.t * can_spatial * can_spatial * can_spatial)) list
  ; mutable g_guar_changed : bool
  ; mutable g_params : IdSet.t
  ; mutable g_no_interf_hack : bool   (** Assume no interference occurs *)
  ; g_linear_pre : cprop option    (** Fail quickly for linearizability checking *)
	; cand_lin_point : (string, 
	  (** 1 eff loc 2 precondition 3 exe st 4 valid lp?*)
		(Location.t * (Predicate.t * (Location.t * 
			(Predicate.t list * cprop * fld_assignments * IdSet.t * bool)) list)) list) Hashtbl.t  
		(** Remember the effectful linearization points *)
	; non_eff_postconditions : (string, 
		(** 1 return loc, 2 pureinfo 3 noneff witnesses *)
		(Location.t * (Predicate.t * (Location.t * cprop) list)) list) Hashtbl.t
  ; rdefs : (component, Predicate.t) Hashtbl.t (** The user defined concrete set function *)
	; spec_pool : Specpool.t (** The spec pool *)
	; hp_launch : Specpool.hp_launch (** The helping mechanism enablement *)
	; seq_table : (Location.t, cprop) Hashtbl.t (** sequnential information *)
	}

let ident_ABS       = Id.create "ABS"
let ident_ABS_value = Id.create "ABS_value"

(** total number of iterations for all the calls to mk_stable_single *)
let stabilisation_iterations = ref 0

(** Checker for pure linearization points *)
let linear_pure_code = ref []

let udom_false = udom_of_uform_list []

let normalize_uforms_aggr =
  List.reduce 
    (fun (p,sl) res -> 
       List.fold_append (fun p -> normalize_uform (p,sl))
         (Pure.normalize_aggr p) res)

(** Return [true] if the correlation between the abstract state and
    the concrete state been broken. *)
let linear_bad_invariant (p,sl) =
  let (sl1,sl2) = List.partition 
    (function Csp_node(_,_,i,_) -> i == E.id ident_ABS | _ -> false)
    sl in
  let sl1_fv = List.fold
    (fun sp r -> match sp with Csp_node(_,_,_,fld) -> 
       Fld.fold (fun t e r -> if t == Misc.list_data_tag then E.exfv e r else r) fld r | _ -> r)
    sl1 IdSet.empty in
  let sl2_fv = spat_fold E.exfv sl2 IdSet.empty in
  not (IdSet.subset sl1_fv sl2_fv)

let linear_abs_pre = 
  (Pure.ptrue, [Csp_node(tag_default, node_component, E.id ident_ABS,
                        Fld.one Misc.list_data_tag (E.id ident_ABS_value))])

let str_is_fair x     = Str.string_match (Str.regexp_string "fair") x 0
let str_is_cutpoint x = (x = "cutpoint")

let cutpoint_counter  = ref 0

let next_cutpoint () =
  incr cutpoint_counter;
  "CUTPOINT_" ^ string_of_int (!cutpoint_counter)

(** Given an eprop, expose [e|->_] in each disjunct. *)
let ext_expose_ptsto prover e ep =
  ext_transform
    (fun cf -> prover.expose_ptsto (cprop_cform cf) e)
    ep

(** Put [ep] into normal form *)
let ext_normalize prover ep =
  ext_transform
    (fun cf -> prover.nf_cprop [] (cprop_cform cf))
    ep

(** Compute [er] such that [ep |- cq * er] *)
let ext_subtract prover ep cq =
  ext_transform
    (fun cf -> prover.find_frame_cprop [] (cprop_cform cf) cq)
    ep

(** Compute [cr] such that [ep |- eq * cr] *)
let ext_ext_subtract prover ep eq =
  let rec go l cf = match l with
    | [] -> raise No_frame_found
    | x::xl ->
	let cp1 = cprop_cform (cform_of_eform cf) in
	let cp2 = cprop_cform (cform_of_eform x)  in
	try
	  let res = prover.find_frame_cprop [] cp1 cp2 in
	  put_edge_skip(*TODO*) cf x;
	  res
	with No_frame_found -> go xl cf in
  aggr_remove_cform_duplicates 
    (List.reduce_append (go eq) ep)

(** Calculate postcondition after executing a generic command *)
let execute_gen_cmd prover (modif,cp,cq,s',loc) epre =
  let epre = ext_append_assign (IdSet.fold (fun x r -> (x,None)::r) modif []) epre in
  let sub_modif = mk_gensym_garb_subst_idset modif in	
  let fr =
    try ext_subtract prover epre cp
    with No_frame_found -> error_noframe_ext loc s' epre cp in
  (if !verbose >= 6 then
     print loc "FRAME inferred:@.@[<hov 2>%a@]@." pp_eprop fr);
  cq @@*** map_eprop sub_modif fr

(** find the pure part of a proposition *)
let pure_part ep = 
  (*let intersection pl pl' = Pure.filter (fun ca -> mem_atom ca pl) pl' in *)
  let rec go = function
    | [] -> Pure.ptrue
    | [n] -> fst (fst (cform_of_eform n))
    | n::cfl -> Pure.ptrue (*intersection pl (go cfl)*) in
  go ep


(** Simple symbolic execution for pure linearization checkers & eff. specs *)
let rec linear_symbexe prover c vars ufl = match c with
  | [] ->
      let sub = mk_gensym_garb_subst_idset vars in
      List.reduce_append (map_uform sub) ufl
  | c0 :: c -> begin match c0.can_st_desc with 
      | Cst_nondet (c1,c2) ->
	  linear_symbexe prover (c1 @ c) vars ufl
	  @ linear_symbexe prover (c2 @ c) vars ufl
      | Cst_kill ids ->
	  let sub = mk_gensym_garb_subst_idset ids in
	  let ufl = List.reduce_append (map_uform sub) ufl in
	  linear_symbexe prover c (IdSet.diff vars ids) ufl
      | Cst_assign (x,e) ->
	  let sub = mk_gensym_garb_subst x in
	  let eq = E.eq (E.id x) (sub e) in
	  let ufl = List.reduce
	    (fun uf res -> List.fold_append
	       (fun (p,sl) -> normalize_uform (eq @& p,sl))
	       (map_uform sub uf) res) ufl in
	  linear_symbexe prover c (IdSet.add x vars) ufl
      | Cst_fldlookup (_rgnl,x,e,t) ->
	  let ufl = List.reduce
	    (fun (p,sl) res ->
	       let sub = mk_gensym_garb_subst x in
	       let e = Pure.to_sub p e in
	       try
		 let (cel,_) = prover.find_ptsto node_component e sl in
		 let eq = E.eq (E.id x) (sub (Fld.get t cel)) in
		 List.fold (fun uf res -> List.fold_append
			     (fun (p,sl) -> normalize_uform (eq @& p,sl))
			     (map_uform sub uf) res)
		   ufl res
	       with Not_found -> List.fold_append (map_uform sub) ufl res)
	    ufl in
	  linear_symbexe prover c (IdSet.add x vars) ufl
      | Cst_assume cp ->
	  let ufl = List.reduce
	    (fun ((p_new,_),_) res -> List.fold
	       (fun (p,sl) res -> 
		  List.fold_append (fun p -> normalize_uform (p,sl))
		    (Pure.normalize_aggr (Pure.conj p_new p))
		    res)
	       ufl res)
	    cp in
	  linear_symbexe prover c vars ufl
      | Cst_assume_exp e ->
          let p_new = Pure.one e in
	  let ufl = List.reduce
	       (fun (p,sl) res -> 
		  List.fold_append (fun p -> normalize_uform (p,sl))
		    (Pure.normalize_aggr (Pure.conj p_new p))
		    res) ufl in
	  linear_symbexe prover c vars ufl
      | Cst_fldassign (_rgnl,[(e1,t,e2)],_) ->
	  let ufl = List.reduce
	    (fun (p,sl) res ->
	       let e1 = Pure.to_sub p e1 in
	       try
		 let (cel,rest) = prover.find_ptsto node_component e1 sl in
		 let cel' = Fld.set t (Pure.to_sub p e2) cel in
		 (p, Csp_node (tag_default, node_component, e1, cel') :: rest) :: res
	       with Not_found -> pp_internal_error (); assert false (*TODO*))
	    ufl in
	  linear_symbexe prover c vars ufl
      | Cst_assert_exp _ 
      | Cst_fcall2 _ -> (*TODO---------------------------HACK_______________ *)
	  linear_symbexe prover c vars ufl
      | Cst_fldassign _ | Cst_new _ | Cst_dispose _ | Cst_pfcall _ 
      | Cst_action_begin _ | Cst_action_end _ | Cst_interfere _ 
      | Cst_stabilize _ | Cst_loop _ | Cst_goto _ | Cst_comment _ ->
          pp_internal_error ();
          pp "Linear cmd: %a@." pp_cmd (c0::c);
          assert false
    end

(** Calculate post-condition outside block *)
let exit_from_block prover (rid,modif_body,cq0,loc) cq =
  let rec remove_box rid = 
    ext_transform 
      (fun (uf,scpl) -> cprop_cform (uf, PList.remove_assq rid scpl)) in
  let get_shared n cq_shared =
    let cf = cform_of_eform n in
    let fr = try PList.assq rid (snd cf) 
             with Not_found -> pp_internal_error (); assert false in
    cprop_or cq_shared (and_cprop_pure (cprop_star fr cq0) (fst (fst cf))) in
  let cq_local = (* local part of post-condition *) 
    try ext_subtract prover cq cq0
    with No_frame_found -> error_noframe_ext loc "action exit" cq cq0 in
  let cq_shared = List.reduce get_shared cq_local in
  let cq_shared = and_cprop_pure cq_shared (pure_part cq_local) in
  let sub = mk_gensym_garb_subst_idset modif_body in
  let cq_local = remove_box rid cq_local in
  let cq_local = map_eprop sub cq_local in
  let cq = cprop_box rid cq_shared @@*** cq_local in
  let cq = 
    let cq_local = List.map cform_of_eform cq_local in
    let sub = mk_gensym_garb_subst_idset (prop_exfv cq_local IdSet.empty) in
    map_eprop sub cq in
  ext_normalize prover cq

(** A bogus assertion, used when abstraction raises [Junk]. *)
let junk_node =
  cprop_spred
    [Csp_node(tag_default,component_of_string "Junk",E.id Id.junk,Fld.emp)]

(* FIXME: this is a hack to avoid branches instead of the 
   straightforward [linear_symbexe prover (!linear_pure_code)].
 *)
let exec_pure_lin_checker env =
  match !linear_pure_code with [] -> identity | _::_ ->
  List.reduce
    (fun uf acc ->
       if Pure.to_sub (fst uf) (E.id ident_lin_res) == E.undef then
         let res = 
           linear_symbexe env.g_prover (!linear_pure_code) IdSet.empty [uf] 
           |> normalize_uforms_aggr
         in
         match res with [uf] -> uf :: acc
         | [] -> acc
         | (p,_)::ufl' -> 
           let pcomm = List.fold (fun (p,_) res -> Pure.common p res) ufl' p in
	   let (res_cr, res_o) = 
             List.partition (fun (p,_) -> Pure.has_can_return (Pure.simplify pcomm p)) res in
           match res_cr, res_o with
	     | _::_, _::_ -> res@acc
             | _ -> 
	   (* pp "ex_p: %a@.all: %a@."
             pp_cprop (cprop_pure pcomm) 
             pp_cprop (List.map (fun uf -> (uf,PNil)) res) ; *)
           (Pure.conj pcomm (fst uf), snd uf) :: acc
       else uf :: acc)

(** [make_stable cp rely] returns a [cp'] such that [cp |- cp'] and [stable_under cp rely] *)
let make_stable env cp actl = 
  let uform_list_to_cprop ufl = List.map (fun uf -> (uf,PNil)) ufl in

  (** Pseudo-fix-point calculation for stability under a single action *)
  let rec mk_stable_single act cou (udom, ufl_new) =
    if ufl_new = [] || cou >= 4 then udom else begin
      incr stabilisation_iterations;
      let _ =
	if !verbose >= 5 then 
	  pp "interf %s@ new: %a@." (act_name act) pp_cprop (uform_list_to_cprop ufl_new)
	else if !verbose >= 4 then
	  pp "interf %s@ new: %d@." (act_name act) (List.length ufl_new)
	else ()
      in
      (* 1. Calculate effect of a single interference step *)
      let ufl' =
        ufl_new
        |> uform_list_to_cprop
        |> interfere_once env.g_prover act
        |> List.map fst
        |> normalize_uforms_aggr
        |> exec_pure_lin_checker env
      in
      (* 2. Join *)
      let res = env.g_abstraction.uform_join udom ufl' in
      (* Fail quickly on unpromising lin. points *)
      let _ = (* TODO ---------- *)
	if (env.g_linear_pre != None) && List.exists linear_bad_invariant (snd res) then begin
          if !verbose >= 1 then begin
	    pp "The current resource invariant looks unpromising for proving linearizability.@.";
	    List.iter (pp "AAA: %a@." pp_uform) ufl_new;
	    List.iter (pp "BBB: %a@." pp_uform) ufl';
	    List.iter (pp "CCC: %a@." pp_uform) (snd res);
	    List.iter (pp "BAD INV: %a@." pp_uform) (List.filter linear_bad_invariant (snd res));
          end;
	  raise Symbolic_execution_error 
	end in
      let _ =
	if !verbose >= 5 then 
	  pp "res: %a@." pp_cprop (uform_list_to_cprop (snd res))
      in
      (* 3. Repeat until fixed point *)
      mk_stable_single act (cou + 1) res
    end in
 
  (** Fix-point calculation for stability under a list of actions *)
  let rec mk_stable n (udom, ufl_new) =
    if ufl_new = [] then udom else begin
      let _ = 
	if !verbose >= 4 then begin
	  let ufl = uform_list_of_udom udom in
          pp "go2(%d,%d,%d)@." n (List.length ufl)(List.length ufl_new);
	  if !verbose >= 5 then
            pp "old: %a@ new: %a@." 
              pp_cprop (uform_list_to_cprop ufl)
              pp_cprop (uform_list_to_cprop ufl_new)
	end in
      (uform_list_of_udom udom, [])          (* TODO: Ugly -- breaks module abstraction!!! *)
      |> List.fold (fun act udom -> mk_stable_single act 0 (udom, ufl_new)) actl
                                             (* Stabilize each action separately *)
      |> uform_list_of_udom
      |> env.g_abstraction.uform_join udom   (* Join with existing domain *)
      |> mk_stable (n+1)                     (* Repeat until fixpoint *)
    end in

  (if !verbose >= 5 then pp "make_stable @ %a@." pp_cprop cp);
  try
    cp
    |> aggr_kill_garbage_vars             (* Turn useless vars into existentials *)
    |> env.g_prover.nf_cprop []
    |> List.map fst
    |> normalize_uforms_aggr
    (* |> exec_pure_lin_checker env *)
    |> env.g_abstraction.uform_join udom_false  (* Do an initial abstraction *)
    |> mk_stable 0                              (* Calculate fix-point *)
    |> uform_list_of_udom
    |> uform_list_to_cprop
  with Junk -> junk_node


(** computes the fixpoint of a transformation from propositions to
    propositions, such as the symbolic execution function *)
let compute_transf_fixpoint env (transf: eprop -> eprop) ep =
  let rec fix ep_total ep ep_new =
    if ep_new = [] then ep
    else 
      let ep_new = transf ep in
      let (ep_total,ep,ep_new) = env.g_abstraction.prop_join ep_total ep ep_new in
      let _ = if !verbose >= 3 then pp "@.LOOP ADDING:@.%a@." pp_eprop ep_new in
      fix ep_total ep ep_new
  in
  try
    (* 1. Do an initial abstraction *)
      (* This step is optional: abstracts the initial value.
         Intuitively it should speed up the analysis slightly.
         In practice, it does not affect performance in the 3 list algorithms. *)
    let ep = env.g_abstraction.prop_abs ep in
    let _ = if !verbose >= 3 then pp "@.LOOP STARTING:@.%a@." pp_eprop ep in
    (* 2. Calculate fix-point *)
    let pfix = fix ep ep ep in
    let _ = 
      if !verbose >= 2 && not (Genarith.enabled ()) then 
        if env.g_no_interf_hack then 
	  pp "@.LOOP NO-INTERFERENCE INV:@.%a@." pp_eprop pfix 
        else
	  pp "@.FOUND LOOP INVARIANT:@.%a@." pp_eprop pfix in
    pfix
  with
    Junk -> eprop_of_cprop junk_node
		
(** computes the fixpoint of a transformation from propositions to
    propositions using user provided qualifiers only *)
(*let compute_transf_qs_fixpoint env (transf: eprop -> eprop) ep rs qs =
	let rtb = Hashtbl.create 16 in
	let _ = List.iter (fun r -> Hashtbl.add rtb r qs) rs in
	(* From qs to cprop *)
	let cprop_of_qs qs = 
		List.fold_left (fun res q -> cprop_star res (cprop_cform q)) Assertions.cprop_empty qs in
	(* Carefully add candidate invariants *)
	let init_inv cp rtb =
  	let add_inv rid qs ((uf,scpl) as cf) = 
    	if PList.mem_assq rid scpl then cf
    	else (uf, PCons (rid, cprop_of_qs qs, scpl)) in
		ext_transform (fun cf -> [Hashtbl.fold add_inv rtb cf]) cp in
	let rec fix rtb = 
		(* modify ep to add resource candidate inv *)
		let ep = init_inv ep rtb in 
		let ep_new = transf ep in
		(*let ep_new = env.g_abstraction.prop_abs ep_new in*)
		let _ = pp "@.Begin eliminating...@." in
		let rtb' = Qualifier.eliminate1 env.g_prover rtb ep_new in 
		let _ = pp "@.End eliminating...@." in
		if (Qualifier.compare rtb rtb') then rtb
		else fix rtb'	 
	in
  try
    (* 1. Do an initial abstraction *)
      (* This step is optional: abstracts the initial value.
         Intuitively it should speed up the analysis slightly.
         In practice, it does not affect performance in the 3 list algorithms. *)
    let ep = env.g_abstraction.prop_abs ep in
    let _ = if !verbose >= 3 then pp "@.LOOP STARTING:@.%a@." pp_eprop ep in
    (* 2. Calculate fix-point *)
    let pfix = init_inv ep (fix rtb) in
    let _ = 
      if !verbose >= 2 && not (Genarith.enabled ()) then 
        if env.g_no_interf_hack then 
	  			pp "@.LOOP NO-INTERFERENCE INV:@.%a@." pp_eprop pfix 
        else
	 		 		pp "@.FOUND LOOP INVARIANT:@.%a@." pp_eprop pfix in
    pfix
  with
    Junk -> eprop_of_cprop junk_node*)


(** Compute [eq] such that [ep |- eq] and [stable_under ep rely] *)
let stabilize env (rid,rely) ep =
  let get_shared rid (uf,scpl) = 
		try
      ((uf, PList.remove_assq rid scpl), PList.assq rid scpl)
    with Not_found -> pp_internal_error (); assert false 
	in
  let ep =
    let cp = List.map cform_of_eform ep in
    map_eprop (existentials_rename_sub (prop_exfv cp IdSet.empty)) ep 
	in
  let eq = (* post-condition outside block *)
    ext_transform (fun (cf : cform) ->
      let (cf_local,cp_shared) = get_shared rid cf in
      let (sub_unex,sub_toex) = existentials_rename_tonormal_sub (form_exfv cf_local IdSet.empty) in
      let cp = map_cform sub_unex cf_local in
      let cp_2 = map_cform sub_unex ((Pure.ptrue,snd(fst cf_local)),PNil) in
      let cp_shared = 
        try map_cprop sub_toex (env.g_prover.find_frame_cprop [] (cprop_star cp cp_shared) cp_2)
        with No_frame_found -> 
	  			pp_internal_error ();
          pp "cp_shared: %a@." pp_cprop cp_shared;
	  			pp "cf_local: %a@." pp_cform cf_local;
          assert false 
			in
      let cp_shared = make_stable env cp_shared rely in
      cprop_cform (fst cf_local, PCons (rid, cp_shared, snd cf_local))) ep
  in
  (if !verbose >= 5 then
     pp "Stabilisation result:@ %a@." pp_eprop eq);
  eq


(** Hack to work around awkward semantics of [e|->fld]. *)
let all_fields = ref StringSet.empty 

let populate_fields fld =
  let rec go s fld =
    let s = component_of_string s in
    if Fld.hasfld s fld then fld 
    else Fld.set s (E.id (Id.gensym_str_ex (string_of_component s))) fld in
  StringSet.fold go !all_fields fld

(* -------------------------------------------------------------------------- *)
(** {2 Action abstraction} *)
(* -------------------------------------------------------------------------- *)

let actabs_ids = idpool_new Id.gensym_str "!a"


let unify_spred inst sp1 sp2 = match sp1, sp2 with
 | Csp_node (_,s1,e1,cel1), Csp_node (_,s2,e2,cel2) ->
    if s1 <> s2 then None else
    let inst = Fld.subset cel1 cel2 @& E.eq e1 e2 @& inst in
    if Pure.is_false inst || Pure.has_unsat_eq inst then None else
    Some inst
 | Csp_listsegi (_,SINGLE (s1,fld1),e1,e2,e3,_,_,_), Csp_listsegi (_,SINGLE (s2,fld2),f1,f2,f3,_,_,_) ->
    if s1 <> s2 then None else
    let inst = Fld.subset fld1 fld2 @& E.eq e1 f1 @& E.eq e2 f2 @& E.eq e3 f3 @& inst in
    if Pure.is_false inst || Pure.has_unsat_eq inst then None else
    Some inst
  | _ -> None

let unify_spatial inst sl1 sl2 =
  let rec do_insert y xl rev_prefix res = match xl with
    | [] ->     List.rev_append rev_prefix [y] :: res
    | x::xl' -> do_insert y xl' (x :: rev_prefix) (List.rev_append rev_prefix (y::xl) :: res) in
  let rec gen_cases xl = match xl with
    | [] -> [[]]
    | x::xl -> List.fold_left (fun res l -> do_insert x l [] res) [] (gen_cases xl) in
  let rec find_first f xl = match xl with
    | [] -> None
    | x::xl -> match f x with None -> find_first f xl | res -> res in
  let rec easy_unify inst sl1 sl2 = match sl1, sl2 with
    | [], [] -> Some inst
    | sp1::sl1, sp2::sl2 ->
			unify_spred inst sp1 sp2 >>= fun inst ->
				easy_unify inst sl1 sl2
    | _ -> None 
	in
  find_first (easy_unify inst sl1) (gen_cases sl2)


let action_newname = 
  let n = ref 0 in
  fun () -> incr n; "inferred_" ^ string_of_int !n

(** [action_subaction act1 act2 = Some inst] iff [act1] is a subaction
    of [act2].
 *)
let action_subaction prover sub_back0
    (_name1,p1,sl_ctx1,sl_pre1,sl_post1) 
    (_name2,p2,sl_ctx2,sl_pre2,sl_post2) =
  (* 1. Fail quickly on unpromising cases *)
  if List.length sl_pre1 != List.length sl_pre2 then None
  else if List.length sl_post1 != List.length sl_post2 then None
  else
    let (sub, sub_back) = 
      idpool_combine2 actabs_ids
				(List.fold spred_exfv sl_ctx1
	   			(List.fold spred_exfv sl_pre1
	      		(List.fold spred_exfv sl_post1 
		 					(Pure.exfv p1 IdSet.empty)))) 
		in
    let p1 = Pure.map sub p1 in
    let sl_ctx1 = map_spat sub sl_ctx1 in
    let sl_pre1 = map_spat sub sl_pre1 in
    let sl_post1 = map_spat sub sl_post1 in
		(*TODO!!!!!!!!!!!!!!*)
    unify_spatial Pure.ptrue sl_pre1 sl_pre2 >>= fun inst ->
    unify_spatial inst sl_post1 sl_post2 >>= fun inst ->

    let rec go n m xs = 
      if n > m || n < 0 then []
      else if n = m then [xs]
      else match xs with
				| [] -> assert false
				| x::xs ->
	    			go n (m-1) xs
	    				@ List.map (fun y->x::y) (go (n-1) (m-1) xs)
    in
    let rec find_first f xl = match xl with
      | [] -> None
      | x::xl -> match f x with None -> find_first f xl | res -> res in
    let x = find_first (unify_spatial inst sl_ctx2)
      (go (List.length sl_ctx2) (List.length sl_ctx1) sl_ctx1)
    in
    match x with
      | None ->
	  			begin try
            let cp2 = normalize_cform ((Pure.conj inst p2, sl_ctx2),PList.nil) in
						(*      let _ = pp "NONE %a@ |- %a@." pp_uform (p1, sl_ctx1) pp_cprop cp2 in *)
	    			let res = prover.find_frame_cprop []
	      			(cprop_uform (p1, sl_ctx1)) cp2 
						in
	    			let res = List.map (fun ((p,_),_) -> ((p,[]),PNil)) res in
	    			Some (map_cprop (sub_back >> sub_back0) res)
	  			with No_frame_found -> None 
	  			end
      | Some inst -> 
	  			begin try
            let cp2 = normalize_cform ((Pure.conj inst p2, spat_empty),PList.nil) in
						(*      let _ = pp "SOME %a@ |- %a@." pp_uform (p1, sl_ctx1) pp_cprop cp2 in *)
	    			let res = prover.find_frame_cprop []
	      			(cprop_uform (p1, spat_empty)) cp2 
						in
	    			let res = List.map (fun ((p,_),_) -> ((p,[]),PNil)) res in
	    			Some (map_cprop (sub_back >> sub_back0) res)
	  			with No_frame_found -> None
	  			end

(* HACK -- disable join. Gives poor performance. *)
(*
let action_subaction prover act1 act2 =
  action_subaction prover act1 act2 && 
  action_subaction prover act2 act1
*)

(** Convert action to (pl,cr,cp,cq) format *)
let action_convert cp_ctx cp cq =
  List.fold (fun ((p_ctx, sl_ctx), _) -> 
  List.fold (fun ((p_pre, sl_pre), _) -> 
  List.fold (fun ((p_post, sl_post), _) -> 
    let pl = Pure.normalize_aggr (Pure.conj p_ctx (Pure.conj p_pre p_post)) in
    List.fold (fun p res -> (action_newname(),p,sl_ctx,sl_pre,sl_post)::res) pl
  ) cq) cp) cp_ctx []

(** Convert action into (cr,cp,cq) format *)
let action_deconvert (name,p,cr,cp,cq) =
  let cr = cprop_spred cr in
  let cp = cprop_uform (p,cp) in
  let cq = cprop_spred cq in
  new_acts name cr cp cq

(** Abstract action [(pl,cr,cp,cq)] *)
let action_abstract abstraction sub_params (name,pl,cr,cp,cq) =
  let (pl,cr,cp,cq) =
    let sub = Pure.to_sub pl >> sub_params in
    (Pure.map sub_params (Pure.remove_eqs pl), 
     map_spat sub cr, map_spat sub cp, map_spat sub cq) in
  let (pl,cr,cp,cq) = 
    let exfv = List.fold spred_exfv cp (List.fold spred_exfv cq IdSet.empty) in
    let (sub_unex,sub_toex) = idpool_combine2 actabs_ids exfv in
    let (pl,cr) = match abstraction.uform_abs true [(Pure.map sub_unex pl, map_spat sub_unex cr)] with
      | [(pl,x)] -> (Pure.map sub_toex pl, map_spat sub_toex x)
      | ufl -> 
          pp_internal_error ();
          pp "+++ %a@." pp_uform (pl, cr);
          pp "=== %a@." pp_uform (Pure.map sub_unex pl, map_spat sub_unex cr);
          List.iter (pp "--- %a@." pp_uform) ufl;
          assert false 
		in
    let cr = List.filter (function Csp_listsegi (_,SINGLE _,_,Enum 0,_,_,_,_) -> false | _ -> true) cr in
    let cr = List.map 
      (function
	 			| Csp_listsegi (tag,SINGLE(snode,_),e1,e2,e3,e4,_,ds) ->
	     		Csp_listsegi (tag,SINGLE(snode,Fld.emp),e1,e2,e3,e4,Cem_PE,Dset.emp)
	 			| sp -> sp) cr 
		in
    (pl,cr,cp,cq) 
	in
  let (fvp, fvq) = 
    (List.fold spred_fv cp IdSet.empty,
     List.fold spred_fv cq IdSet.empty) in
  (* Heuristic for locking and unlocking actions -- context is empty. *)
  let cr =
    if IdSet.mem Id.tid fvp != IdSet.mem Id.tid fvq then
      spat_empty
    else cr 
  in
  (* Simplify @list predicates *)
  let (pl,cr,cp,cq) =
    let ff = (** Get all list expressions *)
      let exp_to_list e = match e with 
				| Efun(Sfn_list,el) -> el
				| e -> [e] 
			in 
      let go_fld t e res = 
				if t == Misc.list_data_tag then exp_to_list e :: res 
				else res 
			in
      let get_lval s res = match s with
				| Csp_node(_,_,_,fld) -> Fld.fold go_fld fld res
				| Csp_listsegi(_,SINGLE _,_,_,e,_,_,_) -> exp_to_list e :: res
				| _ -> res 
			in
      List.fold get_lval 
		in
    let ell = (*ff cr*) (ff cp (ff cq [])) in
    let sub = Abstraction.mk_abs_list_sub ell in
    (Pure.map sub pl,map_spat sub cr, map_spat sub cp, map_spat sub cq)
  in
  (* Simplify @set predicates *)
  let (pl,cr,cp,cq) =
    let ff = (** Get all set expressions *)
      let exp_to_list e = match e with 
				| Efun(Sfn_set,el)  -> el
				| Efun(Sfn_list,el) -> List.map (E.fun1 Sfn_set_of_list) el
				| e -> [e] 
			in 
      let go_fld t e res = 
				if t == Misc.list_data_tag then exp_to_list e :: res 
				else res 
			in
      let get_lval s res = match s with
				| Csp_node(_,_,_,fld) -> Fld.fold go_fld fld res
				| Csp_listsegi(_,SINGLE _,_,_,e,_,_,_) -> exp_to_list e :: res
				| _ -> res 
			in
      List.fold get_lval 
		in
    let ell = (*ff cr*) (ff cp (ff cq [])) in
    let sub = Abstraction.mk_abs_set_sub IdSet.empty ell in
    (Pure.map sub pl,map_spat sub cr, map_spat sub cp, map_spat sub cq)
  in
  let (fvp, fvq) = 
    (List.fold spred_fv cp IdSet.empty,
     List.fold spred_fv cq IdSet.empty) in
  let pl =
    let kills = IdSet.diff (Pure.exfv pl IdSet.empty)
				(spat_fold E.exfv cr (IdSet.union fvp fvq)) 
		in
  	let pl = Pure.kill_vars kills pl in
  	(* TODO: Figure out better heuristic... *)
  	let exfv2 = IdSet.filter Id.is_existential (IdSet.diff fvq fvp) in 
  	let myf e = 
  		let fv = E.exfv e IdSet.empty in
    	IdSet.is_empty fv
    	|| (match e with Efun1 (Sfn_NOT, Eeq(Enum 0,_)) -> true | _ -> false)
    	|| ((match e with Efun2 (Sfn_list_lt,_,_) -> true | _ -> false) 
	  		&& IdSet.exists (function x -> IdSet.mem x exfv2) fv)
  	in
  	Pure.filter myf pl 
	in
  (name,pl,cr,cp,cq)

(** Join action act to the action set recorded in [env]. *)
let action_join env actlr sub_back rid act =
  let insert_act actlr (s,_,_,_,_) inst =
    let inst = 
      List.map (fun ((p,_),_) -> ((Pure.only_inst_eqs p,[]),PNil)) inst in
    let (l, cp) = 
      try
	let cp = List.assq s !actlr in
	let l = List.remove_assq s !actlr in
	(l, cp)
      with Not_found -> (!actlr, cprop_false) in
    actlr := (s, cprop_or inst cp) :: l in
  let myf (r,act') = 
    if r == rid then
      match action_subaction env.g_prover sub_back act act' with
	| None -> true
	| Some inst -> insert_act actlr act' inst; false
    else true
  in
  let myg (r,act') = r != rid || (action_subaction env.g_prover identity act' act == None) in
  if List.for_all myf env.g_guarantee then begin
    let _ =
      if !verbose >= 3 then begin
	let (name,pl,cr,cp,cq) = act in
	pp "Added action: %s %s@.@[<hv>%a@ |  %a @ ~> %a@]@."
          (string_of_component rid) name
          pp_uform (pl, cr)
	  pp_uform (Pure.ptrue, cp)
	  pp_uform (Pure.ptrue, cq)
      end
    in
    insert_act actlr act cprop_empty;
    env.g_guarantee <- (rid,act) :: List.filter myg env.g_guarantee;
    env.g_guar_changed <- true
  end


(** Add action [cp_ctx | cp ~~> cq] to the guarantee. *)
let register_guarantee env actlr rid cp_ctx cp cq =
  if !verbose >= 6 then begin
    pp "register guarantee: %s@.@[<hv>%a@ |  %a @ ~> %a@]@."
      (string_of_component rid)
      pp_cprop cp_ctx
      pp_cprop cp
      pp_cprop cq
  end;
  (* 1. Forget local variables *)
  let (cp_ctx, cp, cq) =
    let cp_ctx = prop_kill_can_return cp_ctx in
    let cp = prop_kill_can_return cp in
    let cq = prop_kill_can_return cq in
    let fv = prop_fv cp_ctx (prop_fv cp (prop_fv cq IdSet.empty)) in
    let locals = IdSet.diff (IdSet.diff fv env.g_globals) env.g_params in
    let sub = mk_gensym_garb_subst_idset locals in
    (map_cprop sub cp_ctx, map_cprop sub cp, map_cprop sub cq) in
  (* Substitution for parameters *)
  let (sub, sub_back) = mk_gensym_garb_subst_idset2 env.g_params in
  (* 2. For each action... *)
  List.iter
     (action_abstract env.g_abstraction sub
        >> action_join env actlr sub_back rid)
     (action_convert cp_ctx cp cq)


let get_reachable froml sl =
  let add x y = if List.exists (fun y -> equal_exp x y) y then y else x::y in
  let add_reach_vars res sp = match sp with
    | Csp_node (_,_,_,fld) -> Fld.fold_val add fld res
    | Csp_listsegi(_,_,e,f,g,h,_,_) -> add e (add f (add g (add h res)))
    | Csp_arr (_,e,f,g,_,_,_) -> add e (add f (add g res))
    | Csp_indpred _ -> res  in
  let is_pred_reachable x sp = match sp with
    | Csp_arr (_,e,_,_,_,_,_) (*TODO*)
    | Csp_node (_,_,e,_) -> equal_exp x e
    | Csp_listsegi(_,SINGLE _,e,_,_,_,_,_) -> equal_exp x e
    | Csp_listsegi(_,(XOR _ | DOUBLE _),e1,_,e2,_,_,_) -> equal_exp x e1 || equal_exp x e2
    | Csp_indpred _ -> false in
  let rec go_reach seen todo sl1 sl2 = match todo with
    | [] -> (sl1, sl2)
    | x::todo -> 
			let (sl1new,sl2) = List.partition (is_pred_reachable x) sl2 in
			let seen = x::seen in
			let todo = List.fold_left add_reach_vars todo sl1new in
			let todo = List.filter (fun x -> not (List.exists (fun y -> equal_exp x y) seen)) todo in
			go_reach seen todo (sl1new @ sl1) sl2 in
  go_reach [] froml [] sl

(** Helper function *)
let reduce_list f cfl =
  let g reso cf =
    reso >>= fun res ->
    f cf >>= fun cfl -> Some (List.rev_append cfl res) in
  List.fold_left g (Some []) cfl


(* -------------------------------------------------------------------------- *)
(** {2 Symbolic execution of field lookup and update} *)
(* -------------------------------------------------------------------------- *)

(** In the context [rctx], calculate the postcondition 
    of executing [x = e->t] given the precondition [cpre]. *)
let execute_fld_lookup prover rctx x e t cpre =
  (* Old value of x is now garbage *)
  let sub = mk_gensym_garb_subst x in
  (* Read from cf *)
  let rec go_simp e rctx ((pl2,sl2),scpl2) = (* type of return is cform list option or cprop option *)
    let e = (Pure.to_sub pl2) e in
    try
      let (cel,sl2b) = prover.find_ptsto node_component e sl2 in
      let (f,cel') = Fld.get_extend t cel in
      let f' = sub f in
      let cp = map_cform sub ((pl2,Csp_node(tag_default,node_component,e,cel')::sl2b),scpl2) in
      Some (and_cprop_pure cp (Pure.one (E.eq (E.id x) f')))
    with Not_found -> 
      go_ctx e rctx ((pl2,sl2),scpl2)
  and go e rctx cf = 
    let cp = prover.expose_ptsto (cprop_cform cf) e in
    reduce_list (go_simp e rctx) cp
  and go_ctx e rctx ((pl2,sl2),scpl2) =
    match rctx with
    | [] -> None
    | rid::rctx ->
				try match reduce_list (go e []) (and_cprop_pure (PList.assq rid scpl2) pl2) with
	  			| None -> go_ctx e rctx ((pl2,sl2),scpl2)
	  			| Some cfl -> 
	      		let cp2 =  map_cform sub ((pl2,sl2), PList.remove_assq rid scpl2) in
	      		Some (List.map (fun (uf2, scpl2) -> (uf2, PCons (rid, cfl, scpl2))) cp2)
				with Not_found -> go_ctx e rctx ((pl2,sl2),scpl2) in
  let go_ext_simp e rctx n = (* type of go simple is (cform -> cform list option); type of n is eform *)
    ext_opt_transform1 (go_simp e rctx) n in
  let go_ext e rctx n =
    ext_expose_ptsto prover e [n] (* return eprop *)
    |> reduce_list (go_ext_simp e rctx) in
  reduce_list (go_ext e rctx) cpre


(** In the context [rctx], calculate the postcondition 
    of executing [e1->t1 = f1, ... en->tn = fn] given the precondition [cpre]. *)
let execute_fld_assign env actlr rctx assignl cpre =
  (* Deal with shared writes *)
  let go_shared (rid : component) ((pl_local,sl_local),scpl) ((pl_shared,sl_shared),scpl') =
    (* TODO :: Normalize cf_local * pl_shared ! *)
    try
      let (old_vals,new_vals,old_nodes,new_nodes,sl_rem_shared) = 
				let sub = Pure.to_sub pl_shared in
				List.fold_left
				  (fun (e2_olds,e2s,old_nodes,new_nodes,sl_rem_shared) (e1,t,e2) ->
				     let e1 = sub e1 in
				     let e2 = sub e2 in
				     let (cel,sl_rem_shared) = 
				       env.g_prover.find_ptsto node_component e1 sl_rem_shared in
				     let cel = populate_fields cel in
				     let (e2_olds, e2) = (* HACK -- abstraction for unlocking actions *)
				       match Fld.try_get t cel with
				       | Some e2_old ->
							   if e2 == E.zero && e2_old == E.tid then
							       (e2_old::e2_olds, E.id (Id.gensym_str_ex "unlock"))
							   else 
					     (e2_old::e2_olds, e2)
				       | None -> (e2_olds, e2) in
				     let e2s = e2::e2s in
				     let old_nodes = Csp_node(tag_default,node_component,e1,cel)::old_nodes in
				     let new_nodes = Csp_node(tag_default,node_component,e1,Fld.set t e2 cel)::new_nodes in
				     (e2_olds,e2s,old_nodes,new_nodes,sl_rem_shared))
	  					([],[],[],[],sl_shared) assignl 
			in
      (* Ownership transfer: private -> shared *)
      let (sl_transf_to_shared,sl_local) = get_reachable new_vals sl_local in
      (* Ownership transfer: shared -> private *)
      let (sl_transf_to_local,sl_rem_shared) = 
				if !allow_leaks then ([],sl_rem_shared)
				else 
	  			let sl3 = spat_star new_nodes (spat_star sl_transf_to_shared sl_rem_shared) in 
	  			let (_,transf) = get_reachable (List.map E.id (IdSet.elements env.g_globals)) sl3 in
	  			let (transf,_) = get_reachable old_vals transf in
	  			List.partition (fun sp -> List.exists (fun x -> compare_can_spred sp x = 0) transf) sl_rem_shared 
			in
      (* Results *)
      	let _ = 
					if !verbose >= 4 && sl_transf_to_local <> [] then
	  				pp "ACTION: BECOME LOCAL =@ %a@.SL2 =@ %a@."
	    			pp_uform (Pure.ptrue, sl_transf_to_local)
	    			pp_uform (Pure.ptrue, sl_rem_shared) 
				in
      	let cp_ctx = env.g_prover.nf_cprop [] (cprop_spred sl_rem_shared) in
      	let cp_pre = 
					let sl_pre = spat_star old_nodes sl_transf_to_local in
					env.g_prover.nf_cprop [] (cprop_uform (pl_shared,sl_pre)) 
				in
      	let cp_post =
					let sl_post = spat_star new_nodes sl_transf_to_shared in
					env.g_prover.nf_cprop [] (cprop_spred sl_post) 
				in
      	let sl_local' = sl_transf_to_local @ sl_local in
      	let sl_shared' = new_nodes @ (sl_transf_to_shared @ sl_rem_shared) in
      	register_guarantee env actlr rid cp_ctx cp_pre cp_post;
      	let cf_shared' = ((pl_shared,sl_shared'),scpl') in
      	Some [((pl_local,sl_local'), PCons (rid, cprop_cform cf_shared', scpl))]
    with Not_found -> None 
	in (* End of definition of go_shared *)
  let go_shared_wrapper rid cf_local (((pl_shared,_),_) as cf_shared) =
    let cp_local = env.g_prover.nf_cprop [] (cprop_cform (cf_local @% pl_shared)) in
    reduce_list (fun cf -> go_shared rid cf cf_shared) cp_local
  in
  let rec go_ctx rctx n =
    let (uf2,scpl2) = cform_of_eform n in
    match rctx with
    	| [] -> None
    	| rid::rctx ->
				try
	  			let cp_shared = and_cprop_pure (PList.assq rid scpl2) (fst uf2) in
	  			let cp_shared = List.fold
	    			(fun (e1,_,_) cp -> env.g_prover.expose_ptsto cp e1)
	    			assignl cp_shared 
					in
	  			let cp_local = (uf2, PList.remove_assq rid scpl2) in
	  			match reduce_list (go_shared_wrapper rid cp_local) cp_shared with
	  				| None -> go_ctx rctx n
	  				| Some cp -> 
	      				Some (ext_transform (fun _ -> cp) [n])
				with Not_found -> go_ctx rctx n in
  (* Local writes *)
  let go n =
    let ((pl2,sl2),scpl2) = cform_of_eform n in
    let sub = Pure.to_sub pl2 in
		
		try 
      let sl2 = List.fold_left (fun sl2 (e1,t,e2) ->
				let e1 = sub e1 in
				let (cel,sl2b) = env.g_prover.find_ptsto node_component e1 sl2 in
				let cel' = Fld.set t e2 cel in
				Csp_node(tag_default,node_component,e1,cel')::sl2b)
				sl2 assignl 
			in
      let m = new_node ((pl2,sl2),scpl2) in
      put_edge_skip n m;
      Some [m]
    with Not_found ->
      if !infer >= 1 then go_ctx rctx n else None 
	
	in
  	(* Main code *)
  	reduce_list go cpre


(* -------------------------------------------------------------------------- *)
(** {2 Symbolic Execution} *)
(* -------------------------------------------------------------------------- *)

(** Result of symbolic execution *)
type se_result = 
  { se_normal : eprop;
    se_break  : eprop;
    se_cont   : eprop;
    se_return : eprop;
		se_lp : bool;
		se_break_lp : bool;
		se_noneff_lins : (Location.t, cprop) Hashtbl.t; 
		se_eff_lins : (Location.t, 
			(Predicate.t list * cprop * fld_assignments * IdSet.t * bool)) Hashtbl.t;
		se_paths: Predicate.t list }

let se_false = 
  { se_normal = eprop_false; 
    se_break  = eprop_false;
    se_cont   = eprop_false;
    se_return = eprop_false;
		se_lp = false;
		se_break_lp = false;
		se_noneff_lins = Hashtbl.create 0; 
		se_eff_lins = Hashtbl.create 0;
		se_paths = []; }

let se_map f se = 
  { se_normal = f se.se_normal; 
    se_break  = f se.se_break;
    se_cont   = f se.se_cont;
    se_return = f se.se_return;
		se_lp = se.se_lp;
		se_break_lp = se.se_break_lp;
		se_noneff_lins = se.se_noneff_lins; 
		se_eff_lins = se.se_eff_lins;
		se_paths = se.se_paths; }

type lv_data = 
  { lv_action : cprop list ; 
    lv_break  : eprop;
    lv_cont   : eprop;
    lv_return : eprop;
		lv_lp : bool;
		lv_break_lp : bool;
		lv_noneff_lins : (Location.t, cprop) Hashtbl.t;
		lv_eff_lins : (Location.t, 
			(Predicate.t list * cprop * fld_assignments * IdSet.t * bool)) Hashtbl.t;
		lv_paths : Predicate.t list }

let ext_map f ep = ext_transform (fun cf -> f [cf]) ep

let kill_garbage prover lv ep1 =
  (if !verbose >= 4 then pp "lv=%a@." pp_idset lv); 
  ext_map
    (fun cf -> prover.nf_cprop [] cf
     |> kill_dead_vars lv
(*     |> kill_garbage_vars *)
     |> prover.nf_cprop [])
    ep1

let se_of_lvs lvs cp =
  { se_normal = cp;
    se_break  = lvs.lv_break;
    se_cont   = lvs.lv_cont;
    se_return = lvs.lv_return;
		se_lp = lvs.lv_lp;
		se_break_lp = lvs.lv_break_lp;
		se_noneff_lins = lvs.lv_noneff_lins;
		se_eff_lins = lvs.lv_eff_lins;
	  se_paths = lvs.lv_paths; }

let add_missing_boxes env rgnl cp =
  let add_inv rid ((uf,scpl) as cf) = 
    if PList.mem_assq rid scpl then cf
    else (uf, PCons (rid, Hashtbl.find env.g_renv rid, scpl)) in
  ext_transform (fun cf -> [List.fold add_inv rgnl cf]) cp
	
(** Collect candidate lineariazation points. 
 		c0 is where a return site is encountered
		cpre is the symbolic state upon return site
		lvs stores the collected linearization points
 *)	
let update_lin_info env fname c0 cpre lvs = 
	(** MCPA major update:
			Note we add guessed noneff witnesses into env for checking pure properties *)
	(* only add pure postcondition *)
	(** 0. Add pure informations *)
		let mcpa_pure_part ep = 
  		let rec go = function
    		| [] -> Pure.ptrue
    		| [n] -> fst (fst (cform_of_eform n))
    		| n::cfl -> Pure.mcpa_common (fst (fst (cform_of_eform n))) (go cfl) in
  		go ep in
		let purepart = mcpa_pure_part cpre in 
		(*let _ = pp "At line%s " (Location.lineno_to_string c0.can_st_loc ) in
		let _ = pp "mcpa common result is %a@." Pure.pp purepart in*)
		let explist = Pure.to_exp purepart in
		let purepred = Predicate.transl_pred explist in
		(** 1. Find return loc * possible noneff witnesses *)
	let newinfo = (c0.can_st_loc, (purepred, Misc.hashtbltoList lvs.lv_noneff_lins)) in
	(** 2. Add to the funtion's return set *)
	if (Hashtbl.mem env.non_eff_postconditions fname) then
		let oldlist = Hashtbl.find env.non_eff_postconditions fname in 
		let newlist = 
			if (List.mem_assoc c0.can_st_loc oldlist) then
				newinfo :: (List.remove_assoc c0.can_st_loc oldlist) 
			else newinfo :: oldlist in
		Hashtbl.replace env.non_eff_postconditions fname (newlist)
	else Hashtbl.replace env.non_eff_postconditions fname [newinfo];
	(** MCPA major update:
			Note we add guessed eff witnesses into env for checking eff properties *)	
	(** 3. Collect all the candidate effective lineariaztion points *)
	let newinfo = (c0.can_st_loc, (purepred, Misc.hashtbltoList lvs.lv_eff_lins)) in
	if (Hashtbl.mem env.cand_lin_point fname) then
		let oldlist = Hashtbl.find env.cand_lin_point fname in
		let newlist = 
			if (List.mem_assoc c0.can_st_loc oldlist) then
				newinfo :: (List.remove_assoc c0.can_st_loc oldlist)
			else newinfo :: oldlist in
		Hashtbl.replace env.cand_lin_point fname newlist
	else Hashtbl.replace env.cand_lin_point fname [newinfo]
		
(** Path sensitive analysis *)		
let extend_path e cpre paths = 
	(*let _ = Misc.pp "Analyzing path condition %a @." Exp.pp_exp e in
	let _ = Misc.pp "by the given cpre as %a @." Assertions.pp_cprop cpre in*)
	let nodes = List.map snd (List.map fst (List.map List.hd (flatten_condition cpre))) in
	let nodes = List.fold_left (fun res nodes -> 
		List.map_partial (fun n -> match n with
		  | Csp_node (_, _, e, _) ->
				if (List.exists (fun node -> match node with
					| Csp_node (_, _, e', _) -> (Exp.compare_exp e e' = 0)
					| _ -> false) nodes ) then Some n
				else None
			| _ -> None	
			) res
		) (List.hd nodes) (List.tl nodes) in
	
	let pe = Predicate.transl_pred e in
	(*let _ = Misc.pp "pe as %a @." Predicate.pprint pe in*)
	match pe with
		| Predicate.Not (Predicate.Atom _)
		| Predicate.Atom _ -> (
			let (pe, flag) = List.fold_left (fun (pe, flag) node -> match node with
				| Csp_node (_, _, enode, fld) -> Fld.fold (fun com exp (pe, flag) ->
					if (com = Misc.list_data_tag || com = Misc.list_link_tag) then (pe, flag)
					else match exp with
						| Exp.Eident _ -> 
							let vid = (Exp.Id.of_exp exp) in
							let vars = Predicate.vars pe in
							if (List.exists (fun var -> Id.compare var vid = 0) vars) then
								(Predicate.subst 
								(Predicate.FunApp (string_of_field_component com, [Predicate.Var (Exp.Id.of_exp enode)])) 
								vid pe, true) 
							else (pe, flag)
						| _ -> (pe, flag)
					) fld (pe, flag) 
				| _ -> (pe, flag)
				) (pe, false) nodes
			in 
				if (flag) then ((*Misc.pp "Extend path %a @." Predicate.pprint pe;*)
					pe :: paths	)
				else paths
			)
		| _ -> paths
	
(** The main symbolic execution function *)
let rec symb_execute (env : global_env) (c : can_cmd) (lvs : lv_data) 
												(do_norm : bool) (cpre : eprop) qs fname : se_result =
  (* Output current symbolic execution state *)
  let _ =
    if !verbose >= 4 then
      let pp_comp s f ep = 
        if ep=[] then () else Format.fprintf f "  %s: %a@." s pp_eprop ep 
			in
      match c with
			| {can_st_loc = loc1}::_ ->
	    	print loc1 "Intermediate State:@.%a%a%a[@[%a@]]@.%a@."
              (pp_comp "return") lvs.lv_return (pp_comp "break") lvs.lv_break
              (pp_comp "continue") lvs.lv_cont pp_eprop cpre pp_cmd c
			| _ -> () 
	in
  (* If the precondition is satisfiable, proceed with symbolic execution *)
  match cpre with 
	| [] -> se_of_lvs lvs eprop_false 
	| _ -> 
  	match c with 
		| [] -> se_of_lvs lvs cpre 
		| c0 :: c1 ->
  	match c0.can_st_desc with 
    | Cst_nondet (c2,c3) ->
			(** MCPA major update:
			 *  We allow past paths to affect the linearization choice *)
			let _ = if (env.g_no_interf_hack) then (
				(*let _ = Misc.pp "c0 loc as %s c2 loc as %s c3 loc as %s\n" 
				(Location.lineno_to_string c0.can_st_loc)
				(Location.lineno_to_string (List.hd c2).can_st_loc)
				(Location.lineno_to_string (List.hd c2).can_st_loc) in
				let _ = Misc.pp "put\n" in*) (
				Hashtbl.replace env.seq_table c0.can_st_loc (List.map cform_of_eform cpre);
				Hashtbl.replace env.seq_table (List.hd c2).can_st_loc (List.map cform_of_eform cpre);
				Hashtbl.replace env.seq_table (List.hd c3).can_st_loc (List.map cform_of_eform cpre))
			) in
			let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in
			let (cp2,cp3) = ext_append_case_split cpre in
			let (nonefftb2, nonefftb3) = (Hashtbl.create 3, Hashtbl.create 3) in
			let (efftb2, efftb3) = (Hashtbl.create 3, Hashtbl.create 3) in
			let nonefftb2 = Misc.mergeHashtbl nonefftb2 lvs.lv_noneff_lins in
			let nonefftb3 = Misc.mergeHashtbl nonefftb3 lvs.lv_noneff_lins in
			let efftb2 = Misc.mergeHashtbl efftb2 lvs.lv_eff_lins in
			let efftb3 = Misc.mergeHashtbl efftb3 lvs.lv_eff_lins in
			(** Make copies of current path *)
			let paths2 = List.copy lvs.lv_paths in
			let paths3 = List.copy lvs.lv_paths in
			let sq2 = symb_execute env c2 
				{lvs with lv_noneff_lins = nonefftb2; 
				lv_eff_lins = efftb2;
				lv_paths = paths2 } false cp2 qs fname in
			let sq3 = symb_execute env c3 
				{lvs with lv_noneff_lins = nonefftb3; 
				lv_eff_lins = efftb3;
				lv_paths = paths3 } false cp3 qs fname in
			(** No reason to keep the following two since its branch has its copy *)
			let _ = Hashtbl.clear lvs.lv_noneff_lins in
			let _ =	Hashtbl.clear lvs.lv_eff_lins in
			let lvs = 
	  		{ lvs with 
	      	lv_break  = eprop_or sq2.se_break  sq3.se_break;
	      	lv_cont   = eprop_or sq2.se_cont   sq3.se_cont;
	      	lv_return = eprop_or sq2.se_return sq3.se_return;
					lv_lp = sq2.se_lp && sq3.se_lp; 
					lv_break_lp = sq2.se_break_lp && sq3.se_break_lp;
					lv_noneff_lins = Misc.mergeHashtbl 
						(Misc.mergeHashtbl lvs.lv_noneff_lins sq2.se_noneff_lins)
						sq3.se_noneff_lins;
					lv_eff_lins = Misc.mergeHashtbl
						(Misc.mergeHashtbl lvs.lv_eff_lins sq2.se_eff_lins)
						sq3.se_eff_lins } in (** It still uses its old paths (local paths are forgotten) *)
			let cq = eprop_or sq2.se_normal sq3.se_normal in
			symb_execute env c1 lvs true cq qs fname
    | Cst_kill ids ->
			(*TODO let cpre = ext_append_assign (IdSet.fold (fun i r -> (i,None)::r) ids []) cpre in *)
			let cq = naive_map_eprop (mk_gensym_garb_subst_idset ids) cpre in
			symb_execute env c1 lvs true cq qs fname
    | Cst_assign (x,e) ->
			(* let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in *)
			let cp = ext_append_assign [(x,Some e)] cpre in
			let sub = mk_gensym_garb_subst x in
			let cq = E.eq (E.id x) (sub e) @@& (map_eprop sub cp) in
			symb_execute env c1 lvs true cq qs fname
    | Cst_fldlookup (rgnl,x,e,t) ->
				(*let _ = pp "@.fldlookup pre:@.%a@." pp_eprop cpre in*)
				let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in
        let cpre = add_missing_boxes env rgnl cpre in
				(*let _ = pp "@.fldlookup pre step later:@.%a@." pp_eprop cpre in*)
				let cp = ext_append_assign [(x,None)] cpre in
				(*let _ = pp "@.fldlookup pre step 2later:@.%a@." pp_eprop cp in*)
				let cq = match execute_fld_lookup env.g_prover rgnl x e t cp with
	  			| Some cq -> cq
	  			| None -> error_heap c0.can_st_loc e cpre in
				(** MCPA major update
						remember possible noneff spec witnesses 
						Only add to noneff_lins if the next statment is Cst_stabilize(rid)
						*)
				let _ = match c1 with [] -> () | cn ::_ -> 
					(Hashtbl.replace lvs.lv_noneff_lins c0.can_st_loc (List.map cform_of_eform cq);
					if (env.g_no_interf_hack) then
						Hashtbl.replace env.seq_table c0.can_st_loc (List.map cform_of_eform cq)
					)
					(*(match cn.can_st_desc with
					| Cst_stabilize _ -> Hashtbl.replace lvs.lv_noneff_lins c0.can_st_loc (List.map cform_of_eform cq) 
					| _ -> ())*) in
				symb_execute env c1 lvs true cq qs fname
    | Cst_fldassign (rgnl,l,actlr) ->
				(** MCPA major update:
						Remembering effectful linearization point *)
				let remembered_cpre = List.map cform_of_eform cpre in
				let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in
        let cpre = add_missing_boxes env rgnl cpre in
				let cp = List.fold (fun (e,_,_) cp -> ext_expose_ptsto env.g_prover e cp) l cpre in
				let cq = match execute_fld_assign env actlr rgnl l cp with
	  			| Some cq -> cq
	  			| None -> error_heap2 c0.can_st_loc "memory write" cpre in
				(*let lvs = match !actlr with 
					| [] -> lvs
					| _ -> (Hashtbl.clear lvs.lv_noneff_lins; {lvs with lv_lp = true}) in*)
				let _ = match !actlr with
					| [] -> ()(** May be only a local update update *)
					| _ ->  (** In this case, remember assignmen instruction and precondition *)
						((*pp "@.set pre cp as @.%a@." pp_cprop remembered_cpre;*)
						Hashtbl.replace lvs.lv_eff_lins c0.can_st_loc 
							(List.copy lvs.lv_paths, remembered_cpre, l, c0.can_st_lv, lvs.lv_lp);
						if (env.g_no_interf_hack) then (** Sequential version state *)
							Hashtbl.replace env.seq_table c0.can_st_loc remembered_cpre
						(*if (Hashtbl.mem env.cand_lin_point fname) then
							let lps = Hashtbl.find env.cand_lin_point fname in
							let lps = 
								if (List.mem_assoc c0.can_st_loc lps) then
									let lps = List.remove_assoc c0.can_st_loc lps
									in lps @ [(c0.can_st_loc, (List.map cform_of_eform cpre, l, lvs.lv_lp))]
								else lps @ [(c0.can_st_loc, (List.map cform_of_eform cpre, l, lvs.lv_lp))] in
							Hashtbl.replace env.cand_lin_point fname lps
						else
							Hashtbl.replace env.cand_lin_point fname 
								[(c0.can_st_loc, (List.map cform_of_eform cpre, l, lvs.lv_lp))] *)
						) in
				symb_execute env c1 lvs true cq qs fname
    | Cst_new (x,size) ->
			(* assert (size == E.one);*) (* TODO !!!!!!!!! *)
			(* let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in *)
			let cp = ext_append_assign [(x,None)] cpre in
			let cq = 
	  		let sub = mk_gensym_garb_subst x in
	  		let cp = map_eprop sub cp in
        let cq0 = cprop_uform
              (mk_array tag_default (E.id x) (E.add (E.id x) size) 
                        (E.id (Id.gensym_str_ex "VAL")) Fld.emp Dset.emp uform_empty) 
				in
	  			(*let cq0 = cprop_spred [Csp_node(tag_default,node_component,E.id x,Fld.emp)] in*)
	  			cq0 @@*** cp 
			in symb_execute env c1 lvs true cq qs fname
    | Cst_dispose (e,size) ->
			assert (size == E.one); (* TODO !!!!!!!!! *)
			let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in
			let cp1 = cprop_spred [Csp_node(tag_default,node_component,e,Fld.emp)] in
			let cq = execute_gen_cmd env.g_prover (IdSet.empty,cp1,cprop_empty,"dispose",c0.can_st_loc) cpre in
			symb_execute env c1 lvs false cq qs fname (* Already normalized *)
    | Cst_pfcall par_calls -> (* type of par_calls is (Id.t option * string * Id.t list * exp list) list *)
			let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in
	  	(* TODO -- freshen exist. vars *)
	  	let cp =
	    	List.fold
		      (fun (_,s,_,_) cp ->
			 			if str_is_cutpoint s then
			   			ext_append_comment 
			     		(fun () ->
							let n = next_cutpoint() in
							"goto " ^ n ^ "; " ^ n ^ ": 0;") cp
			 			else if str_is_fair s then 
			   			ext_append_comment (fun () -> s ^ " = 1;") cp
			 			else cp) par_calls cpre 
			in
	  	(* 1. Calculate the specification of a generic command *)
      let go_fun (resido,s,idl,el) =
	    let fi = Hashtbl.find env.g_fun_ht s in
	    let (vl,idl) = match resido with
	      | None -> (fst fi.fun_param, idl)
	      | Some resid -> (Id.create "Result" :: fst fi.fun_param, resid :: idl) in
	    let sub = 
	      let sl_ref = PList.combine vl (List.map E.id idl) in
	      let sl_val = PList.combine (snd fi.fun_param) el in
	      mk_subst (PList.rev_append sl_ref sl_val) in
	    let modif = List.fold IdSet.add idl (map_idset sub fi.fun_modif) in
	    let (sub_ex, sub_ex_post) = 
	      let exfv_pre = prop_exfv fi.fun_pre IdSet.empty in
	      let exfv_post = IdSet.diff (prop_exfv fi.fun_post IdSet.empty) exfv_pre in
	      (mk_gensym_garb_subst_idset exfv_pre,
	       existentials_rename_sub exfv_post) in
            let post = map_cprop (fun e -> sub_ex_post (sub_ex (sub e))) fi.fun_post in
	    let pre = map_cprop (fun e -> sub_ex (sub e)) fi.fun_pre in
	    (modif,pre,post) in
	  	let go (m,p,q) x =
	    	let (m',p',q') = go_fun x in
	    	(IdSet.union m' m, cprop_star p' p, cprop_star q' q) 
			in
      let (modif,cp1,cp2) = List.fold_left go (IdSet.empty,cprop_empty,cprop_empty) par_calls in
	  	(* 2. Apply the generic command *)
	  	let cq = execute_gen_cmd env.g_prover (modif,cp1,cp2,"Function call",c0.can_st_loc) cp in 
	  	symb_execute env c1 lvs true cq qs fname
    | Cst_fcall2 (modif,cp1,cp2,s') ->
			let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in
			let cq = execute_gen_cmd env.g_prover (modif,cp1,cp2,s',c0.can_st_loc) cpre in 
			symb_execute env c1 lvs true cq qs fname
    | Cst_assume cp ->
			let cq = cp @@*** cpre in
			let cq = ext_transform normalize_cform_aggr cq in
			symb_execute env c1 lvs true cq qs fname
    | Cst_assume_exp e ->
			let lvs = 
	  		{ lvs with lv_paths = 
					if (env.g_no_interf_hack) then lvs.lv_paths
					else 
						try 
						let rem_cpre = Hashtbl.find env.seq_table c0.can_st_loc in
						extend_path e rem_cpre lvs.lv_paths with _ -> ((*Misc.pp "Not found loc\n";*) lvs.lv_paths)} in
			let cq = cprop_pure (Pure.one e) @@*** cpre in
			let cq = ext_transform normalize_cform_aggr cq in
			symb_execute env c1 lvs true cq qs fname
    | Cst_assert_exp e ->
    	let _ = if not (env.g_prover.adv_entails_atom (List.map cform_of_eform cpre) e) then
          error_noframe_ext c0.can_st_loc "assert" cpre (cprop_pure (Pure.one e)) 
			in symb_execute env c1 lvs true cpre qs fname
    | Cst_action_begin (rid,cp_ctx,cp0,cq0,modif_body) ->
			let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in
	  	let (cp,cp_ctx,cp0,lvs') =
	    	(* 1. Freshen existential variables *)
	    	let (cp_ctx,cp0,cq0) =
	      	let (@+) = prop_exfv in
	      	let exfv = (cp0 @+ cq0 @+ cp_ctx @+ IdSet.empty) in
	      	let sub = mk_gensym_garb_subst_idset exfv in
	      	(map_cprop sub cp_ctx, map_cprop sub cp0, map_cprop sub cq0) 
				in
	    	(* 2. Rename vars modified by region body and appear in action post *)
	    	let (cp,cq0) =
	      	let sub_modif_pairs = 
						let modif_vars = IdSet.inter modif_body (fv_norm_cprop cq0) 
						in
							IdSet.fold (fun id r -> PCons(id, E.id (Id.gensym_norm id), r)) modif_vars PNil 
					in
	      		let cq0 = map_cprop (mk_subst sub_modif_pairs) cq0 in
	      		let pl' = PList.fold (fun id e res-> E.eq (E.id id) e @& res) 
							sub_modif_pairs Pure.ptrue 
						in
	      		let cp = pl' @@&& cpre in
	      		(cp,cq0) 
				in
	    	let lvs' = { lvs with lv_action = cq0 :: lvs.lv_action } in
	    	(cp,cp_ctx,cp0,lvs') 
			in
	  	(* Consider each disjunct separately *)
	  	let cq = ext_transform (fun cf ->
	      (* 1. Calculate the frame [fr] that is not accessed by the block *)
	      let fr = 
					let cp_shared = 
						try PList.assq rid (snd cf) 
            with Not_found -> pp_internal_error (); assert false 
					in
					let cp1 = and_cprop_pure cp_shared (fst(fst cf)) 
					in           
						try env.g_prover.find_frame_cprop (snd(fst cf)) cp1 cp0
						with No_frame_found -> 
		  				error_noframe c0.can_st_loc "action entry" cp1 cp0 
				in
	      (* 2. Check that the frame [fr] contains the context: [fr |- cp_ctx * true] *)
        let _ = 
					try 
		  			let (sub1,sub2) = existentials_rename_tonormal_sub (prop_exfv fr IdSet.empty) in
		  			let fr = map_cprop sub1 fr in
		  			let cp_ctx = map_cprop sub1 cp_ctx in
		  			env.g_prover.find_frame_cprop (snd(fst cf)) fr cp_ctx
						with No_frame_found ->
		  				error_noframe c0.can_st_loc "action entry context" fr cp_ctx 
				in
	      (* 3. Calculate the precondition inside the block *)
	      let cfl = 
					let uf = fst cf in
					let scpl' = PList.remove_assq rid (snd cf) in
					List.map (fun cfs -> (uf, PCons(rid, cprop_cform cfs, scpl'))) fr
	      in
	      	cprop_star cfl cp0) cp 
			in symb_execute env c1 lvs' true cq qs fname
    | Cst_action_end (rid,_) ->
			let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in
			(* 1. Pop the action's postcondition from the stack *)
			let (cq0, lvs) =
	  		(List.hd (lvs.lv_action), {lvs with lv_action = List.tl (lvs.lv_action)}) in
			(* 2. Calculate the postcondition outside the "do" block *)
			let modif_body = IdSet.empty (* TODO! *) in 
			let cq = exit_from_block env.g_prover (rid,modif_body,cq0,c0.can_st_loc) cpre 
			in
				symb_execute env c1 lvs true cq qs fname
    | Cst_interfere (rid,actid) ->
			let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in
			let get_shared rid (uf,scpl) = 
				try ((uf, PList.remove_assq rid scpl), PList.assq rid scpl)
				with Not_found -> pp_internal_error (); assert false 
			in
			let act = 
	  		try List.find (fun a -> act_name a = actid) (Hashtbl.find env.g_res_ht rid)
	  		with Not_found -> pp_internal_error (); assert false in
			let cq = ext_transform
	  		(fun cf ->
	     	let ((uf,scpl),cp_shared) = get_shared rid cf in
	     	let cp_shared = interfere_once env.g_prover act cp_shared in
	     	cprop_cform (uf, PCons (rid, cp_shared, scpl)))
	  		cpre 
			in
				symb_execute env c1 lvs true cq qs fname
    | Cst_stabilize(rid) ->
			if env.g_no_interf_hack then symb_execute env c1 lvs do_norm cpre qs fname
			else
	  		let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in
	  		let rely = Hashtbl.find env.g_res_ht rid in
				(*let _ = pp "@.stabilizing with the number of rely as @.%d@." (List.length rely) in *)
	  		let cq = stabilize env (rid,rely) cpre in
	  		Gc.minor ();
	  		let _ = (* Debugging... *)
	    		let inv = [(uform_empty, PCons (rid, Hashtbl.find env.g_renv rid, PNil))] 
					in
	    			if 
	      			(try let _ = env.g_prover.find_frame_cprop [] (List.map cform_of_eform cpre) inv in true
	       			with No_frame_found -> false) 
	      			&& not (try let _ = env.g_prover.find_frame_cprop [] (List.map cform_of_eform cq) inv in true
		      		with No_frame_found -> false)
	    			then 
							begin
	      				pp "@.WARNING: Loss of precision:@.BEFORE = %a@.AFTER = %a@."
								pp_eprop cpre pp_eprop cq;
	    				end 
				in
	  			symb_execute env c1 lvs true cq qs fname
    | Cst_loop(c2,None) ->
			let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in
			(* Cell to store the exit conditions *)
			let res_break = ref eprop_false in
			let res_return = ref eprop_false in
			let res_break_lp = ref true in
			let res_noneff = Hashtbl.create 0 in
			let res_eff = Hashtbl.create 0 in
			let lvs' = 
          { lv_action = lvs.lv_action;
	    			lv_break = eprop_false; lv_cont = eprop_false;
            lv_return = eprop_false;
						lv_lp = lvs.lv_lp;
						lv_break_lp = lvs.lv_break_lp;
						lv_noneff_lins = lvs.lv_noneff_lins; 
						lv_eff_lins = lvs.lv_eff_lins;
						lv_paths = lvs.lv_paths } 
			in
			let transf cp =
	  		let (cp,_) = ext_append_case_split cp in
        let se = symb_execute env c2 {
					lvs' with lv_noneff_lins = Hashtbl.copy lvs.lv_noneff_lins;
					lv_eff_lins = Hashtbl.copy lvs.lv_eff_lins;
					lv_paths = List.copy lvs.lv_paths } false cp qs fname in
	  		res_break  := eprop_or se.se_break  !res_break;
	  		res_return := eprop_or se.se_return !res_return;
				res_break_lp := se.se_break_lp && (!res_break_lp);
				Hashtbl.clear res_noneff; ignore (Misc.mergeHashtbl res_noneff se.se_noneff_lins);
				Hashtbl.clear res_eff; ignore (Misc.mergeHashtbl res_eff se.se_eff_lins);
	  		kill_garbage env.g_prover c0.can_st_lv (eprop_or se.se_normal se.se_cont)
			in
			(** MCPA major update:
					This procedure does qualifier elimination for shape analysis *)
			(*let compute_heap_inv cp = 
				let _ = pp "@.Start loop with precondition:@.%a@." pp_eprop cp in
				(* We first instantiate all qualifiers *)
				let (cp,_) = ext_append_case_split cp in
				(* We care all se.break, se.return, se.normal, se.cont *)
        let se = symb_execute env c2 lvs' false cp qs fname in
				let se_break = (*env.g_abstraction.prop_abs*) kill_garbage env.g_prover c0.can_st_lv se.se_break in
				let _ = pp "@.se_break as:@.%a@." pp_eprop se_break in
				(*let (_,se_return,_) = env.g_abstraction.prop_join eprop_false eprop_false se.return in*)
				let se_resume = kill_garbage env.g_prover c0.can_st_lv (eprop_or se.se_normal se.se_cont) in
				let _ = pp "@.se_resume:@.%a@." pp_eprop se_resume in
				(*let se_break  = kill_garbage env.g_prover c0.can_st_lv se.se_break in
				let _ = pp "@.se_break as:@.%a@." pp_eprop se.se_break in
				let _ = pp "@.se_break' as:@.%a@." pp_eprop se_break in*)
				let se_return = (*kill_garbage env.g_prover c0.can_st_lv*) kill_garbage env.g_prover c0.can_st_lv se.se_return in
				let _ = pp "@.se_return:@.%a@." pp_eprop se_return in
	  		(*let se_break  = Qualifier.eliminate env.g_prover qs se_break in
				let _ = pp "@.user abstracted se_break as:@.%a@." pp_eprop se_break in
				let se_return = Qualifier.eliminate env.g_prover qs se_return in
				let _ = pp "@.user abstracted se_return as:@.%a@." pp_eprop se_return in
				let se_resume = Qualifier.eliminate env.g_prover qs se_resume in
				let _ = pp "@.user abstracted se_resume as:@.%a@." pp_eprop se_resume in (
				res_break  := eprop_or se_break  !res_break;
	  		res_return := eprop_or se_return !res_return;
				se_resume)*)
				eprop_or se_break (eprop_or se_return se_resume)
				(*let se_final = eprop_or se_break (eprop_or se_return se_resume) in
				se_final*)
				(*ext_transform (fun cf -> env.g_prover.nf_cform [] cf) se_final*)
			in*)
			let pre =
	  	(** First calculate a fixpoint assuming no interference occurs with user provied shape qualifiers *)
	  		if not env.g_no_interf_hack then 
					begin
	    			env.g_no_interf_hack <- true;
						(** MCPA major update:
								Use shape user given shape qualifiers for inferring loop invariant *)
	    			let fix = 
							if (!qs_given) then 
								(*let lv_vars = (List.hd c2).can_st_lv in
								(* Loop invaraint will use qualifiers tailored to context *)
								let qs = Qualifier.instantiate qs lv_vars in
								(* Look ahead to collect the resource the loop will access *)
								let rs = Commands.cmd_lookup_rgnl c2 in
								compute_transf_qs_fixpoint env compute_heap_inv cpre rs qs*)
								(** Shape qualifiers are no longer used for inferring loop inv *)
								compute_transf_fixpoint env transf cpre
							else compute_transf_fixpoint env transf cpre
						in 
	    				env.g_no_interf_hack <- false;
	    				fix
	  			end 
				else cpre 
			in
	  	(* 1. Compute fixpoint *)
			(*let _ = pp "@.pre:@.%a@." pp_eprop pre in*)
	  	let _ = compute_transf_fixpoint env transf pre in
			(*let _ = pp "@.res_break:@.%a@." pp_eprop !res_break in
			let _ = pp "@.res_return:@.%a@." pp_eprop !res_return in*)
	  	let (_,cq,_) = env.g_abstraction.prop_join eprop_false eprop_false !res_break in
			(*let _ = pp "@.LOOP cq:@.%a@." pp_eprop cq in*)
	  	let lvs = { lvs with lv_return = eprop_or !res_return lvs.lv_return; 
			lv_lp = !res_break_lp; 
			lv_noneff_lins = res_noneff; 
			lv_eff_lins = res_eff} in (** After a loop, local paths are not useful at all! *)
	  	(* 2. Return the result *)
			(*let _ = Misc.pp "%s's loop lv_lp is %b@." fname lvs.lv_lp in*)
	  	symb_execute env c1 lvs true cq qs fname
    | Cst_loop(c2,Some inv) ->
			let cpre = if do_norm then kill_garbage env.g_prover c0.can_st_lv cpre else cpre in
	  	let inv0 = eprop_of_cprop inv in
	  	(* 1. Check precondition entails loop invariant *)
	  	let fr = 
	    	try ext_ext_subtract env.g_prover cpre inv0
	    	with No_frame_found -> error_noframe_ext c0.can_st_loc "loop entry" cpre inv in
	  	(* 2. Execute the body of the loop *)
	  	let lvs' = 
            { lv_action = lvs.lv_action;
	       		lv_break = eprop_false; lv_cont = eprop_false; lv_return = eprop_false;
						lv_lp = lvs.lv_lp;
						lv_break_lp = lvs.lv_break_lp;
						lv_noneff_lins = lvs.lv_noneff_lins;
						lv_eff_lins = lvs.lv_eff_lins;
						lv_paths = lvs.lv_paths } in
	  	let se = symb_execute env c2 lvs' true inv0 qs fname in
	  	(* 3. Check postcondition of the loop body entails loop invariant *)
	  	let () = 
	    	let cq = eprop_or se.se_cont se.se_normal in
	    	let fr' =
	      	try ext_ext_subtract env.g_prover cq inv0
	      	with No_frame_found -> error_noframe_ext c0.can_st_loc "loop exit" cq inv 
				in
	    		test_leakmem c0.can_st_loc fr' in
	  	(* 4. Calculate the postcondition of the loop *)
	  	let cq = fr @@*** se.se_break in
	  	let lvs = { lvs with lv_return = eprop_or (fr @@*** se.se_return) lvs.lv_return;
			lv_lp = se.se_break_lp } in
			(*let _ = Misc.pp "%s's loop lv_lp is %b@." fname lvs.lv_lp in*)
	  	symb_execute env c1 lvs true cq qs fname
    | Cst_goto (Cgo_break) ->
			{ se_normal = eprop_false; 
	  		se_break  = eprop_or cpre lvs.lv_break ; 
	  		se_cont   = lvs.lv_cont ;
	  		se_return = lvs.lv_return;
				se_lp = true;
				se_break_lp = lvs.lv_lp;
				se_noneff_lins= lvs.lv_noneff_lins; 
				se_eff_lins = lvs.lv_eff_lins;
				se_paths = []; } (** very safe! current path is interupted anyway! *)
    | Cst_goto (Cgo_continue) ->
			{ se_normal = eprop_false; 
	  		se_break  = lvs.lv_break ; 
	  		se_cont   = eprop_or cpre lvs.lv_cont ;
	  		se_return = lvs.lv_return;
				se_lp = true;
				se_break_lp = lvs.lv_break_lp;
				se_noneff_lins = lvs.lv_noneff_lins;
				se_eff_lins = lvs.lv_eff_lins;
				se_paths = []; } (** very safe! current paht is interupted anyway! *)
    | Cst_goto (Cgo_return) ->
			(** MCPA major update:
					Note we add guessed noneff witnesses into env for checking pure properties *)
			if (!mcpa_infer >= 1) then update_lin_info env fname c0 cpre lvs;
			(*let _ = (*if (lvs.lv_lp) then () else*) if (!mcpa_infer >= 1) then 
				(* only add pure postcondition *)
				(** 0. Add pure informations *)
				let mcpa_pure_part ep = 
		  		let rec go = function
		    		| [] -> Pure.ptrue
		    		| [n] -> fst (fst (cform_of_eform n))
		    		| n::cfl -> Pure.common (fst (fst (cform_of_eform n))) (go cfl) in
		  		go ep in
				let purepart = mcpa_pure_part cpre in 
				let explist = Pure.to_exp purepart in
				let purepred = Predicate.transl_pred explist in
				(** 1. Find return loc * possible noneff witnesses *)
				let newinfo = (c0.can_st_loc, (purepred, Misc.hashtbltoList lvs.lv_noneff_lins)) in
				(** 2. Add to the funtion's return set *)
				if (Hashtbl.mem env.non_eff_postconditions fname) then
					let oldlist = Hashtbl.find env.non_eff_postconditions fname in 
					let newlist = 
						if (List.mem_assoc c0.can_st_loc oldlist) then
							newinfo :: (List.remove_assoc c0.can_st_loc oldlist) 
						else newinfo :: oldlist in
					Hashtbl.replace env.non_eff_postconditions fname (newlist)
				else Hashtbl.replace env.non_eff_postconditions fname [newinfo] in
			(** MCPA major update:
					Note we add guessed eff witnesses into env for checking eff properties *)	
			(** 3. Collect all the candidate effective lineariaztion points *)		
			let _ = if (!mcpa_infer >= 1) then
				let newinfo = (c0.can_st_loc, Misc.hashtbltoList lvs.lv_eff_lins) in
				if (Hashtbl.mem env.cand_lin_point fname) then
					let oldlist = Hashtbl.find env.cand_lin_point fname in
					let newlist = 
						if (List.mem_assoc c0.can_st_loc oldlist) then
							newinfo :: (List.remove_assoc c0.can_st_loc oldlist)
						else newinfo :: oldlist in
					Hashtbl.replace env.cand_lin_point fname newlist
				else Hashtbl.replace env.cand_lin_point fname [newinfo] in*)
			(** 4. Clear. So different return points wont interfere with each other *)
			let _ = Hashtbl.clear lvs.lv_noneff_lins in
			let _ = Hashtbl.clear lvs.lv_eff_lins in
				(*let newpost = List.map cform_of_eform cpre in
				if (Hashtbl.mem env.non_eff_postconditions fname) then
					let oldpost = Hashtbl.find env.non_eff_postconditions fname in
					Hashtbl.replace env.non_eff_postconditions 
						fname (cprop_or newpost oldpost) 
				else Hashtbl.replace env.non_eff_postconditions fname newpost in*)
			{ se_normal = eprop_false; 
	  		se_break  = lvs.lv_break ; 
	  		se_cont   = lvs.lv_cont ;
	  		se_return = eprop_or cpre lvs.lv_return;
				se_lp = true;
				se_break_lp = lvs.lv_break_lp;
				se_noneff_lins = lvs.lv_noneff_lins;
				se_eff_lins = lvs.lv_eff_lins;
				se_paths = []; } (** very safe! current path is interupted anyway! *)
    | Cst_comment s ->
			let cq = ext_append_comment (fun () -> s) cpre in
			symb_execute env c1 lvs do_norm cq qs fname

let calculate_post (env : global_env) cp1 c fv_post qs fname =
  let lvs =
      { lv_action = [];
        lv_break = eprop_false;
        lv_cont = eprop_false;
        lv_return = eprop_false;
				lv_lp = false;
				lv_break_lp = true; 
				lv_noneff_lins = Hashtbl.create 5;
				lv_eff_lins = Hashtbl.create 5;
				lv_paths = [] } in
	let se = symb_execute env c lvs true cp1 qs fname
	in
  	assert (se.se_break = eprop_false); (* allowed only in a loop *)
  	assert (se.se_cont = eprop_false);  (* allowed only in a loop *)
		(** MCPA major update
				remember possible noneff and eff witnesses *)
		(*let post = eprop_or se.se_return se.se_normal in
		(if ((String.compare fname "resource") != 0) then
		let c0 = List.hd (List.rev c) in
		(match c0.can_st_desc with 
			| Cst_goto (Cgo_return) -> ()
			| _ ->
				let cpre = post in
				let lvs = {lvs with lv_noneff_lins = se.se_noneff_lins; 
				lv_eff_lins = se.se_eff_lins} in
				if (!mcpa_infer >= 1) then update_lin_info env fname c0 cpre lvs));*)
			
		(*let _ = if (se.se_lp) then () else 
			let newlist = Misc.hashtbltoList lvs.lv_noneff_lins in
				if (Hashtbl.mem env.non_eff_postconditions fname) then
					let oldlist = Hashtbl.find env.non_eff_postcondition fname in 
					Hashtbl.replace env.non_efff_postconditions fname (oldlist @ newlist)
				else Hashtbl.replace env.non_eff_postconditions fname newlist in*)
			(*let newpost = List.map cform_of_eform se.se_normal in
			if (Hashtbl.mem env.non_eff_postconditions fname) then
				let oldpost = Hashtbl.find env.non_eff_postconditions fname in
				Hashtbl.replace env.non_eff_postconditions 
					fname (cprop_or newpost oldpost) 
			else Hashtbl.replace env.non_eff_postconditions fname newpost in *)
		let post = eprop_or se.se_return se.se_normal in
		(*let post' = List.map cform_of_eform post in*)
  	let post = kill_garbage env.g_prover fv_post post in
		((*Hashtbl.replace env.non_eff_postconditions fname post';*) post)
		

let eliminate_inplace env rtb symb_eprop = 
	let cp = List.map (Genarith.cform_of_eform) symb_eprop in
	let rtbcopy = Hashtbl.copy rtb in
	Hashtbl.iter (fun rid cand_cforms -> 
		let cand_cforms = List.filter (fun ccf -> 
			try 
				let _ = pp "@.ccf as @.%a@." pp_cform ccf in
				let ccp = cprop_cform ccf in
				let rely = Hashtbl.find env.g_res_ht rid in
				let ccp = make_stable env ccp rely in
				let gccp = cprop_cform (uform_empty, PCons (rid, ccp, PNil)) in
				((*ignore*) 
				let result = (Qualifier.subtract1 env.g_prover cp gccp) in 
				(if (not result) then pp "@.remove ccf @.%a@." pp_cform ccf; 
			 	result) (*; true*)) 
			with _ -> (pp "@.remove ccf @.%a@." pp_cform ccf; 
			(*pp "@.symb_eprop as @.%a@." Genarith.pp_eprop symb_eprop;*) false)
		) cand_cforms in
		Hashtbl.replace rtb rid cand_cforms
	) rtbcopy
		
let check_resource env qs (rid,what) =
  linear_pure_code := [];
  pp_comment ("Resource " ^ string_of_component rid);
  let rely = Hashtbl.find env.g_res_ht rid in
  try match what with
    | Cri_inv (inv,loc) ->
			let inv = env.g_prover.nf_cprop [] inv in
			let _ = pp "@.FOUND RESOURCE INVARIANT:@.%a@." pp_cprop inv in
	  	Hashtbl.add env.g_renv rid inv;
			let inv' = make_stable env inv rely in
			let fr =
		  try env.g_prover.find_frame_cprop [] inv' inv
		  with No_frame_found -> error_noframe loc "resource invariant" inv' inv  in
			test_leakmem ~warn:false loc fr;
			true
    | Cri_code (fv_post,c,loc) ->
			(** if qs is given, check the shape inferred so far by user provided qualifers
					can dominiate the initialization. Initialization => shape => Postcondition 
					otherwise inferring shape *)
			let _ = Hashtbl.add env.g_renv rid cprop_empty in
			let cp = eprop_of_cprop cprop_empty in
			let cq = calculate_post env cp c fv_post qs "resource" in
			let cq = List.map cform_of_eform cq in
			let cq = 
		  	let fv = IdSet.diff (prop_fv cq IdSet.empty) fv_post in
		  	let sub = mk_gensym_garb_subst_idset fv in
		  	map_cprop sub cq 
			in
			let cq = match env.g_linear_pre with
		  	| None -> cq
		  	| Some cpre -> cprop_star cpre cq in		
			if (!qs_given) then
				(** Obtain current inv from qs and check that cq => inv *)
				let shape_qs = Hashtbl.find qs rid in
				let cprop_of_qs qs = qs
					(*List.fold_left (fun res q -> cprop_star res (Qualifier.expand_shape_qualifier q)) 
						Assertions.cprop_empty qs*) in
				let shape_inv = env.g_prover.nf_cprop [] (cprop_of_qs shape_qs) in
				(** interger variables in cq are made existentially quantified *)
				(*let abstract_init_post cq = 
					let rec abstract_init_post_rec fld = 
						try
							let comp = Fld.containing (E.zero) fld in
							let fld' = Fld.set comp (E.gensym_str_ex "ex") fld in
							abstract_init_post_rec fld'
						with _ -> fld in
					List.map (fun cf -> 
							let ((pl', sp'), sl') = cf in
							let sp' = List.map (fun s -> 
								match s with
									| Csp_node (t, c, e, fld) -> Csp_node (t, c, e, abstract_init_post_rec fld)
									| _ -> s 
								) sp' in
							((pl', sp'), sl')
						) cq in
				let cq = abstract_init_post cq in*)
				let shape_inv = make_stable env shape_inv rely in
				let _ = pp "@.print shape_inv as @.%a@." pp_cprop shape_inv in
				try (
					(*ignore (Qualifier.subtract env.g_prover shape_inv cq);*)
					Hashtbl.replace env.g_renv rid shape_inv; 
					true
				) 
				with _ -> 
					(pp "@.Cannot prove the shape invariants @.%a@. dominates initial conditions @.%a@."
					pp_cprop shape_inv pp_cprop cq; false) 
			else if (!inv_given) then
				try 
					let shape_qs = Hashtbl.find qs rid in
					let shape_inv = env.g_prover.nf_cprop [] shape_qs in
					let shape_inv = make_stable env shape_inv rely in
					let _ = pp "@.print shape_inv as @.%a@." pp_cprop shape_inv in
					(Hashtbl.replace env.g_renv rid shape_inv; true)
				with _ -> (
						let inv = make_stable env cq rely in
						if !verbose >= 2 && not (Genarith.enabled ()) then
		  				pp "@.FOUND RESOURCE INVARIANT:@.%a@." pp_cprop inv;
							Hashtbl.replace env.g_renv rid inv; true
				)
			else begin
				let inv = make_stable env cq rely in
				if !verbose >= 2 && not (Genarith.enabled ()) then
		  		pp "@.FOUND RESOURCE INVARIANT:@.%a@." pp_cprop inv;
				Hashtbl.replace env.g_renv rid inv; true
			end 
  with Symbolic_execution_error -> false

let check_entailment env qs (fname,(cp1,c,pure_code,cp2,res_lv,loc)) =
  let params = (Hashtbl.find env.g_fun_ht fname).fun_param in
  let params = List.fold IdSet.add (snd params) IdSet.empty in
  env.g_params <- params;
  linear_pure_code := pure_code;
  if str_is_cutpoint fname then true
  else if str_is_fair fname then
    if Genarith.enabled () then
      (pp "@.int %s = 0;@." fname; true)
    else 
      (pp "@.WARNING: Ignoring function %s@." fname; true)
  else begin
    pp_comment ("Function " ^ fname);
    (if !verbose >= 3 && pure_code != [] then
       pp "@.Pure checker:@.  %a@." pp_cmd pure_code);
    (* Normalize the precondition and the postcondition *)
    let cp1 = env.g_prover.nf_cprop [] cp1 in
    let cp2 = env.g_prover.nf_cprop [] cp2 in
    if !verbose >= 3 then
      pp "@.VERIFICATION CONDITION:@.[@[%a@]]@.%a@.[@[%a@]]@.@."
			pp_cprop cp1 pp_cmd c pp_cprop cp2;
    try 
      (* 1. Create entry and exit node(s) for the arithmetic program *)
      let (n1,ep1) = eprop_of_cprop_at_start_node cp1 in
      let ep2 = eprop_of_cprop cp2 in
      ext_append_return ep2;
      (* 2. Execute the body *)
      let cq = calculate_post env ep1 c (prop_fv cp2 res_lv) qs fname in
      if !verbose >= 4 then pp "@.Derived postcondition:@.%a@." pp_eprop cq;
      (* 3. Check the postcondition *)
      let fr =
				try ext_ext_subtract env.g_prover cq ep2
				with No_frame_found -> error_noframe_ext loc "postcondition" cq cp2 in
      test_leakmem loc fr             (* Are there any memory leaks? *) ;
      pp_generated_function fname n1  (* Output integer program *) ;
			(**  MCPA major update:
					 4. Check shape => Postcondition  *)
			if (!qs_given) then begin
				(*let r_prop = List.map (fun ef -> Genarith.cform_of_eform ef) cq in 	
	    	let r_prop = prop_kill_can_return r_prop in
	    	let fv = prop_fv r_prop IdSet.empty in
	    	let locals = IdSet.diff (IdSet.diff fv env.g_globals) env.g_params in
	    	let sub = mk_gensym_garb_subst_idset locals in
				let r_prop = map_cprop sub r_prop in
	  		let (sub, _) = mk_gensym_garb_subst_idset2 env.g_params in
				let r_prop = map_cprop sub r_prop in
				let r_invs = Hashtbl.create 16 in
				let _ = List.iter (fun (uf, scpl) -> 
					PList.iter (fun rid rcp -> 
							if (Hashtbl.mem r_invs rid) then
								let pre_inv = Hashtbl.find r_invs rid in
								Hashtbl.replace r_invs rid (Assertions.cprop_or pre_inv rcp)
							else Hashtbl.add r_invs rid rcp
						) scpl
					) r_prop in
				Hashtbl.iter (fun rid rcp -> 
					if !verbose >= 2 && not (Genarith.enabled ()) then
		  			pp "@.RESOURCE INVARIANT UPGRADE TO:@.%a@." pp_cprop (env.g_prover.nf_cprop [] rcp);
						Hashtbl.replace env.g_renv rid rcp;
					) r_invs;*)
			eliminate_inplace env qs cq
			end;
      true
    with Symbolic_execution_error -> false
  end

(* ----------- HACK ---- TODO ----------- *)
let check_entailment env qs (fname,(cp1,c,pure_code,cp2,res_lv,loc)) =
    check_entailment env qs (fname,(cp1,c,[],cp2,res_lv,loc))
 || (pure_code != [] && check_entailment env qs (fname,(cp1,c,pure_code,cp2,res_lv,loc)))

(** Check VCs without doing action inference. *)
let check_no_inference env ril entl qs =
	(** check_resource and check_entailment have the function to update qs (Hashtbl) *)
  List.for_all (check_resource env qs) ril
  && List.for_all (check_entailment env qs) entl

let update_res_ht env = 
  List.iter (fun rid -> Hashtbl.replace env.g_res_ht rid [])
    (Hashtbl.fold (fun k _ r -> k :: r) env.g_res_ht []) ;
  List.iter 
    (fun (rid,act) ->
       (try Hashtbl.find env.g_res_ht rid with Not_found -> [])
       |> List.append (action_deconvert act)
       |> Hashtbl.replace env.g_res_ht rid)
    env.g_guarantee
		
(* -------------------------------------------------------------------------- *)
(** {2 MCPA's Linearizability checking} *)
(* -------------------------------------------------------------------------- *)
(** The real robust and sound lineariazability checking implementation *)

(** Search all update points to decide if past views can be used
 * This step is heuristic:
 * If, in one method, there are two instructions that both update the linking fields
 * of different nodes, then we forbid the use of past views
 *)
let allow_past_view env =
	let lins = env.cand_lin_point in
	Hashtbl.fold (fun fun_name returns res -> 
		if (res) then
			List.fold_left (fun res (locreturn, (_, effs)) ->
				if (res) then
					(let nup = List.fold_left (fun nup (_, (_, pre, fld_assignments, _, _)) ->
						(** Need to know if the instruction(s) update linking fields *)
						let sl = List.flatten (List.map (fun x -> snd (fst (List.hd x))) (flatten_condition pre)) in
						let links = List.fold_left (fun res spred -> match spred with
							| Csp_listsegi (_,SINGLE (snode, _),e,f,g,_,_,_) -> snode :: res
							| _ -> res 
							) [] sl in 
						let links = List.remove_duplicates links in
						nup + List.fold_left (fun nup (_, com, _) -> 
							if (List.exists (fun link -> (link = com)) links) then nup + 1
							else nup
							) 0 fld_assignments
						) 0 effs
					in (nup < 2) && res)
				else res
				) res returns
		else res
		) lins true

(** Translate a pexpr like Q.posthead.tl to node Q and fileds [head; tl] *)
let rec transl_pexpr_node pexpr = match pexpr with
	| Predicate.Field (field, pexpr) -> 
		let (node, fs) = transl_pexpr_node pexpr in
		(node, fs @ [field]) 
	| Predicate.Var id -> (Exp.E.id id, [])
	| _ -> (pp "Error Specification %a" Predicate.pprint_pexpr pexpr; assert false) 

(** Before get reachable heap segments, need to solve the path prefix like 
		Q.head.posttl or Q.head.pretl *)
let mcpa_find_heap_content node fields sl = 
	let (res, sl) = List.fold_left (fun (res, sl) field -> match res with
		| Some node ->
			let (snodes, restsl) = List.partition (fun sp -> match sp with
				| Csp_node (_,_,e,_) -> Exp.equal_exp e node
				| _ -> false 
				) sl in
			if (List.length snodes = 1) then
				let snode = List.hd snodes in
				match snode with
					| Csp_node (_, _, e, fld) ->
						(let com = component_of_string ("." ^ field) in
						try (Some (Fld.get com fld), restsl) with Not_found ->
							(pp "Invalid speicification@."; assert false))
					| _ -> (pp "internal bug@."; assert false)
			else if (List.length snodes = 0) then (None, sl) 
			else (pp "Internal implementation bug@."; assert false)
		| None -> (res, sl)
		) (Some node, sl) fields
	in match res with
		| Some res -> (res, sl)
		| None -> (node, sl)

(** The reachable set of sp is different for pure and eff prop verification *)
let rec mcpa_get_reachable pure froml sl pure_or_eff = 
	let add x y = if List.exists (fun y -> equal_exp x y) y then y else x::y in
  let add_reach_vars res sp = match sp with
    | Csp_node (_,_,e,fld) -> Fld.fold_val add fld res
    | Csp_listsegi(_,_,e,f,g,h,_,_) -> add e (add f (add g (add h res)))
    | Csp_arr (_,e,f,g,_,_,_) -> add e (add f (add g res))
    | Csp_indpred _ -> res  in
  let is_pred_reachable x sp = match sp with
    | Csp_arr (_,e,_,_,_,_,_) (*TODO*)
    | Csp_node (_,_,e,_) -> equal_exp x e && 
														((Exp.compare_exp (Pure.to_sub pure e) E.zero) <> 0)
    | Csp_listsegi(_,SINGLE _,e,_,_,_,_,_) -> equal_exp x e && 
																							((Exp.compare_exp (Pure.to_sub pure e) E.zero) <> 0)
    | Csp_listsegi(_,(XOR _ | DOUBLE _),e1,_,e2,_,_,_) -> 
			(equal_exp x e1 && ((Exp.compare_exp (Pure.to_sub pure e1) E.zero) <> 0)) || 
			(equal_exp x e2 && ((Exp.compare_exp (Pure.to_sub pure e2) E.zero) <> 0))
    | Csp_indpred _ -> false in
  let rec go_reach seen todo sl1 sl2 = match todo with
    | [] -> (sl1, sl2)
    | x::todo -> 
			let (sl1new,sl2) = List.partition (is_pred_reachable x) sl2 in
			let (sl1new,sl2) = 
				if ((List.length sl1new) = 0) then
					(* new spred is not found... seek if their alias refer any spred *)
					List.partition (is_pred_reachable (Pure.to_sub pure x)) sl2
				else (sl1new, sl2) (* new spred is found *) in
			let seen = x::seen in
			let todo = List.fold_left add_reach_vars todo sl1new in
			let todo = List.filter (fun x -> not (List.exists (fun y -> equal_exp x y) seen)) todo in
			go_reach seen todo (sl1new @ sl1) sl2 in
	let islist = List.exists (fun s -> match s with Csp_listsegi _ -> true | _ -> false) sl in
	if (pure_or_eff && islist) then (** For pure property verification, get an old view *)
		let (cursl, possible_presl) = go_reach [] froml [] sl in 
		(*let _ = List.iter (fun r -> pp "pastview: %a@." pp_spred r) cursl in*)
		get_old_view pure cursl possible_presl
	else go_reach [] froml [] sl 
	
(** To verify pure properties, need to extract an old view of the remembered witness 
 * cursl @ possible_presl = sl.
 * while (cursl, possible_presl) is obtained from the call of mcpa_get_reacable pure froml sl
 * It is possible some abstract head existed in possible_presl 
 * This method just extract the previous view before stablization.
 *)
and get_old_view pure cursl possible_presl = 
	(** 1. Visit possible_presl to find abstract head *)
	let res = List.fold_left (fun res sp -> match sp with
		| Csp_node (_,_,e,fld) -> 
			(** 2. Obtain the sl from abstract head *)
			let (c', p') = (mcpa_get_reachable pure [e] (cursl @ possible_presl) false) in
			if (List.exists 
					(fun (c'', p'') -> List.isPrefix (Assertions.compare_can_spred) c' c'') 
					res) then res
			else 
				let res = List.filter 
										(fun (c'', p'') -> not (List.isPrefix (Assertions.compare_can_spred) c'' c')) 
										res in
				(c', p') :: res
		| _ -> res
		) [] possible_presl in
	match res with
		| [] -> (cursl, possible_presl)
		| [r] -> (let _ = Misc.pp "Note get an old view@." in
			let _ = List.iter (fun r -> pp "Note: %a@." pp_spred r) (fst r) in
			r)
		| _::_::_ -> (Misc.pp "FIXME: more than one abstract head
		is considered impossible by developers.@."; 
		List.iter (fun (r, _) -> 
			let _ = pp "===@." in
			let _ = List.iter (fun r -> pp "Note: %a@." pp_spred r) ( r) in
			pp "===@."
			) res;
		Misc.pp "FIXME: Just pick one ... Now if verified then still sound any way!!";
		List.hd res)	
		
(** If a list segment's start and end tend to be the same, remove it! *)		
let filter_empty_lseg pure sl = 
	List.map_partial (fun s -> match s with
		| Csp_listsegi(_,_,e,f,g,h,_,_) -> 
			if Exp.equal_exp (Pure.to_sub pure e) (Pure.to_sub pure f) then None
			else Some s
		| _ -> Some s
		) sl

let getReachableCsps prepure presl postpure postsl pexpr pure_or_eff = 
	match pexpr with
		| Predicate.Field (field, pointer) -> 
			if (String.length field >= 3 && (String.compare (String.sub field 0 3) "pre") = 0) then
				let field = String.sub field 3 (String.length field - 3) in
				
				let (pointer, fields) = transl_pexpr_node pointer in
				let fields = if ((String.compare "" field) = 0) then fields else fields @ [field] in
				let (pointer, presl) = mcpa_find_heap_content pointer fields presl in 
				
				(*let pointer_name = match pointer with
					| Some id -> id
					| _ -> (Misc.pp "Invalid memory location%a@." Predicate.pprint_pexpr pexpr; assert false) in*)
				let (rl, _) = mcpa_get_reachable prepure [pointer] presl pure_or_eff in
				(*let _ = pp "Pre shape abstraction@." in*)
				let rl = (*filter_empty_lseg prepure*) (List.rev rl) in
				(*let _ = List.iter (fun r -> pp "Note: %a@." pp_spred r) rl in*) rl
				(*if (String.length field = 0) then rl else List.tl (rl)*)
			else if (String.length field >= 4 && String.compare (String.sub field 0 4) "post" = 0) then
				let field = String.sub field 4 (String.length field - 4) in
				
				let (pointer, fields) = transl_pexpr_node pointer in
				(*let _ = pp "Given pointer as %a@." pp_exp pointer in*)
				let fields = if ((String.compare "" field) = 0) then fields else fields @ [field] in
				(*let _ = List.iter (fun r -> pp "2See: %a@." pp_spred r) postsl in*)
				let (pointer, postsl) = mcpa_find_heap_content pointer fields postsl in
				(*let _ = pp "Target pointer parsed as %a@." pp_exp pointer in*)
				(*let pointer_name = match pointer with
					| Some id -> id
					| _ -> (Misc.pp "Invalid memory location%a@." Predicate.pprint_pexpr pexpr; assert false) in*)
				let (rl, _) = mcpa_get_reachable postpure [pointer] postsl pure_or_eff in
				(*let _ = pp "Post shape abstraction@." in*)
				let rl = (*filter_empty_lseg postpure*) (List.rev rl) in
				(*let _ = List.iter (fun r -> pp "Note: %a@." pp_spred r) rl in*) rl
				(*if (String.length field = 0) then rl else (List.tl (rl))*)
			else []
		| _ -> []

(** Analyze the programmer provided set spec to know how to unfold *)
let unfold_strategy pred = match pred with
	| Predicate.Or (Predicate.Not (Predicate.In _), p) -> (
			let eles = Predicate.flatten_and p in
			(List.fold_left (fun res ele -> match ele with
				Predicate.Atom (Predicate.FunApp (field, _), Predicate.Eq, pe) ->
					(component_of_string ("." ^ field), Predicate.transl_exp pe) :: res
				| _ -> res
				) [] eles, 
			List.fold_left (fun res ele -> match ele with
				Predicate.Atom (Predicate.FunApp (field, _), rel, pe) 
				when (rel != Predicate.Eq)->
					(Predicate.Atom (Predicate.Var (Id.create field), rel, pe)) :: res
				| _ -> res
				) [] eles)
		)
	| _ -> (pp "Cannot identify set specification"; assert false)

(** Unfold a field *)
let unfold_field resourcepred presl postsl pexpr = 
	match pexpr with
		| Predicate.Field (field, pointer) -> 
			if ((String.compare (String.sub field 0 3) "pre") = 0) then
				let field = String.sub field 3 (String.length field - 3) in
				let (pointer, fields) = transl_pexpr_node pointer in
				let fields = if ((String.compare "" field) = 0) then fields else fields @ [field] in
				let (pointer, _) = mcpa_find_heap_content pointer fields presl in 
				Predicate.transl_pexp pointer
			else if ((String.compare (String.sub field 0 4) "post") = 0) then
				let field = String.sub field 4 (String.length field - 4) in
				let (pointer, fields) = transl_pexpr_node pointer in
				let fields = if ((String.compare "" field) = 0) then fields else fields @ [field] in
				let (pointer, _) = mcpa_find_heap_content pointer fields postsl in 
				Predicate.transl_pexp pointer
			else (pp "Unfolding field error field is %a@." Predicate.pprint_pexpr pexpr; assert false)
		| _ -> pexpr

let unfold_val_field resourcepred presl postsl pexpr =
	match pexpr with
		| Predicate.Field (field, pointer) -> 
			if ((String.compare (String.sub field 0 3) "pre") = 0) then
				let field = String.sub field 3 (String.length field - 3) in
				let (pointer, fields) = transl_pexpr_node pointer in
				let fields = if ((String.compare "" field) = 0) then fields else fields @ [field] in
				let (pointer, _) = mcpa_find_heap_content pointer fields presl in 
				(** Whether extend a node depend upon the fact that if this node is updated *)
				let values = List.map_partial (fun node -> match node with
					| Csp_node (_, _, e, fld) when (Exp.compare_exp pointer e = 0) -> 
						Some (Fld.get Misc.list_data_tag fld)
					| _ -> None
					) presl in
				let values' = List.map_partial (fun node -> match node with
					| Csp_node (_, _, e, fld) when (Exp.compare_exp pointer e = 0) -> 
						Some (Fld.get Misc.list_data_tag fld)
					| _ -> None
					) postsl in
				if (List.length values = 1 && List.length values' = 1 && 
							Exp.compare_exp_list values values' != 0) then 
					Predicate.transl_pexp (List.hd values)
				else 
					Predicate.FunApp ("val", [Predicate.transl_pexp pointer])
			else if ((String.compare (String.sub field 0 4) "post") = 0) then
				let field = String.sub field 4 (String.length field - 4) in
				let (pointer, fields) = transl_pexpr_node pointer in
				let fields = if ((String.compare "" field) = 0) then fields else fields @ [field] in
				let (pointer, _) = mcpa_find_heap_content pointer fields postsl in 
				(*let pexps = List.map_partial (fun node -> match node with
					| Csp_node (_, _, e, fld) when (Exp.compare_exp pointer e = 0) -> 
						Some (Predicate.transl_pexp (Fld.get Misc.list_data_tag fld))
					| _ -> None
					) postsl in
				if (List.length pexps = 1) then List.hd pexps
				else*) 
				Predicate.FunApp ("val", [Predicate.transl_pexp pointer])
			else (pp "Unfolding field error field is %a@." Predicate.pprint_pexpr pexpr; assert false)
		| _ -> Predicate.FunApp ("val", [pexpr])

(** resourcepred indicates how a memory location (under a recurisve function) should be unrolled
    purepred indicates the future behaviors 
		pure_or_eff indicates whether past views need to be built
		fn indicates the recursive function on the memory location
		pexpr inddicate the memory location *)
let unfold_func resourcepred purepred prepure presl postpure postsl pure_or_eff fn pexpr = 
	let (fn, connection) = 
		try let index = String.index fn '_' 
		in (String.sub fn 0 index, String.sub fn (index+1) (String.length fn - index - 1))
		with _ -> (fn, "") in
	(*let _ = Misc.pp "fn = %s and connection = %s\n" fn connection in*)
	(** if under purepred fld meets condition, then return true otherwise false *)
	let filter purepred prepure postpure is_preheap fld conditions = 
		if (List.length conditions = 0) then true
		else 
			(** if this fld does not mention enough information in conditions
		 		* simply return true
				*)
			let required_fields = List.fold_left (fun res p -> match p with
				Predicate.Atom (Predicate.Var f, _ , _) -> f :: res 
				| _ -> res
				) [] conditions in
			let having_fields = Fld.fold (fun com exp res -> 
				Id.create (Misc.string_of_field_component com) :: res
				) fld [] in
			let is_decidable = List.for_all (fun f -> 
				List.exists (fun f' -> 
					Id.compare f f' = 0
					) having_fields
				) required_fields in
			if (is_decidable) then (** We have all the information to decide this csp *)
				let actual = Fld.fold (fun com exp res -> 
					let exp = List.hd (Exp.map_sub (Predicate.transl_subs purepred) [exp]) in
					let exp = 
						if is_preheap then (Pure.to_sub prepure exp)
						else (Pure.to_sub postpure exp) in
					(Predicate.Atom 	
					(Predicate.Var (Id.create (Misc.string_of_field_component com)), 
					Predicate.Eq, 
					Predicate.transl_pexp exp)) :: res
					) fld [] in
				let p = Predicate.big_and (purepred::actual) in
				let p = 
					if is_preheap then
						let explist = Pure.to_exp prepure in
						let pu = Predicate.transl_pred explist in
						Predicate.And (pu, p)
					else 
						let explist = Pure.to_exp postpure in
						let pu = Predicate.transl_pred explist in
						Predicate.And (pu, p)
				in
				let expect = Predicate.big_and conditions in
				let result = TheoremProver.implies p expect in
				(TheoremProver.finish (); result) 
			else (** We have incomplete information. Abstractly return true *) 
				true in
	let transl_csp_val sp = 
		(** See the heaplet is for preheap or postheap *)
		let is_preheap = match pexpr with
			| Predicate.Field (field, pointer) -> 
				if ((String.compare (String.sub field 0 3) "pre") = 0) then true
				else if (String.compare (String.sub field 0 4) "post" = 0) then false
				else (Misc.pp "Dealing with unknonw heaplet@."; assert false)
			| _ -> (Misc.pp "Dealing with unknonw heaplet@."; assert false)
		(** Present it by formula abstraction *) in
		match sp with
			| Csp_node (_,_,e,fld) ->
				let (conditions, conditions') = unfold_strategy resourcepred in
				let result = List.fold_left (fun res (comp, expect) -> 
					try let actual = Fld.get comp fld in
							let actual = List.hd (Exp.map_sub (Predicate.transl_subs purepred) [actual]) in
							let actual = 
								if is_preheap then (Pure.to_sub prepure actual)
								else (Pure.to_sub postpure actual) in
							((Exp.compare_exp actual expect) = 0) && res
					with _ -> res
					) true conditions in
				(*let result = if (List.length conditions = 0) then false else result in*)
				if (result && (filter purepred prepure postpure is_preheap fld conditions')) then 
					if ((String.compare fn "datas") = 0) then
						(** datas are built-in recursive function that is identical to vals 
              * We unfold data field of a node directly
							*)
						try let dataexp = Fld.get (Misc.component_of_string ".data") fld in
						Some (Predicate.transl_pexp dataexp) with _ -> 
						Some (Predicate.FunApp ("val", [Predicate.Var (Exp.Id.of_exp e)]))
					else
						Some (Predicate.FunApp ("val", [Predicate.Var (Exp.Id.of_exp e)]))
				else None
	 		| Csp_listsegi (_,SINGLE (_, fld),e,f,g,_,_,_) ->
				let last = try Predicate.Var (Exp.Id.of_exp f) with _ -> Predicate.PInt 0 in 
				let first = Predicate.Var (Exp.Id.of_exp e) in
				let (conditions, conditions') = unfold_strategy resourcepred in
				let result = List.fold_left (fun res (comp, expect) -> 
					try let actual = Fld.get comp fld in
							((Exp.compare_exp actual expect) = 0) && res
					with _ -> res
					) true conditions in
				(*let result = filter purepred fld conditions in*)
				if (result && filter purepred prepure postpure is_preheap fld conditions') then 
					Some (Predicate.FunApp ("vals", [first; last]))
				else None
	 		| _ -> (Misc.pp "Note supported csp@."; assert false) in	
	let csps = getReachableCsps prepure presl postpure postsl pexpr pure_or_eff in
	(* Our implementation provides some built-in recursive definitions *)
	if ((String.compare fn "vals") = 0 || (String.compare fn "datas") = 0) then 
		(*let exps = List.map transl_csp_val csps in*) 
		let exps = List.map_partial transl_csp_val csps in
		if (List.length exps = 0) then Predicate.Var (Id.junk) (* return empty set *)
		else (* with only soley pointer argument it is unfolded *) 
			if (String.compare connection "c" = 0) then
				(** sort the unfoldings *)
				let (hdexp, tlexps) = (List.hd exps, List.tl exps) in
				List.fold_left (fun res exp -> Predicate.Concat (res, exp)) hdexp tlexps
			else
				(** sort the unfoldings *)
				let exps = List.stable_sort compare exps in
				let (hdexp, tlexps) = (List.hd exps, List.tl exps) in
				List.fold_left (fun res exp -> Predicate.Union (res, exp)) hdexp tlexps
	else if ((String.compare fn "val") = 0) then
		(*Predicate.FunApp ("val", [unfold_field resourcepred presl postsl pexpr])*)
		unfold_val_field resourcepred presl postsl pexpr
	else (* Recursive definition is undefined. Throw exceptions *) 
		raise Predicate.Unfold_ex
		
let unfold_pred resourcepred prepure presl postpure postsl pure_or_eff fn pexpr = 
	let transl_csp sp = match sp with
		| Csp_node (_,_,e,fld) ->
			Predicate.FunApp ("val", [Predicate.Var (Exp.Id.of_exp e)])
 		| Csp_listsegi (_,SINGLE _,e,f,g,_,_,_) ->
			let last = try Predicate.Var (Exp.Id.of_exp f) with _ -> Predicate.PInt 0 in 
			let first = Predicate.Var (Exp.Id.of_exp e) in
			Predicate.FunApp ("vals", [first; last])
 		| _ -> (Misc.pp "Note supported csp@."; assert false) in
	let csps = getReachableCsps prepure presl postpure postsl pexpr pure_or_eff in 
	(* Our implementation provides some built-in recursive predicates *)
	if ((String.compare fn "sorted") = 0) then
		(*let exps = List.map transl_csp csps in*)
		let csps_len = List.length csps in
		if (csps_len = 0) then 
			(Misc.pp "Recursive predicate must be defined on pointer argument@."; assert false)
		else if (csps_len = 1) then Predicate.Recpred (fn, transl_csp (List.hd csps))
		else	
			let (hdcsp1, hdcsp2) = (List.hd csps, List.hd (List.tl csps)) in
			(* our implementation provides some built-in resursive predicate *)
			snd (List.fold_left 
				(fun (prev, fm) csp -> 
					(csp, match csp with 
						| Csp_node _ -> 
							Predicate.And (Predicate.Atom (transl_csp prev, Predicate.Le, transl_csp csp), fm)
						| _ -> Predicate.And (Predicate.Recpred (fn, transl_csp csp), 
						Predicate.And (Predicate.Atom (transl_csp prev, Predicate.Le, transl_csp csp), fm)))) 
				(hdcsp2, match hdcsp1 with
					| Csp_node _ -> (
						match hdcsp2 with
						| Csp_node _ ->
							Predicate.Atom (transl_csp hdcsp1, Predicate.Le, transl_csp hdcsp2)
						| _ ->
							Predicate.And (Predicate.Recpred (fn, transl_csp hdcsp2), 
							Predicate.Atom (transl_csp hdcsp1, Predicate.Le, transl_csp hdcsp2))
						)
					| _ -> 
					Predicate.And (Predicate.Recpred (fn, transl_csp hdcsp1), match hdcsp2 with
						| Csp_node _ ->
							Predicate.Atom (transl_csp hdcsp1, Predicate.Le, transl_csp hdcsp2)
						| _ ->
						Predicate.And (Predicate.Recpred (fn, transl_csp hdcsp2), 
							Predicate.Atom (transl_csp hdcsp1, Predicate.Le, transl_csp hdcsp2)))) 
				(List.tl (List.tl csps)))
	else (* Recursive pre *)
		raise Predicate.Unfold_ex

(** Translate the pure part into predicate  *)
let getPurePred cp = 
	let _ = if (List.length cp <> 1) then (Misc.pp "Warning: linearizability cannot be ensured!@."; assert false) in
	let ((pure, sl), scpl) = List.hd cp in
	let _ = if (PList.length scpl <> 0) then (Misc.pp "Warning: linearizability cannot be ensured!@."; assert false) in
	(** type of pure is (Id.t, exp) plist * exp list *)
  let explist = Pure.to_exp pure in
	let pure_pred = Predicate.transl_pred explist in
	(** Collect a set of linkers *)
	let links = List.fold_left (fun res spred -> match spred with
		| Csp_listsegi (_,SINGLE (snode, _),e,f,g,_,_,_) -> snode :: res
		| _ -> res 
		) [] sl in
	let sl_pred = Predicate.big_and (List.map (fun spred -> match spred with
			| Csp_node (_,nextcom,e,fld) ->
				let fld = List.fold_left (fun res link -> Fld.remove link res) fld links in
				let vs = Fld.fold (fun com exp l -> (com, exp) :: l) fld [] in 
				let pvs = List.map (fun (com, exp) -> 
					Predicate.Atom (
					Predicate.transl_pexp exp, 
					Predicate.Eq, 
					Predicate.FunApp (string_of_field_component com, [Predicate.Var (Exp.Id.of_exp e)]))) vs in
				Predicate.big_and pvs
	  		(* let v = Fld.get Misc.list_data_tag fld in
					let pv = Predicate.transl_pexp v in
					Predicate.Atom (
						pv, 
						Predicate.Eq, 
						Predicate.FunApp (string_of_field_component (Misc.list_data_tag), [Predicate.Var (Exp.Id.of_exp e)]))*)
			| Csp_listsegi (_,SINGLE _,e,f,g,_,Cem_NE,_) ->
				let last = try Predicate.Var (Exp.Id.of_exp f) with _ -> Predicate.PInt 0 in 
				let first = Predicate.Var (Exp.Id.of_exp e) in
				let pg = Predicate.transl_pexp g in
	  		Predicate.And (
						Predicate.Atom (
						pg,
						Predicate.Eq,
						Predicate.FunApp (string_of_field_component (Misc.list_data_tag) ^ "s", [first; last]))
					  ,
						Predicate.Atom (
						first,
						Predicate.Ne,
						last)
					)
	 		| Csp_listsegi (_,SINGLE _,e,f,g,_,_,_) ->
				let last = try Predicate.Var (Exp.Id.of_exp f) with _ -> Predicate.PInt 0 in 
				let first = Predicate.Var (Exp.Id.of_exp e) in
	  		Predicate.Atom (
					Predicate.Var (Exp.Id.of_exp g),
					Predicate.Eq,
					Predicate.FunApp (string_of_field_component (Misc.list_data_tag) ^ "s", [first; last]))
	 		| _ -> Predicate.True
		) sl) in
	let subs = List.fold_left (fun res spred -> match spred with
		| Csp_node (_,_,e,fld) -> (
			try let v = Fld.get Misc.list_data_tag fld in
					let v' = List.hd (Exp.map_sub (Pure.to_sub pure) [v]) in
			(Exp.Id.of_exp v', 
			Predicate.FunApp (string_of_field_component (Misc.list_data_tag), [Predicate.Var (Exp.Id.of_exp e)])) 
			:: res
			with _ -> res 
			)
		| _ -> res) [] sl in
	(Predicate.big_and [pure_pred; sl_pred], subs)
	
(** Checks effectful specification is held 
 *)
let mcpa_check_eff_spec rdefs purepred paths precondition postcondition spec = 
	(** 1. Forms verification condition (VC) *)
	(** 2.1 Maps pointer fields to all the set of locations reachable from them *)
	(** 2.2 Unfold recursive predicate and recursive functions *)
	(** 3. Verifies the VC's validity *)
	let specid = component_of_string (fst spec) in
	let (pure, subs) = getPurePred postcondition in
	(** Do a substitution before unfolding for spec *)
	let spec = Predicate.apply_substs subs (snd spec) in
	(* postcondition is well-formed checked by getPurePred *)
	let postsl = snd (fst (List.hd postcondition)) in
	let postpure = fst (fst (List.hd postcondition)) in
	let presl = snd (fst (List.hd precondition)) in (* Assume... Fixme? *)
	let prepure = fst (fst (List.hd precondition)) in
	let vc = Predicate.unfold_recursive_defnition spec 
		(unfold_func (Hashtbl.find rdefs specid) purepred prepure presl postpure postsl false) 
		(unfold_pred (Hashtbl.find rdefs specid) prepure presl postpure postsl false) 
		(unfold_field (Hashtbl.find rdefs specid) presl postsl) in
	(** Effective operation may also need to see future behavior *)
	let _ = Misc.pp "@.==========Checking for linearizability specifications=============@." in
	(*let _ = if (List.length paths > 0) then (
		Misc.pp "Showing the paths: ";
		List.iter (fun path -> Misc.pp "%a " Predicate.pprint path) paths; Misc.pp "\n"
		) in*)
	let pure = Predicate.And (purepred, pure) in
	(** To support a read as linearization point before a future write *)
	let pure = Predicate.big_and (pure::paths) in
	let _ = Misc.pp "Pure is %a@." Predicate.pprint pure in
	let _ = Misc.pp "vc is %a@." Predicate.pprint vc in
	let result = TheoremProver.implies pure vc in
	(*let _ = Misc.pp "The checking result is %b@." result in*)
	(TheoremProver.finish (); result)
	
	
(** Check pure specification is held 
*)
let mcpa_check_pure_spec purepred postcondition spec returnpred rdefs allow_past_view = 
	(** 1. Forms verification condition (VC) *)
	(** 2.1 Maps pointer fields to all the set of locations reachable from them *)
	(** 2.2 Unfold recursive predicate and recursive functions *)
	(** 3. Verifies the VC's validity *)
	let specid = component_of_string (fst spec) in 
	let (purepost,_) = getPurePred postcondition in
	let postsl = snd (fst (List.hd postcondition)) in
	let postpure = fst (fst (List.hd postcondition)) in
	let spec = snd spec in
	if (spec = Predicate.Not Predicate.True) then false
	else
		let vc = Predicate.unfold_recursive_defnition spec
						(unfold_func (Hashtbl.find rdefs specid) purepred Pure.pfalse [] postpure postsl allow_past_view) 
						(unfold_pred (Hashtbl.find rdefs specid) Pure.pfalse [] postpure postsl allow_past_view) 
						(unfold_field (Hashtbl.find rdefs specid) [] postsl) in
		let vc = Predicate.big_and [purepred; purepost; vc] in
		let result = TheoremProver.implies vc returnpred in
		(TheoremProver.finish (); result)
	
type linear_kind = Eff | Pure | Wit	
	
let mcpa_check_linearizable env = 
	let lins = env.cand_lin_point in
	(** Checks effectful path *)
	(*let _ = pp "the size of lins is %d@." (Hashtbl.length lins) in*)
	let linearized_effps = Hashtbl.fold (fun fun_name returns linear_returns -> 
			(** 1. Obains the function's specification *)
			let _ = Misc.pp "@.Checking eff property for function %s@." fun_name in
			let _ = (Specpool.funname := fun_name) in
			let fi = Hashtbl.find env.g_fun_ht fun_name in
			(**2. Check the specification is held *)
			linear_returns @ (List.map (fun (l, wl, b) -> 
			(Misc.pp "Location %s is linearized@." (Location.lineno_to_string l); (l,wl,b)))
			(List.map_partial (fun (locreturn, (purepred, effs)) -> 
				let _ = Misc.pp "@.Working at return site %s@." (Location.lineno_to_string locreturn) in
				let _ = Misc.pp "Size of eff wit candidates = %d including: @." (List.length effs) in
				let _ = List.iter (fun (l, _) -> Misc.pp "%s@." (Location.lineno_to_string l)) effs in
				let effs = List.sort (fun (loc1, _) (loc2, _) -> 
						compare (Location.lineno_to_int loc1) (Location.lineno_to_int loc2)) effs in
				let effs = List.rev effs in
				try Some (locreturn, fst (List.find (
					fun (locwitness, (paths, pre, fld_assignments, lives, lp)) -> 
					let _ = Misc.pp "@.Verify function %s's at witness site %s@." 
									fun_name (Location.lineno_to_string locwitness) in
					(** 1. Obtains a set of conditions of possible pre-shape abstraction *)
					(*let _ = pp "@.%s'pre as @.%a@." fun_name pp_cprop pre in
					let _ = List.iter (fun (e1, com, e2) -> pp "@.%a.%s = %a@." pp_exp e1 
						(string_of_component com) pp_exp e2) fld_assignments in
					let _ = pp "lp as %b@." lp in*)
					let preconditions = flatten_condition pre in
					(** Define a check function which takes into the sequential or concurrent precondition
            * is_set_spec = true then verifying concurrent precondition
						* is_set_spec = false then verifying sequential precondition
						*)
					let check_precondition preconditions is_set_spec = 
						List.for_all (fun precondition -> 
							(*let _ = pp "@.Executing with precondition @.%a@." pp_cprop precondition in*)
							(** 2. Exectues for each possible pre-shape abstraction to obtain post-shape abstraction *)
							let postcondition = 
									match execute_fld_assign env (ref []) [] fld_assignments (eprop_of_cprop precondition) with
				  				| Some cq -> cq
				  				| None -> (pp "@.Failed to prove linearizability@."; assert false) in
							let postcondition = List.map cform_of_eform postcondition in
							(*let _ = pp "@.Executed postcondition @.%a@." pp_cprop postcondition in*)
							
							(** Important!! Not check for itself only but also check if others can be fuifilled by it *)
							let lives = (List.map Exp.Id.of_exp (Specpool.getNodeExps precondition))
								@ (Exp.IdSet.elements lives) in
							let lives = List.remove_duplicates lives in
							
							let t_descs = List.filter (fun live -> 
								Specpool.is_thread_desc fi.fun_lbs live) lives in 
							
							(** 3. Checks the pre- and post- shape abstraction are consistent to sequential specification *)
							if (List.length t_descs = 0) then 
								(** Note in this check, no thread descripor is used, we do not consider helping mechanism 
									* if is_set_spec = true, we translate the specification into set specification
									* otherwise is_set_spec = false, we use sequential state to check the original specification
									* if the spec uses concatation and this is an effectful method
									*)
								if (is_set_spec) then (** no matter what is the class of the spec translate it *)
									let spec = (fst (fi.fun_effspec), Predicate.transl_concat_union (snd (fi.fun_effspec))) in
									let _ = Misc.pp "The translated spec is %a@." Predicate.pprint (snd spec) in
									mcpa_check_eff_spec env.rdefs purepred paths precondition postcondition spec
								else if (Predicate.is_concat_pred (snd (fi.fun_effspec)) && (** concatation is using *)
									(let returnpred = Hashtbl.find fi.fun_returns locreturn in match returnpred with
										| Predicate.Atom (_, Predicate.Eq, Predicate.FunApp _) 
										| Predicate.Atom (_, Predicate.Eq, Predicate.Var _) -> true 
										| _ -> false
									) (** this is an effectful method *)) then 
									(** verify the orign spec using the sequential state *)	
									mcpa_check_eff_spec env.rdefs purepred paths precondition postcondition fi.fun_effspec
								else (** spec is set based so simply return true *) true
							else if (is_set_spec) then (** Note in this check, we simply use the original sepcification. *)
								(** Firstly identify the threads that passes when query *)
								(*let _ = Misc.pp "Begin to search helping mechanism\n" in*)
								let t_descs = List.map Exp.E.id t_descs in
								let t_descs = List.filter (fun t_desc -> 
									Specpool.when_query env.spec_pool t_desc precondition fi.fun_lbs) t_descs in
								if (List.length t_descs = 0) then
									let returnpred = Hashtbl.find fi.fun_returns locreturn in
									let spec = match returnpred with
										| Predicate.Atom (_, Predicate.Eq, pexp) -> 
											(fst (fi.fun_effspec), 
											Predicate.subst pexp Specpool.return_v (snd (fi.fun_effspec)) )
										| _ -> fi.fun_effspec in
									mcpa_check_eff_spec env.rdefs purepred paths precondition postcondition spec
								else 
									(** Secondly check the identified threads *)
									Specpool.check_by_t_descs locreturn precondition postcondition env.spec_pool 
													env.hp_launch
													t_descs 
													env.g_fun_ht 
													(mcpa_check_eff_spec env.rdefs purepred paths)		
							else true (** We do not check when is_set_spec = false we use the orginal
								            * specification so no need to sequentianality
														*)								
							) preconditions in
					check_precondition preconditions true && 
						(
						 let preconditions' = (** FIXME: reuse preconditions ?? *)
						 try flatten_condition (Hashtbl.find env.seq_table locwitness) 
						 with _ -> preconditions in
						 check_precondition preconditions' false
						)
					) effs), Eff) with Not_found -> None
				) returns))
			) lins []	in
	(*Hashtbl.fold (fun fun_name cand_points res -> 
		if res then 
			List.exists (fun (_, (pre, fld_assignments, lp)) -> 
			(** 1. Obtains a set of conditions of possible pre-shape abstraction *)
			let _ = pp "@.%s'pre as @.%a@." fun_name pp_cprop pre in
			let _ = List.iter (fun (e1, com, e2) -> pp "@.%a.%s = %a@." pp_exp e1 
				(string_of_component com) pp_exp e2) fld_assignments in
			let _ = pp "lp as %b@." lp in
			let preconditions = flatten_condition pre in
			(** 2. Obtains the function's effectul sequential specification *) 
			let fi = Hashtbl.find env.g_fun_ht fun_name in
			List.for_all (fun precondition -> 
				let _ = pp "@.Executing with precondition @.%a@." pp_cprop precondition in
				(** 2. Exectues for each possible pre-shape abstraction to obtain post-shape abstraction *)
				let postcondition = 
						match execute_fld_assign env (ref []) [] fld_assignments (eprop_of_cprop precondition) with
	  				| Some cq -> cq
	  				| None -> (pp "@.Failed to prove linearizability@."; assert false) in
				let postcondition = List.map cform_of_eform postcondition in
				let _ = pp "@.Executed postcondition @.%a@." pp_cprop postcondition in
				(** 3. Checks the pre- and post- shape abstraction are consistent to sequential specification *)
				mcpa_check_eff_spec precondition postcondition fi.fun_effspec
				) preconditions
			) cand_points
		else res 
		) lins true*)
		let _ = Misc.pp "@.Complete effective spec checking ...@." in 
		(*let _ = Misc.pp "Showing the spec pool ... \n" in
		let _ = Specpool.print_pool env.spec_pool env.hp_launch in*)
		let apv = allow_past_view env in
		let posts = env.non_eff_postconditions in
		(** Remove return sites that has been proved effective *)
		(** Checks non-effectful path *)
		
		let linearized_noneffps = Hashtbl.fold (fun fun_name returns linear_returns -> 
			if ((String.compare fun_name "resource") != 0) then
				(** 1. Obains the function's specification *)
				let _ = Misc.pp "@.Checking pure property for function %s@." fun_name in
				let _ = (Specpool.funname := fun_name) in
				let fi = Hashtbl.find env.g_fun_ht fun_name in
				let returns = List.filter 
					(fun (l, _) -> not (List.exists 
					(fun (l',_, _) -> (Location.lineno_to_int l = Location.lineno_to_int l')) linearized_effps)) 
					returns in 
				(**2. Check the specification is held (excluding resource init function) *)
				linear_returns @ List.map (fun (l, wl, b) -> 
					(Misc.pp "Location %s is linearized@." (Location.lineno_to_string l); (l,wl,b)))
					(List.map_partial (fun (locreturn, (purepred, noneffs)) -> 
					(*let _ = Misc.pp "Working at return site %s for function %s@." 
									(Location.lineno_to_string locreturn) fun_name in
					let _ = Misc.pp "noneffs size = %d, including @." (List.length noneffs) in
					let _ = List.iter (fun (l, _) -> Misc.pp "%s@." (Location.lineno_to_string l)) noneffs in*)
					let returnpred = try Hashtbl.find fi.fun_returns locreturn 
														with Not_found -> (* This site return void *) Predicate.True in
					(** UGLY. HACK. Substitute the result in purepred *)
					let purepred = 
						Predicate.apply_substs [(Id.result, Predicate.Var (Id.create "_Result"))] purepred in
					let uglysubst = Exp.mk_single_subst Id.result (Exp.E.id (Id.create "_Result")) in
					let noneffs = List.sort (fun (loc1, _) (loc2, _) -> 
							compare (Location.lineno_to_int loc1) (Location.lineno_to_int loc2)) noneffs in
					let noneffs = List.rev noneffs in
					let is_wit = ref false in
					try let found_l = fst (List.find (fun (locwitness, post) -> 
						(*let _ = Misc.pp "@.At site %s noneff witness is @.%a@." 
										 (Location.lineno_to_string locwitness) pp_cprop post in*)
						let funposts = flatten_condition post in
						List.for_all (fun funpost -> 
							let funpost = Assertions.map_cprop uglysubst funpost in
							mcpa_check_pure_spec purepred funpost fi.fun_purespec returnpred env.rdefs apv ||
							(let seqst = try Hashtbl.find env.seq_table locwitness with _ -> Assertions.cprop_false in
							is_wit := Specpool.whether_query env.spec_pool purepred returnpred funpost 
												seqst fi.fun_lbs;
							!is_wit
							)
						) funposts 
						) noneffs) in
					Some (locreturn, found_l, if(!is_wit) then Wit else Pure)  	
					with Not_found -> None
					) returns)
			else linear_returns
			) posts [] in
		let linearized_rs = linearized_effps @ linearized_noneffps in
		let non_linearized_rs = Hashtbl.fold (fun fname fi res -> 
			let rl = fi.fun_returns in
			let rl = Hashtbl.fold (fun k v res -> res @ [(k, v)]) rl [] in
			let failedsites = (List.map fst (List.filter (fun (r,_) -> 
				not (List.exists (fun (r',_,_) -> 
				Location.lineno_to_int r' = Location.lineno_to_int r
				) linearized_rs)) rl))
			in if (List.length failedsites = 0) then res else (fname, failedsites) :: res
			) env.g_fun_ht [] in
		let functional_checkresult = (List.length non_linearized_rs = 0) in
		let wellformness_checkresult = 
			if functional_checkresult && (Hashtbl.length env.hp_launch > 0) then
				(** checking well formness only if helping mechanism is discovered *)
				let _ = Misc.pp "@.Checking whether helping mechanism is well-formed@." in
				Hashtbl.fold (fun funname returns res ->
					if (res) then
						List.fold_left (fun res (locreturn, (_, effs)) -> 
							if (res) then
								List.fold_left (fun res (l, wl, b) ->
									if (Location.lineno_to_int l = Location.lineno_to_int locreturn) then
										match b with Pure -> res | _ ->
											Specpool.check_well_formness funname locreturn effs wl env.hp_launch env.g_fun_ht
											(execute_fld_assign env (ref []) [])
									else res
									) res linearized_rs					
							else res
							) res returns
					else res 
					) env.cand_lin_point true
			else functional_checkresult in
		let _ = pp "@.Verification completes! @.Summarizaiton of verificiation resulsts: @." in	
		let _ = List.iter (fun (l, wl, b) -> 
			pp "return site %s is linearized at site %s in a %s way@." 
			(Location.lineno_to_string l) (Location.lineno_to_string wl)
			(match b with Eff -> "Eff" | Pure -> "Pure" | Wit -> "helped")
			;
			) linearized_rs in
		let _ = List.iter (fun (fname, nlrs) -> 
			pp "Cannot verify %s's linearizability at site: " fname;
			List.iter (fun nlr -> pp "%s " (Location.lineno_to_string nlr)) nlrs;
			pp "@."
			) non_linearized_rs in
		wellformness_checkresult
			

(** Executes RGSep action inference and then checks linearizability. *)
let rec check_with_inference env ril entl qs =
  let rec go2 n =
    pp_line ();
    if n >= 10 then begin 
      if !verbose >= 1 then pp "@.ERROR: Exceeding number of allowed iterations.@.";
      false
    end else begin
      env.g_guar_changed <- false;
      actlr_clear entl;
			Hashtbl.clear env.g_renv;
      update_res_ht env;
			(** clear recorded pure postconditions  *)
			Hashtbl.clear env.non_eff_postconditions;
			Hashtbl.clear env.cand_lin_point;
      if !verbose >= 1 then begin
				pp "Iter: %d, #Actions: %d@." n (List.length env.g_guarantee);
				let n = ref 1 in
				List.iter 
			    			(fun (rid, (s,pl,cr,cp,cq)) ->
									pp "Action #%d %s: %s@.  @[<v>   %a@ |  %a @ ~> %a@]@."
									!n s (string_of_component rid)
									pp_uform (pl, cr)
									pp_uform (Pure.ptrue, cp)
									pp_uform (Pure.ptrue, cq); n := !n + 1)
			    		env.g_guarantee
			end;
      check_no_inference env ril entl qs
      	&& if env.g_guar_changed then begin
						go2 (n+1)
      end 
			else begin
				pp_line ();
				if !verbose >=1 then pp "DONE after iteration: %d@." n;
				if !verbose >= 1 then begin 
	  			pp "@.Inferred %d actions:@." (List.length env.g_guarantee);
	  			let n = ref 1 in
	  			List.iter 
	    			(fun (rid, (s,pl,cr,cp,cq)) ->
							pp "Action #%d %s: %s@.  @[<v>   %a@ |  %a @ ~> %a@]@."
							!n s (string_of_component rid)
							pp_uform (pl, cr)
							pp_uform (Pure.ptrue, cp)
							pp_uform (Pure.ptrue, cq); n := !n + 1)
	    		env.g_guarantee;
	  			actlr_print entl;
	  			Hashtbl.iter
	    		(fun r inv ->
	       	pp "@.Invariant of resource %s:@.  %a@." (string_of_component r) pp_cprop inv)
	    		env.g_renv
				end;
				if (!mcpa_infer >= 1) then
					(** Linearizability checking *)
					mcpa_check_linearizable env
				else true
    	end
    end 
	in go2 1


(* -------------------------------------------------------------------------- *)
(** {2 CAVE's Linearizability checking} *)
(* -------------------------------------------------------------------------- *)
(** Inline abs.specs at linearization points. *)
let linear_merge env entl_specs (fname,ent) =
  try 
    let (_,spec,_,_,_,_) = List.assoc ("ABS_"^fname) entl_specs in
    let params = (Hashtbl.find env.g_fun_ht fname).fun_param in
    let params = List.fold IdSet.add (snd params) IdSet.empty in

    let symbexe p c =
      List.map fst p
      |> linear_symbexe env.g_prover c IdSet.empty 
      |> List.map (fun uf -> (uf,PNil))
    in

    let go abs_post p = 
      let sub = mk_gensym_garb_subst_idset (IdSet.diff (fv_norm_cprop p) params) in
      let p = map_cprop sub p in
      let pl = List.map (fun ((p,_),_) -> Pure.only_inst_eqs p) p in
      let p = match pl with 
        | [] -> Pure.ptrue
        | p::pl -> List.fold Pure.common pl p in
      and_cprop_pure abs_post p 
    in

    actlr_merge_linear symbexe go spec (fname,ent)
  with Not_found -> []

let linear_check_assignment old_guar env ril entl qs =
  if !verbose >= 1 then List.iter (fun (_, (_,c,_,_,_,_)) -> pp_linear_annot !Misc.formatter c) entl;
  if !verbose >= 1 then actlr_print entl;
  env.g_guarantee <- [];
  if !infer = 2 then begin
    actlr_iter 
      (fun (s,cp) ->
         if List.for_all (fun (_,(s',_,_,_,_)) -> s' != s) env.g_guarantee then begin
           let (rname, (actname, p, ctx, pre, post)) = 
             try List.find (fun (_,(s',_,_,_,_)) -> s' == s) old_guar
             with Not_found -> pp_internal_error (); assert false in
           let sub = mk_gensym_garb_subst_idset (IdSet.remove ident_ABS (fv_norm_cprop cp)) in
           let abs_pre = map_spat sub (snd linear_abs_pre) in
           match map_cprop sub cp with
             | [((p',abs_post),_)] -> 
               if List.exists (function Csp_node(_,_,e,_) -> e == E.id ident_ABS | _ -> false) abs_post
               then begin 
                 let abs_pre = map_spat (Pure.to_sub p') abs_pre in
                 let act = (rname, (actname, p, ctx, pre @ abs_pre, post @ abs_post)) in
                 env.g_guarantee <- act :: env.g_guarantee
               end
             | _ -> ()
         end 
      ) entl;
    List.iter
      (fun (rname, (actname, p, ctx, pre, post)) -> 
         if List.for_all (fun (_,(s',_,_,_,_)) -> s' != actname) env.g_guarantee then begin
           let act = 
             (rname, (actname, p,
                      Csp_node (tag_default, node_component, E.id ident_ABS, Fld.emp) :: ctx,
                      pre, post)) in
           env.g_guarantee <- act :: env.g_guarantee
         end 
      ) old_guar;
  end;
  actlr_clear entl;
  if !verbose >= 1 then begin
    List.iter 
      (fun (rid, (s,pl,cr,cp,cq)) ->
         pp "Action %s: %s@.  @[<v>   %a@ |  %a @ ~> %a@]@."
           s (string_of_component rid)
           pp_uform (pl, cr)
           pp_uform (Pure.ptrue, cp)
           pp_uform (Pure.ptrue, cq))
      env.g_guarantee
  end;
  check_with_inference env ril entl qs


let check_linearizable env ril entl entl_specs qs =
  begin 
    env.g_no_interf_hack <- true;
    if !verbose >= 1 then pp "@.====== [ Linearizability prover: sequential run ] ==========================@.";
    let res = check_with_inference env ril entl qs in
    env.g_no_interf_hack <- false;
    res
  end && begin 
    let new_env = 
      { env with 
        g_linear_pre = 
          Some (try (Hashtbl.find env.g_fun_ht "init_ABS").fun_post
      	  with Not_found -> cprop_empty) } in
    let entl0 = 
      List.fold_right 
        (fun h r -> List.concat (List.map (fun x -> List.map (fun y-> y::x) h) r))
        (List.filter (fun x->x<>[])
           (List.map (linear_merge new_env entl_specs) entl)) [[]]
    in
    let entl0 = 
      List.map (List.map (fun (f,(p,c,q,r,s,l)) -> (f,(p,cmd_copy c,q,r,s,l)))) entl0 in
    if !verbose >= 1 then pp "@.LINEAR: We have %d case(s) to consider.@." (List.length entl0);
    let linear_iter = ref 0 in
    List.exists
      (fun entl_new ->
         incr linear_iter;
         if !verbose >= 1 then pp "@.====== [ Linearizability prover: iteration %2d ] ============================@."
           !linear_iter;
         linear_check_assignment env.g_guarantee new_env ril entl_new qs
      ) entl0
  end
	

(* -------------------------------------------------------------------------- *)
(** {2 Entry point } *)
(* -------------------------------------------------------------------------- *)
(** globals, fun_specifications, resources, res_initializers, fun_proofs with type as:
  comments: string list *
  fields: Misc.StringSet.t *
  globals: Exp.IdSet.t *
  fun_ht: (string, fun_info) Hashtbl.t *  
  res_ht: (Misc.component, act list) Hashtbl.t * 
  ril: (Misc.component * res_init) list * 
  entl: (string * can_entailment) list
*)
let check_props prover abstraction (comments,fields,globals,fun_ht,res_ht,rdefs,ril,entl,tdesc) 
									qscfl pures =
  let entl = if !left_mover_opt then left_mover_optimization entl else entl in
  all_fields := fields;
  if Genarith.enabled () then begin
    pp "#define assm(e) if (!(e)) {while(1){TerminationIgnore();}}@.@.";
    List.iter (pp "%s@.") comments;
  end;
	(** MCPA major update: ignoring injected init function *)
	let (_, entl) = 
		let re = Str.regexp "init" in
		List.partition (fun (s, _) -> Str.string_match re s 0) entl in
  let (entl_specs,entl) = (* Ignore any functions starting with ABS_ *)
    let re = Str.regexp "ABS_" in
    List.partition (fun (s,_) -> Str.string_match re s 0) entl 
  in
  let env = 
    { g_prover = prover
    ; g_abstraction = abstraction
    ; g_globals = globals
    ; g_fun_ht = fun_ht
    ; g_res_ht = res_ht
    ; g_renv = Hashtbl.create 15
    ; g_guarantee = []
    ; g_guar_changed = false
    ; g_params = IdSet.empty
    ; g_no_interf_hack = false
    ; g_linear_pre = None
		; cand_lin_point = Hashtbl.create 15
		; non_eff_postconditions = Hashtbl.create 15
		; rdefs = rdefs
		; spec_pool = ref []
		; hp_launch = Hashtbl.create 15
		; seq_table = Hashtbl.create 15
    } in
	(** MCPA major update: qualifiers give idea of the shape of the resources *)
	let rs = List.remove_duplicates (List.fold_left (fun rs (_,(_,c,_,_,_,_)) -> 
			rs @ Commands.cmd_lookup_rgnl c
		) [] entl) in
	let qs = Hashtbl.create 16 in
	let _ = List.iter (fun r -> 
		if (String.compare (string_of_component r) "r" = 0) 
		then (Hashtbl.replace qs r qscfl)) rs in
	
	let _ = match tdesc with 
		| Some tdesc -> Specpool.parse_thread_descriptor tdesc 
		| _ -> Misc.pp "No thread descriptor architector@." in	
		
  let res = if !infer >= 1 then begin
    check_with_inference env ril entl qs
  end else 
    check_no_inference env ril entl qs in
	(** This version of MCPA does not differient with CAVE *)
  let res = res && (!infer < 2 || check_linearizable env ril entl entl_specs qs) in
  if Genarith.enabled () then begin
    pp "int main() {@.";
    List.map fst entl
    |> List.filter (fun x -> not (str_is_cutpoint x) && not (str_is_fair x))
    |> List.iter (pp "  if (nondet()) %s(); else@.");
    pp "  {}@.}@.@.";
  end;
  res

