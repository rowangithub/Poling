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
(** Representation of commands *)
open Misc
open Exp
open Assertions

type can_goto = Cgo_break | Cgo_continue | Cgo_return

type fld_assignments = (exp * component * exp) list

type can_stmt =
  { can_st_desc: can_st_desc;
    mutable can_st_lv: IdSet.t;
    can_st_loc: Location.t; }

and can_cmd = can_stmt list

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
  | Cst_goto of can_goto
  | Cst_comment of string

type can_entailment =
  cprop * can_cmd * can_cmd * cprop * IdSet.t * Location.t

type fun_info =
    { fun_param: Id.t list * Id.t list;
      fun_modif: IdSet.t;
      fun_pre: cprop;
      fun_post: cprop;
      fun_loc: Location.t;
			fun_purespec: (string * Predicate.t);
			fun_effspec: (string * Predicate.t);
			fun_returns: (Location.t, Predicate.t) Hashtbl.t;
			fun_lbs : (Id.t * string) list }

type res_init = 
  | Cri_inv of cprop * Location.t
  | Cri_code of IdSet.t * can_cmd * Location.t

let node_component   = component_of_string "Node"
let ident_ABS        = Id.create "ABS"
let ident_ABS_value  = Id.create "ABS_value"
let ident_lin_res    = Id.create "$lres"

(* -------------------------------------------------------------------------- *)
(** {2 Pretty printing} *)
(* -------------------------------------------------------------------------- *)

let rec pp_seq pp f = function
  | [] -> ()
  | [x] -> pp f x
  | x::l -> pp f x; Format.pp_print_char f ','; pp_seq pp f l

let pp_rgnl f = function
  | [] -> ()
  | l -> 
      Format.fprintf f " [%a]" 
	(pp_seq (fun f x -> Format.pp_print_string f (string_of_component x)))
	l

let rec pp_stmt f st = 
  let go f st = match st.can_st_desc with
  | Cst_nondet (c1,c2) ->
      Format.fprintf f "@[nondet@;  %a@;or@;  %a@]"
      pp_cmd c1 pp_cmd c2
  | Cst_kill ids ->
      Format.fprintf f "kill(%a);" pp_idset ids
  | Cst_assign (x,e) ->
      Format.fprintf f "%a=%a;" pp_ident x pp_exp e
  | Cst_fldlookup (rgnl,x,e,t) ->
      Format.fprintf f "%a=%a->%s;" pp_ident x pp_exp e 
        (string_of_component t);
      pp_rgnl f rgnl
  | Cst_fldassign (rgnl,l,_) ->
      List.iter 
	(fun (e1,t,e2) ->
	   Format.fprintf f "%a->%s=%a;"
	     pp_exp e1 (string_of_component t) pp_exp e2)
	l;
      pp_rgnl f rgnl
  | Cst_new (x,e) ->
      Format.fprintf f "%a=new(%a);" pp_ident x pp_exp e
  | Cst_dispose (e1,e2) ->
      Format.fprintf f "dispose(%a,%a);" pp_exp e1 pp_exp e2
  | Cst_pfcall [(None,s,vl,el)] ->
      Format.fprintf f "%s(@[<hov 2>%a;@ %a@]);" s 
	(pp_seq pp_ident) vl (pp_seq pp_exp) el
  | Cst_pfcall [(Some v,s,vl,el)] ->
      Format.fprintf f "%a = %s(@[<hov 2>%a;@ %a@]);" pp_ident v s 
	(pp_seq pp_ident) vl (pp_seq pp_exp) el
  | Cst_pfcall xl ->
      Format.fprintf f "[@par@;  %a@]" pp_cmd 
	(List.map (fun x -> {can_st_desc = Cst_pfcall [x]; 
			     can_st_lv = st.can_st_lv;
			     can_st_loc = st.can_st_loc}) xl)
  | Cst_fcall2 (modif,cp1,cp2,s) ->
      Format.fprintf f "fcall(@[<hv>{%a},@[<hov 2>%a@],@ @[<hov 2>%a@]@]);"
      pp_idset modif pp_cprop cp1 pp_cprop cp2
  | Cst_assume (cp) ->
      Format.fprintf f "assume(%a);" pp_cprop cp
  | Cst_assume_exp (e) ->
      Format.fprintf f "assume(%a);" pp_exp e
  | Cst_assert_exp (e) ->
      Format.fprintf f "assert(%a);" pp_exp e
  | Cst_interfere (rid,actid) ->
      Format.fprintf f "interfere(%s.%s);" (string_of_component rid) actid
  | Cst_stabilize rid ->
      Format.fprintf f "stabilize(%s);" (string_of_component rid)
  | Cst_action_begin(_rid,cr,cp,cq,modif) ->
      Format.fprintf f "@[<hv 2>action_begin(%a@ | %a@ --> %a)@];"
	pp_cprop cr pp_cprop cp pp_cprop cq
  | Cst_action_end _ -> Format.fprintf f "action_end;"
  | Cst_loop (c,None) ->
      Format.fprintf f "@[<hv 2>loop@ %a@]" pp_cmd c 
  | Cst_loop (c,Some cp) ->
      Format.fprintf f "@[<v 2>loop@ @[invariant:@ %a@]@ %a@]"
        pp_cprop cp pp_cmd c 
  | Cst_goto (Cgo_break)    -> Format.pp_print_string f "break;"
  | Cst_goto (Cgo_continue) -> Format.pp_print_string f "continue;"
  | Cst_goto (Cgo_return)   -> Format.pp_print_string f "return;"
  | Cst_comment s -> Format.fprintf f "comment(%s);" s
  in
  (* Format.fprintf f "[LV: %a]@;%a" pp_idset st.can_st_lv go st *)
  go f st

and pp_cmd f sl =
  let rec go f = function 
  | [] -> Format.pp_print_string f "skip;"
  | [x] -> pp_stmt f x
  | x::l -> pp_stmt f x; Format.fprintf f "@;"; go f l
  in
    Format.fprintf f "@[<v>%a@]" go sl

let rec pp_linear_annot f c =
  List.iter (fun c -> match c.can_st_desc with
    | Cst_nondet(c1,c2) -> 
        pp_linear_annot f c1;
        pp_linear_annot f c2 
    | Cst_loop (c1,_) ->
        pp_linear_annot f c1
    | Cst_fldassign (rgnl,l,_) ->
        if List.exists (fun (e,_,_) -> e == E.id ident_ABS) l then
          Format.fprintf f "LP %s: %a@."
            (Location.lineno_to_string c.can_st_loc) pp_cmd [c]
    | _ -> ()) c

(* -------------------------------------------------------------------------- *)
(** {2 Live variable analysis} *)
(* -------------------------------------------------------------------------- *)

type lv_info = 
  { lv_next: IdSet.t 
  ; lv_break: IdSet.t 
  ; lv_cont: IdSet.t 
  ; lv_return: IdSet.t }

let (++) = IdSet.union
let (--) = IdSet.diff

(** [clear_live_vars c] updates all the live variable annotations to
    [IdSet.empty]. *)
let rec clear_live_vars c = 
  List.iter
    (fun c ->
       c.can_st_lv <- IdSet.empty;
       match c.can_st_desc with
         | Cst_nondet (c1,c2) -> clear_live_vars c1; clear_live_vars c2
         | Cst_loop (c1,_cpo) -> clear_live_vars c1
         | _ -> ())
    c

(** [mark_live_vars lv_post c] annotates the live variables before each program
    point. *)
let mark_live_vars lv_post c = 
  let lv_post = {lv_next=lv_post; lv_break=IdSet.empty;
                 lv_cont=IdSet.empty; lv_return=lv_post} in
  let changed = ref false in
  let (+) x y = IdSet.add y x in
  let (-) x y = IdSet.remove y x in
  let (---) x o = match o with None -> x | Some y -> x - y in
  let rec go c0 lv =
    let set lv_add =
      let lv_add = lv_add ++ (IdSet.singleton Id.tid) in
      if IdSet.for_all (fun e -> IdSet.mem e c0.can_st_lv) lv_add 
      then ()
      else (changed := true; c0.can_st_lv <- c0.can_st_lv ++ lv_add); 
            {lv with lv_next = c0.can_st_lv} in
    match c0.can_st_desc with
      | Cst_nondet(c1,c2)        -> set((go_cmd c1 lv).lv_next ++ (go_cmd c2 lv).lv_next)
      | Cst_kill(ids)            -> set(lv.lv_next -- ids)
      | Cst_assign(id,e)
      | Cst_new(id,e)           
      | Cst_fldlookup(_,id,e,_)  -> set(E.fv e (lv.lv_next - id))
      | Cst_fldassign(_,l,_) ->
	  set(List.fold
		(fun (e1,_,e2) lv -> E.fv e1 (E.fv e2 lv))
		l lv.lv_next)
      | Cst_dispose(e1,e2)       -> set(E.fv e1 (E.fv e2 lv.lv_next))
      | Cst_pfcall par_calls     ->
	  set(List.fold
		(fun (_,_,vl,el) lv -> List.fold E.fv el (List.fold_left (+) lv vl))
		par_calls
		(List.fold (fun (ido,_,_,_) lv -> lv --- ido) par_calls lv.lv_next))
      | Cst_fcall2(modf,cp,cq,s) -> set(prop_fv cp (lv.lv_next -- modf))
      | Cst_assume (cp)          -> set(prop_fv cp lv.lv_next)
      | Cst_assume_exp (e) 
      | Cst_assert_exp (e)       -> set(E.fv e lv.lv_next)
      |	Cst_interfere _
      |	Cst_stabilize _          -> set(lv.lv_next);
      | Cst_action_begin(_,cr,cp,cq,_)-> set(lv.lv_next ++ fv_norm_cprop cp ++ fv_norm_cprop cr)
      |	Cst_action_end (_,fv)        -> set(lv.lv_next ++ fv)
      | Cst_loop (c1,cpo)       ->
	  let fv = match cpo with None -> IdSet.empty | Some cp -> fv_norm_cprop cp in
	  let lv' =
	    let x = c0.can_st_lv ++ fv in 
            { lv_next = x; lv_break = lv.lv_next;
	      lv_cont = x; lv_return = lv.lv_return } in
	  set((go_cmd c1 lv').lv_next ++ fv)
      | Cst_goto (Cgo_break)     -> set (lv.lv_break)
      | Cst_goto (Cgo_continue)  -> set (lv.lv_cont)
      | Cst_goto (Cgo_return)    -> set (lv.lv_return)
      | Cst_comment _            -> set (lv.lv_next)
  and go_cmd c cfg = List.fold_right go c cfg in
  let rec fix () = 
    changed := false;
    let _ = go_cmd c lv_post in
    if !changed then fix () else () in
  clear_live_vars c;
  fix ()

let insert_kill_dead_vars c lv_post = c
(*
  let rec go c lv = match c with
    | [] -> ([], lv)
    | c0 :: c ->
	let (c, lv) = go c lv in
	let c = match c0.can_st_desc with
	  | Cst_nondet _ 
	  | Cst_goto _ -> c
	  | _ ->
	      let kill = c0.can_st_lv -- lv in
	      if IdSet.is_empty kill then c
	      else { can_st_desc = Cst_kill IdSet.empty (* kill *) ;
                     can_st_lv = lv; can_st_loc = c0.can_st_loc } :: c in
	let c = match c0.can_st_desc with
	   | Cst_nondet(c1,c2) -> 
	       let (c1, _) = go c1 lv in
	       let (c2, _) = go c2 lv in
	       { c0 with can_st_desc = Cst_nondet(c1,c2) } :: c
	   | Cst_loop (c1,cpo)       ->
	       let (c1, _) = go c1 (c0.can_st_lv ++ lv) in
	       { c0 with can_st_desc = Cst_loop (c1,cpo) } :: c
	   | _ -> c0 :: c in
	(c, c0.can_st_lv) in
  fst (go c lv_post)
*)

(* -------------------------------------------------------------------------- *)
(** {2 Loop unrolling} *)
(* -------------------------------------------------------------------------- *)

let mkst desc loc lv =
  { can_st_desc = desc
  ; can_st_loc = loc
  ; can_st_lv = lv }

let mk_cmd desc loc =
  [mkst desc loc IdSet.empty]
 
let mk_nondet c1 c2 loc lv = match c1, c2 with
  | {can_st_desc=Cst_assume []}::_, _
  | {can_st_desc=Cst_assume_exp (Enum 0)}::_, _ -> c2
  | _, {can_st_desc=Cst_assume []}::_
  | _, {can_st_desc=Cst_assume_exp (Enum 0)}::_ -> c1
  | _ -> [mkst (Cst_nondet (c1, c2)) loc lv]

let mk_loop c1 cpo loc lv = match c1 with
  | {can_st_desc=Cst_assume []}::_ -> c1
  | {can_st_desc=Cst_assume_exp (Enum 0)}::_ -> c1
  | {can_st_desc=Cst_goto Cgo_break}::_ -> []
  | _ -> [mkst (Cst_loop (c1, cpo)) loc lv]

let mk_assume e loc = 
   match e with 
   | Enum n when n <> 0 -> []
   | _ ->  mk_cmd (Cst_assume_exp e) loc

let rec clarify_stmt c0 c_next = match c0.can_st_desc with 
  | Cst_goto _ -> [c0]
  | Cst_nondet (c1,c2) ->
      mk_nondet (clarify_cmd c1) (clarify_cmd c2) c0.can_st_loc c0.can_st_lv
      @ c_next
  | Cst_loop (c1,cpo) ->
      mk_loop (clarify_cmd c1) cpo c0.can_st_loc c0.can_st_lv
      @ c_next
  | Cst_assume [] -> [c0]
  | Cst_assume [((p,[]),PNil)] ->
      if Pure.is_true p then c_next else c0 :: c_next
  | Cst_assume_exp (Enum n) -> if n == 0 then [c0] else c_next
  | Cst_assert_exp (Enum n) -> if n == 0 then [c0] else c_next
  | Cst_assume _ | Cst_assume_exp _ | Cst_assert_exp _
  | Cst_kill _ | Cst_assign _ | Cst_fldlookup _ 
  | Cst_fldassign _ | Cst_new _ | Cst_dispose _ | Cst_pfcall _ 
  | Cst_fcall2 _ | Cst_action_begin _ | Cst_action_end _ 
  | Cst_interfere _ | Cst_stabilize _ | Cst_comment _ -> c0 :: c_next

and clarify_cmd c = List.fold_right clarify_stmt c []

let mk_nondet_opt c1 c2 loc = match c1, c2 with
  | None, None -> None
  | None, Some _ -> c2
  | Some _, None -> c1
  | Some c1, Some c2 -> Some (mk_nondet c1 c2 loc IdSet.empty)

let mk_copy c = { c with can_st_lv = IdSet.empty }

let rec unfold_loop_inf can_break c0 c_next = match c0.can_st_desc with 
  | Cst_goto Cgo_return -> None
  | Cst_goto Cgo_break -> if can_break then Some [mk_copy c0] else None
  | Cst_goto Cgo_continue -> Some [mk_copy c0]
  | Cst_nondet (c1,c2) ->
      mk_nondet_opt
        (List.fold_right (unfold_loop_inf can_break) c1 c_next)
        (List.fold_right (unfold_loop_inf can_break) c2 c_next)
        c0.can_st_loc
  | Cst_kill _ | Cst_assign _ | Cst_fldlookup _ | Cst_assume _
  | Cst_assume_exp _ | Cst_assert_exp _ 
  | Cst_fldassign _ | Cst_new _ | Cst_dispose _ | Cst_pfcall _ 
  | Cst_fcall2 _ | Cst_action_begin _ | Cst_action_end _ 
  | Cst_interfere _ | Cst_stabilize _ | Cst_comment _ ->
      begin match c_next with 
        | None -> None 
        | Some c -> Some (mk_copy c0 :: c)
      end
  | Cst_loop (c1,cpo) ->
      begin match List.fold_right (unfold_loop_exit c_next) c1 None with
      | None -> 
        begin match List.fold_right (unfold_loop_inf false) c1 (Some []) with
        | None -> None
        | Some c1 -> Some (mk_loop c1 cpo c0.can_st_loc IdSet.empty)
        end
      | Some k ->
        begin match List.fold_right (unfold_loop_inf true) c1 (Some []) with
        | None -> None
        | Some c1 -> Some (mk_loop c1 cpo c0.can_st_loc IdSet.empty @ k)
        end
      end

and unfold_loop_exit c_break c0 c_next = match c0.can_st_desc with 
  | Cst_goto Cgo_return -> Some [mk_copy c0]
  | Cst_goto Cgo_break -> c_break
  | Cst_goto Cgo_continue -> None
  | Cst_nondet (c1,c2) ->
      mk_nondet_opt 
        (List.fold_right (unfold_loop_exit c_break) c1 c_next)
        (List.fold_right (unfold_loop_exit c_break) c2 c_next)
        c0.can_st_loc
  | Cst_kill _ | Cst_assign _ | Cst_fldlookup _ | Cst_assume _ 
  | Cst_assume_exp _ | Cst_assert_exp _ 
  | Cst_fldassign _ | Cst_new _ | Cst_dispose _ | Cst_pfcall _ 
  | Cst_fcall2 _ | Cst_action_begin _ | Cst_action_end _ 
  | Cst_interfere _ | Cst_stabilize _ | Cst_comment _ ->
     begin match c_next with 
       | None -> None
       | Some c -> Some (mk_copy c0 :: c) 
     end
  | Cst_loop (c1,cpo) ->
     List.fold_right (unfold_loop_exit c_next) c1 None >>= fun k ->
     begin match List.fold_right (unfold_loop_inf false) c1 (Some []) with
       | None -> Some k
       | Some c1 -> 
           let br = mkst (Cst_goto Cgo_break) c0.can_st_loc IdSet.empty in
           let nd = mk_nondet [br] c1 c0.can_st_loc IdSet.empty in
           let lp = mk_loop nd cpo c0.can_st_loc IdSet.empty in
           Some (lp @ k)
     end

(** Unroll the last iteration of all the loops in [c] *)
let unfold_loops c = 
  match List.fold_right (unfold_loop_exit None(*anything*)) c (Some []) with
  | None -> mk_assume E.zero Location.none
  | Some c -> c

(* -------------------------------------------------------------------------- *)
(** {2 Linearizability stuff} *)
(* -------------------------------------------------------------------------- *)

(** Specifications for checking that the linearization point occured
    at most once. *)
let (linear_fun_pre, linear_fun_post) = 
  let exp_RES = E.id Id.result in
  let exp_LRES = E.id ident_lin_res in
  let cp = cprop_pure (Pure.one (E.eq exp_LRES E.undef)) in
  let cq = cprop_pure (Pure.one (E.eq exp_LRES exp_RES)) in
  let cr = Pure.one (E.fun1 Sfn_can_return exp_RES) in
  (cp, cprop_or (and_cprop_pure cp cr) cq)

let linear_abs_pre =
  [Csp_node(tag_default, node_component, E.id ident_ABS,
            Fld.one Misc.list_data_tag (E.id ident_ABS_value))]


let rec cmd_to_dnf c0 res = match c0.can_st_desc with 
  | Cst_goto Cgo_return -> [[]]
  | Cst_comment _ 
  | Cst_kill _ | Cst_assign _ | Cst_fldlookup _ | Cst_assume _ 
  | Cst_assume_exp _ 
  | Cst_fldassign _ ->
      begin match res with 
        | [c] -> [c0 :: c]
        | _   -> List.map (fun c -> mk_copy c0 :: c) res
      end
  | Cst_nondet (c1,c2) ->
      List.fold_right cmd_to_dnf c1 res
      @ List.fold_right cmd_to_dnf c2 res
  | Cst_assert_exp _ 
  | Cst_new _ | Cst_dispose _
  | Cst_pfcall _ | Cst_fcall2 _ | Cst_action_begin _ | Cst_action_end _ 
  | Cst_interfere _  | Cst_goto _ | Cst_stabilize _ | Cst_loop _ ->
      print_endline ("\n" ^ Location.sprint c0.can_st_loc ^ 
                     "This command is not allowed in a linearizability specification.");
      invalid_arg ("Errors found in input.")


(** Check that a linearizability specification contains no loops
    and return its effectful & pure execution paths *)
let linear_parse_spec c =
  let cl = List.fold_right cmd_to_dnf c [[]] in
  let effectful c = match c.can_st_desc with
    | Cst_loop _ | Cst_fldassign _ | Cst_goto _ -> true
    | Cst_nondet _ -> assert false (* These have been eliminated by previous pass *)
    | _ -> false in
  let (effl, purel) = List.partition (List.exists effectful) cl in
  let effl_as_pure = List.map (fun l ->
       List.map (fun c0 -> { c0 with can_st_desc = c0.can_st_desc }) 
         (List.filter (fun c0 -> match c0.can_st_desc with 
           | Cst_fldlookup _ | Cst_assume _ | Cst_assume_exp _ -> true
           | _ -> false) l)) effl in
  let effl = List.map (fun cl -> 
    mkst (Cst_fcall2 (IdSet.empty, linear_fun_pre, cprop_empty, "LIN.POINT"))
      Location.none IdSet.empty
    :: List.map (fun c0 -> match c0.can_st_desc with 
       | Cst_assign (id, e) when id == Id.result ->
           { c0 with can_st_desc = Cst_assign (ident_lin_res, e) } 
       | Cst_assume p -> { c0 with can_st_desc = Cst_fcall2 (IdSet.empty, p, cprop_empty, "LIN.ASSUME") }
       | Cst_assume_exp e -> { c0 with can_st_desc = Cst_assert_exp (e) } 
       | _ -> c0) cl) effl in
  let purel = List.map (List.map 
    (fun c0 -> match c0.can_st_desc with 
       | Cst_assign (id, e) when id == Id.result ->
           { c0 with can_st_desc = Cst_assume_exp (E.fun1 Sfn_can_return e) }
(*           let eq = Pure.one (E.fun1 Sfn_can_return e) in
           { c0 with can_st_desc = Cst_assume (cprop_pure eq) } *)
       | _ -> c0)) purel in
  let purel = purel @ effl_as_pure in
(*  let pure_assn = List.fold (fun l r -> can_prop_star 
     (List.fold (fun c0 r -> match c0.can_st_desc with
         | Cst_assume p -> can_prop_neg p star p r
         | _ -> r) l can_prop_empty) *)
  (effl, purel)

(** Make a deep copy of a command (preserve lv) *)
let rec cmd_copy c = 
  let go c res = match c.can_st_desc with
    | Cst_nondet (c1,c2) ->
        { c with can_st_desc = Cst_nondet (cmd_copy c1, cmd_copy c2) } :: res
    | Cst_loop (c0,cpo) ->
        { c with can_st_desc = Cst_loop (cmd_copy c0, cpo) } :: res
    | Cst_fldassign (rgnl,l,r) ->
        { c with can_st_desc = Cst_fldassign (rgnl, l, ref !r) } :: res
    | d ->
        { c with can_st_desc = d } :: res in
  List.fold_right go c []

let rec stmt_lookup_rgnl c =
	match c.can_st_desc with
		| Cst_fldlookup (rgnl,x,e,t) -> rgnl
    | Cst_fldassign (rgnl,l,r) -> rgnl
    | Cst_nondet (c1,c2) -> cmd_lookup_rgnl c1 @ cmd_lookup_rgnl c2
    | Cst_loop (c0,cpo) -> cmd_lookup_rgnl c0
    | x -> []
			 
and cmd_lookup_rgnl c =
  List.remove_duplicates (List.flatten (List.map (stmt_lookup_rgnl) c))

(** MCPA major update 
Look up all resources  *)	
let rec stmt_add_rgnl rgnl' loc' c =
  { can_st_desc = 
      (match c.can_st_desc with
       | Cst_fldlookup (rgnl,x,e,t) -> Cst_fldlookup (rgnl' @ rgnl,x,e,t)
       | Cst_fldassign (rgnl,l,r) -> Cst_fldassign (rgnl' @ rgnl,l,r)
       | Cst_nondet (c1,c2) -> Cst_nondet (cmd_add_rgnl rgnl' loc' c1, 
                                           cmd_add_rgnl rgnl' loc' c2)
       | Cst_loop (c0,cpo) -> Cst_loop (cmd_add_rgnl rgnl' loc' c0, cpo)
       | x -> x);
    can_st_lv = IdSet.empty;
    can_st_loc = loc' }

and cmd_add_rgnl rgnl' loc' c =
  List.map (stmt_add_rgnl rgnl' loc') c
 

(** Copy [c] and insert [pure_code] before every atomic_block exit *)
let rec insert_pure_code pure_code c = 
  let go c res = match c.can_st_desc with
    | Cst_nondet (c1,c2) ->
        mk_cmd (Cst_nondet (insert_pure_code pure_code c1,
                            insert_pure_code pure_code c2)) c.can_st_loc @ res
    | Cst_loop (c0,cpo) ->
        mk_cmd (Cst_loop (insert_pure_code pure_code c0, cpo)) c.can_st_loc @ res
    | Cst_stabilize s ->
        { c with can_st_lv = IdSet.empty }
        :: List.rev_append (cmd_add_rgnl [s] c.can_st_loc pure_code) res
    | Cst_fldassign (rgnl,l,r) ->
        mk_cmd (Cst_fldassign (rgnl, l, ref !r)) c.can_st_loc @ res
    | _ -> { c with can_st_lv = IdSet.empty } :: res in
  List.rev (List.reduce go c)

let actlr_iter f = 
  let rec go c = match c.can_st_desc with
    | Cst_fldassign (_,_,r) -> List.iter f !r
    | Cst_nondet(c1,c2) -> List.iter go c1; List.iter go c2
    | Cst_loop (c,_) -> List.iter go c
    | _ -> () in
  List.iter (fun (_fname,(_,c,_,_,_,_)) -> List.iter go c)

let actlr_clear =
  let rec go c = match c.can_st_desc with
    | Cst_fldassign (_,_,r) -> r := []
    | Cst_nondet(c1,c2) -> List.iter go c1; List.iter go c2
    | Cst_loop (c,_) -> List.iter go c
    | _ -> () in
  List.iter (fun (_fname,(_,c,_,_,_,_)) -> List.iter go c)

let actlr_print =
  let rec go c = match c.can_st_desc with
    | Cst_fldassign (_,_,r) ->
        List.iter 
          (fun (s,cp) -> pp
             "@[Line %s, action: %s@ [%a]@]@."
             (Location.lineno_to_string c.can_st_loc)
             s pp_cprop cp)
          !r
    | Cst_nondet(c1,c2) -> List.iter go c1; List.iter go c2
    | Cst_loop (c,_) -> List.iter go c
    | _ -> () in
  List.iter (fun (_fname,(_,c,_,_,_,_)) -> List.iter go c)

(** Inline abs.specs at linearization points. *)
let actlr_merge_linear
  symbexe actlr_upd (spec : can_cmd) (fname,(pre,c,_,post,res_fv,loc)) =
  (* Combine field assignment [(l,r)] with command [c]. *)
  let rec concat_assn l r c = match c with
    | [] -> assert false (* should never happen as [c] is an effectful branch *)
    | ({can_st_desc = Cst_fldassign (rgnl,l',_)} as c0) :: c ->
        {c0 with can_st_desc = Cst_fldassign(rgnl, l @ l', ref r)} :: c
    | c0 :: c -> c0 :: concat_assn l r c in
  let rec go eff_spec abs_post c = match c.can_st_desc with
    | Cst_fldassign (rgnl,l,r) -> 
	begin match !r with 
	  | []   -> []
	  | _::_ -> 
	      try
		let rnew =
                   List.map (fun (s,cp) -> (s,actlr_upd abs_post cp)) !r in
                [concat_assn l rnew (cmd_add_rgnl rgnl c.can_st_loc eff_spec)]
	      with Not_found -> []
	end
    | Cst_nondet(c1,c2) -> 
				List.map
				  (fun c1 -> mk_nondet c1 c2 c.can_st_loc IdSet.empty) 
				  (go_list eff_spec abs_post c1)
				@ List.map
				  (fun c2 -> mk_nondet c1 c2 c.can_st_loc IdSet.empty)
				  (go_list eff_spec abs_post c2)
    | Cst_loop (c0,po) ->
			List.map 
	  		(fun c0 -> mk_loop c0 po c.can_st_loc IdSet.empty)
	  		(go_list eff_spec abs_post c0)
    | _ -> [] 
  and go_list eff_spec abs_post = function
    | [] -> []
    | c0 :: c ->
			List.map (fun c0 -> c0 @ c) (go eff_spec abs_post c0)
			@ List.map (fun c -> c0 :: c) (go_list eff_spec abs_post c)
  in
  let (eff_specs, pure_specs) = linear_parse_spec spec in
  let pure_code =
    match pure_specs with
    | [] -> []
    | c::cl ->
        List.fold (fun c1 c2 -> mk_nondet c1 c2 Location.none IdSet.empty) cl c
  in
  let c = insert_pure_code pure_code c in
  let res = match eff_specs with
    | [] -> [c] 
    | [spec] ->
        go_list spec (symbexe (cprop_spred linear_abs_pre) spec) c
    | _::_::_ -> assert false in
  let res = match res with [] -> [c] | _ -> res in
  let pre = cprop_star linear_fun_pre pre in
  let post = cprop_star linear_fun_post post in
  let res_fv = IdSet.add ident_ABS res_fv in
  let res = (* Deep copy [res] to avoid aliasing problems *)
    List.map cmd_copy res in
  let _ = (* Recompute live variables *)
    List.iter (mark_live_vars (prop_fv post res_fv)) res
  in
  List.map (fun c -> (fname,(pre,c,pure_code,post,res_fv,loc))) res


(* -------------------------------------------------------------------------- *)
(** {2 Left-mover optimisation} *)
(* -------------------------------------------------------------------------- *)

let rec compute_fld_updates_in_regions c res = match c with 
  | [] -> res 
  | c0 :: c ->
      let res = match c0.can_st_desc with
        | Cst_nondet (c1, c2) -> 
            compute_fld_updates_in_regions c2
              (compute_fld_updates_in_regions c1 res)
        | Cst_loop (c0,_) ->
            compute_fld_updates_in_regions c0 res
        | Cst_fldassign ([],_,_) -> res
        | Cst_fldassign (_::_,l,_) ->
            List.fold
              (fun (_,t,_) res -> if List.memq t res then res else t::res)
              l res
        | Cst_kill _ | Cst_assign _ | Cst_fldlookup _ | Cst_new _
        | Cst_dispose _ | Cst_pfcall _ | Cst_fcall2 _ | Cst_assume _ 
        | Cst_assume_exp _ | Cst_assert_exp _
        | Cst_interfere _ | Cst_stabilize _ | Cst_action_begin _ 
        | Cst_action_end _ | Cst_goto _ | Cst_comment _ -> res
      in
      compute_fld_updates_in_regions c res

let rec cmd_lm_optimize flds c = match c with
  | [] -> []
  | ({can_st_desc = Cst_stabilize rid} as c0) :: c1 ->
      begin match c1 with
        | [] -> [c0]
        | {can_st_desc = Cst_stabilize rid'} :: _ when rid' == rid ->
            cmd_lm_optimize flds c1
        | ({can_st_desc = Cst_fldlookup (rgnl,x,e,t)} as c2) :: c3 ->
            if List.memq rid rgnl && List.memq t flds then begin
              c0 :: c2 :: cmd_lm_optimize flds c3
            end else begin
              c0.can_st_lv <- c2.can_st_lv;
              c2 :: cmd_lm_optimize flds (c0 :: c3)
            end
        | ({can_st_desc = Cst_fldassign (rgnl,_,_)} as c2) :: c3 ->
            if List.memq rid rgnl then
              c0 :: c2 :: cmd_lm_optimize flds c3
            else
              c2 :: cmd_lm_optimize flds (c0 :: c3)
        | ({can_st_desc = 
              Cst_assume _ | Cst_kill _ | Cst_assign _
            | Cst_assume_exp _ | Cst_assert_exp _
            | Cst_new _ | Cst_dispose _} as c2) :: c3 ->
              c2 :: cmd_lm_optimize flds (c0 :: c3)
        | _ ->
            c0 :: cmd_lm_optimize flds c1
      end
  | ({can_st_desc = Cst_loop (ca,cp0)} as c0) :: c1 ->
      {c0 with can_st_desc = Cst_loop (cmd_lm_optimize flds ca, cp0)} 
      :: cmd_lm_optimize flds c1
  | ({can_st_desc = Cst_nondet (ca,cb)} as c0) :: c1 ->
      {c0 with can_st_desc = Cst_nondet (cmd_lm_optimize flds ca,
                                         cmd_lm_optimize flds cb)} 
      :: cmd_lm_optimize flds c1
  | c0 :: c1 -> c0 :: cmd_lm_optimize flds c1

let left_mover_optimization (entl : (string * can_entailment) list) =
  let flds = 
    List.fold (fun (_,(_,c,_,_,_,_)) r -> compute_fld_updates_in_regions c r) entl [] in
  List.map (fun (s,(p,c,r,q,v,l)) -> (s,(p,cmd_lm_optimize flds c,r,q,v,l))) entl
 
