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

(** Abstraction (i.e. overapproximation) of assertions *)
open Misc
open Exp
open Assertions
open Genarith

(* -------------------------------------------------------------------------- *)
(** {2 Arguments & statistics} *)
(* -------------------------------------------------------------------------- *)

let value_abs = ref true
let verbose = ref 0

let args = 
 [ ("-value",        Arg.Set   value_abs, " Enable value abstraction (default)")
 ; ("-no_value",     Arg.Clear value_abs, " Disable value abstraction")
 ; ("-vAbstraction", Arg.Set_int verbose,
                     "<n> Display internal information (abstraction)")]

let pr s ufl =
  if !verbose > 0 then 
    List.iter (pp "%s %a@." s pp_uform) ufl

(** number of calls to the theorem prover during abstraction *)
let prover_calls = ref 0

(* -------------------------------------------------------------------------- *)
(** {2 Helper routines} *)
(* -------------------------------------------------------------------------- *)

exception Abstraction_error of string

let normal_ids = idpool_new Id.gensym_str    "!"
let bogus_ids  = idpool_new Id.gensym_str_ex "?"
let val_ids    = idpool_new Id.gensym_str_ex "?val"
let sval_ids   = idpool_new Id.gensym_str_ex "?sval"

let (@&) = Pure.conj_one

let normalize_uform_aggr (p, sl) res = 
  List.fold_append (fun p -> normalize_uform (p, sl)) 
    (Pure.normalize_aggr p) res

(** Find all expressions reachable from pointers [n] *)
let compute_reachable n sl = 
  let res = ref n in
  let changed = ref true in
  let add e = 
    if not (mem_exp e res.contents) then begin
      changed := true;
      res := e::res.contents
    end in
  while changed.contents do
    changed := false;
    List.iter 
      (fun sp -> match sp with
	 | Csp_node (_,_,e,fld) ->
	     if mem_exp e res.contents then Fld.iter_val add fld
	 | Csp_listsegi (_,SINGLE _,e,f,g,_,_,_) ->
	     if mem_exp e res.contents then (add f; add g)
	 | _ -> ()) 
      sl
  done;
  res.contents

(* -------------------------------------------------------------------------- *)
(** {2 Abstraction of sequences and sets} *)
(* -------------------------------------------------------------------------- *)

let do_tl_case_splits (p,sl) =
  let get_tl_exp e r = match e with
    | Efun1 (Sfn_tl, e1) -> if mem_exp e1 r then r else e1 :: r
    | _ -> r in
  let el = spat_fold (exp_fold get_tl_exp) sl [] in
  List.fold 
    (fun e r ->
       let hd_var = E.gensym_str_ex "HD" in
       let tl_var = E.gensym_str_ex "TL" in
       let exp_non_empty = E.list [E.item hd_var; tl_var] in
       List.map (fun (p,sl) -> (E.eq e E.empty_list @& p, sl)) r
       @ List.map (fun (p,sl) -> (E.eq e exp_non_empty @& p, sl)) r)
    el [(p,sl)]


(** Get a list of all `interesting' expressions in [(p,sl)] *)
let get_values aggressive sfun (p,sl) = 
  let go_exp e res = match e with 
    | Efun(s,el) when s == sfun -> el :: res
    | Efun1(Sfn_item, _) -> [e] :: res
    | e -> [e] :: [E.item e] :: res in 
  let go_fld t e res = 
    if t == list_data_tag then go_exp e res else res in
  (if aggressive then [] 
   else [[E.item (E.num (-12345))]; [E.item (E.num 12345)]])
  |> go_exp (Pure.to_sub p (E.id Commands.ident_lin_res))
  |> List.fold (fun s res -> match s with
	        | Csp_node(_,_,_,fld) -> Fld.fold go_fld fld res
	        | Csp_listsegi(_,SINGLE _,_,_,e,_,_,_) -> go_exp e res
	        | _ -> res) sl 

(** Get a list of all `interesting' expressions in [sl] *)
let get_plain_values = 
  let add x y = if mem_exp x y then y else x::y in
  let go_exp e res = match e with 
    | Efun((Sfn_set | Sfn_list), el) -> List.fold add el res
    | Efun1(Sfn_item, _) -> add e res
    | e -> add e (add (E.item e) res) in
  let go_fld t e res = 
    if t == list_data_tag then go_exp e res else res in
  List.fold (fun s res -> match s with
	       | Csp_node(_,_,_,fld) -> Fld.fold go_fld fld res
	       | Csp_listsegi(_,SINGLE _,_,_,e,_,_,_) -> go_exp e res
	       | _ -> res)

(** Apply a sequence substitution *)
let list_sub_exp sub =
  let sub = PList.fold (fun k v r -> (k,v)::r) sub [] in
  let all = List.sort (fun (x,_) (y,_) ->
                         compare (List.length x) (List.length y)) sub in
  let all_set = (* Used for substituting inside set expressions *)
    List.map (fun (x,y) ->
                (List.sort compare_exp (List.map (E.fun1 Sfn_set_of_list) x),
                 E.fun1 Sfn_set_of_list y)) all in
  let rec go_list m mem = function
    | [] -> List.rev mem
    | x::xs -> 
	let m = List.filter (function (z::_,_) -> equal_exp z x
                               | _ -> false) m in
	let m = List.map (fun (x,y) -> (List.tl x, y)) m in
	match m with 
	  | [] -> List.rev_append mem (x :: go_list all [] xs)
	  | ([],y)::_ -> y :: go_list all [] xs
	  | _ -> go_list m (x::mem) xs in
  let rec match_one = function
    | ([], ys) -> Some ys
    | (_::_, []) -> None
    | (x::xs, y::ys) ->
	if equal_exp x y then match_one (xs,ys)
	else match_one (x::xs,ys) >>= fun res -> Some (y::res) in
  let go_set el (x,y) = match match_one (x, el) with 
    | None -> el
    | Some el' -> List.merge compare_exp [y] el' in
  let rec go_exp e = match e with
    | Efun1 (i, e1) ->
	let e1' = go_exp e1 in 
	if e1' == e1 then e else E.fun1 i e1'
    | Efun2 (i, e1, e2) ->
	let e1' = go_exp e1 in 
	let e2' = go_exp e2 in 
	if e1' == e1 && e2' == e2 then e else E.fun2 i e1' e2'
    | Efun (Sfn_list, el) -> E.list (go_list all [] el)
    | Efun (Sfn_set, el) -> E.set (List.fold_left go_set el all_set)
    | Efun (i, el) -> E.funn i (List.map go_exp el)
    | Eeq (e1, e2) ->
        let e1' = go_exp e1 in
        let e2' = go_exp e2 in
	if e1'==e1 && e2'==e2 then e else E.eq e1' e2'
    | (Eident _ | Enum _ | Egrp _) -> e in
  go_exp

(** Apply a set substitution *)
let set_sub_exp sub e =
  let all = List.map (fun (x,y) -> (List.sort compare_exp x, y)) sub in
  let rec match_one = function
    | ([], ys) -> Some ys
    | (_::_, []) -> None
    | (x::xs, y::ys) ->
			if equal_exp x y then match_one (xs,ys)
			else match_one (x::xs,ys) >>= fun res -> Some (y::res) 
	in
  let go el (x,y) = match match_one (x, el) with 
    | None -> el
    | Some el' -> List.merge compare_exp [y] el' 
	in
  let rec go_exp e = match e with
    | Efun1 (Sfn_set_of_list, _) ->
				E.set (List.fold_left go [e] all)
    | Efun1 (i, e1) ->
				let e1' = go_exp e1 in 
				if e1' == e1 then e else E.fun1 i e1'
    | Efun2 (i, e1, e2) ->
				let e1' = go_exp e1 in 
				let e2' = go_exp e2 in 
				if e1' == e1 && e2' == e2 then e else E.fun2 i e1' e2'
    | Efun (Sfn_set,el) -> 
				let el = List.sort compare_exp el in
				E.set (List.fold_left go el all)
    | Efun (x,el) -> 
				E.funn x (List.map go_exp el)
    | Eeq (e1, e2) as e ->
        let e1' = go_exp e1 in
        let e2' = go_exp e2 in
				if e1'==e1 && e2'==e2 then e else E.eq e1' e2'
    | (Eident _ | Enum _ | Egrp _) -> e 
	in
  go_exp e

let abs_populate_pure xs ys p =
  let add_not_subset m (x,y) r =
    if Pure.entails_exp p (E.fun1 Sfn_NOT (E.fun2 Sfn_subset (E.item (E.id m)) (E.fun1 Sfn_set_of_list x))) 
    then E.fun1 Sfn_NOT (E.fun2 Sfn_subset (E.item (E.id m)) (E.fun1 Sfn_set_of_list y)) @& r 
    else r in
  let add_sorted (x,y) r =
    if Pure.entails_exp p (E.fun1 Sfn_sorted x)
    then E.fun1 Sfn_sorted y @& r 
    else r in
  let add_list_lt l x (m,y) r =
    if l != m && Pure.entails_exp p (E.fun2 Sfn_list_lt l m)
    then E.fun2 Sfn_list_lt x y @& r
    else r in
  let add_list_lt2 m (l,x) r =
    let r = 
      if Pure.entails_exp p (E.fun2 Sfn_list_lt l m)
      then E.fun2 Sfn_list_lt x m @& r
      else r in
    if Pure.entails_exp p (E.fun2 Sfn_list_lt m l)
    then E.fun2 Sfn_list_lt m x @& r
    else r in
  let xs = PList.fold (fun xs y r -> (E.list xs,y)::r) xs [] in
  p
  |> IdSet.fold (fun x -> List.fold (add_not_subset x) xs) (IdSet.filter (fun x -> not (Id.is_existential x)) (Pure.fv p IdSet.empty))
  |> List.fold add_sorted xs
  |> List.fold (fun (l,x) -> List.fold (add_list_lt l x) xs) xs
  |> List.fold (fun m -> List.fold (add_list_lt2 m) xs) ys

(** Abstract all values *)
let abs_all_values uf =
  let xxs = idpool_combine val_ids (get_values true Sfn_list uf) in
  uf
  |> map_uform (list_sub_exp xxs)
  |> List.map 
      (fun (p,sl) ->
	 (Pure.filter (fun x -> IdSet.is_empty (E.exfv x IdSet.empty)) p, sl))

(** Abstract list values *)
let mk_pre_abs_list_sub aggressive xs =
  let (@+) x y = match x with [] -> y | _ -> x::y in
  (** Break [ys] into two sublists if it contains [x]. *)
  let rec break1 x zs e ys = match ys with
    | [] -> (List.rev zs)::e
    | y::ys ->
	if equal_exp x y then
	  List.rev zs @+ ys @+ e
	else
	  break1 x (y::zs) e ys in
  let rec break2 x zs e ys0 = match ys0 with
    | [] -> (List.rev zs)::e
    | y::ys ->
	if equal_exp x y then
	  List.rev zs @+ ys0 @+ e
	else
	  break2 x (y::zs) e ys in
  let rec break3 zs ys e = match ys with
    | [] -> (List.rev zs) @+ e
    | Efun1(Sfn_item, y)::ys 
      when not aggressive && IdSet.is_empty (E.exfv y IdSet.empty) ->
	break3 [] ys (List.rev zs @+ e)
    | y::ys ->
	break3 (y::zs) ys e in
  let rec reduce n xs = 
    if n > List.length xs then xs 
    else match xs with
      | [] -> [] 
      | []::xs -> reduce n xs
      | [y]::xs ->
	 let xs = List.fold_left (break1 y []) [] (List.rev xs) in
	 reduce n xs
      | (y::ys as l)::xs -> 
	 let xs = List.fold_left (break2 y []) [l] (List.rev xs) in
	 reduce (n+1) xs in
  (* pp "List abstraction %d %d@." 
     (List.length xs) (List.fold (fun x e -> List.length x + e) xs 0);
     List.iter (fun el -> pp "____ %a@." pp_exp (E.list el)) xs; *)
  xs
  |> List.reduce (break3 [])
  |> reduce 0
  (* and the other way round... *)
  |> List.map List.rev 
  |> reduce 0 
  |> List.map List.rev
  |> idpool_combine val_ids
  (* |>> (fun xxs ->
	   pp "List abs result  %d@." (List.length xxs);
	   List.iter (fun (x,e) -> pp "____ %a = %a@." pp_exp (E.list x)
                                     pp_exp e) xxs) *)

let mk_abs_list_sub values = 
  list_sub_exp (mk_pre_abs_list_sub false values)

(** Abstract list values *)
let abs_list_values aggressive (p,sl) =
  let xxs =
    mk_pre_abs_list_sub aggressive (get_values aggressive Sfn_list (p,sl)) in
  let ys = 
    let (@+) x y = if mem_exp x y then y else x::y in
    let go_exp e r = match e with 
      | Efun1 (Sfn_item, i) when not (existential_id i) -> e @+ r
      | _ -> r in
    Pure.fold (exp_fold go_exp) p []
    |> get_plain_values sl
    |> List.filter (fun y -> not (PList.exists 
                      (fun l _ -> List.exists (equal_exp y) l) xxs))
  in
  (abs_populate_pure xxs ys p, sl)
  |> map_uform (list_sub_exp xxs)
  (* |> reduce normalize_uform_aggr *)
  |> List.map 
    (fun (p,sl) ->
       let fv = List.fold (spred_fold E.exfv) sl IdSet.empty in 
       (Pure.filter (fun x -> IdSet.subset (E.exfv x IdSet.empty) fv) p, sl))


let saturate_set_equalities ufl =
  let (&&&) = Pure.conj in
  let do_sub x y = 
    Pure.map (set_sub_exp [(x, E.set y)]) in
  let uf_sub = function
    | [] -> (fun x -> [x])
    | eqs ->
        map_uform
	  (set_sub_exp 
	    (List.map (fun (x,y) -> (x,E.set y)) eqs)) in
  let saturate (p,sl) =
    match Pure.get_set_eqs p with [] | [_] -> (p,sl) | eqs ->
      (List.fold (fun (x,y) p -> do_sub x y p &&& do_sub y x p &&& p) eqs p, sl) in
  ufl
  |> List.reduce_append (fun uf -> normalize_uform (saturate uf))
  |> List.reduce_append (fun uf -> uf_sub (Pure.get_set_eqs (fst uf)) uf)
  |> List.map 
      (fun (p,sl) ->
	 (Pure.filter (function
			 | Eeq (Efun(Sfn_set,_), Efun(Sfn_set,_)) -> false
			 | _ -> true) p, sl))


(** Return a substitution that abstracts the set values in [xs]. *)
let mk_abs_set_sub list_vars item_vars xs =
  (** [remove xs ys = if xs <= ys then ys - xs else ys] *)
  let remove xs ys = 
    let rec go acc xs ys0 = match xs with
      | [] -> List.rev_append acc ys0
      | x::xs1 -> 
				begin match ys0 with
	  			| [] -> ys
	  			| y::ys1 ->
	      		let n = compare_exp x y in
	      		if n = 0 then go acc xs1 ys1 
	      		else if n > 0 then go (y::acc) xs ys1 else ys
				end 
		in go [] xs ys 
	in
  let my_compare_list l1 l2 = 
    let n = compare (List.length l1) (List.length l2) 
		in if n <> 0 then n else compare_exp_list l1 l2 
	in
  let rec reduce acc xs = match xs with
    | [] -> acc
    | []::xs -> reduce acc xs
    | x::xs ->
			let xs = List.sort my_compare_list (List.map (remove x) xs) in
			begin match x with
	  		| [Efun1 (Sfn_set_of_list, Eident _)] -> reduce (x::acc) xs
	  		| [_] -> reduce acc xs 
	  		| _ -> reduce (x::acc) xs 
			end
  in
  (** Remove [@item(...)] and [@set_of_list(...)] subterms *)
  let my_filter = function
    | Efun1 (Sfn_item, e) ->
			existential_id e && not (IdSet.mem (Id.of_exp e) item_vars)
    | Efun1 (Sfn_set_of_list, (Eident _ as e)) ->
			not (IdSet.mem (Id.of_exp e) list_vars)
    | _ -> true 
	in
  let xxs =
    List.map (List.filter my_filter) xs
    |> List.sort my_compare_list
    |> reduce []
    |> idpool_combine sval_ids 
	in
  	PList.fold (fun x y r -> match x with 
		| [Efun1 (Sfn_item,_)] -> (x, E.item y)::r
		| _ -> (x,y)::r) xxs []
  	|> set_sub_exp

(** Abstract set values *)
let abs_set_values (p,sl) =
  let sub =
    let vars = List.fold spred_fv sl IdSet.empty in
    let item_vars = 
      spat_fold (fun e r -> match e with 
		   | Efun (Sfn_list, el) ->
		       List.fold (fun e r -> match e with 
				    | Efun1 (Sfn_item, (Eident _ as x)) ->
							IdSet.add (Id.of_exp x) r
				    | _ -> r) el r
		   | _ -> r)
			sl IdSet.empty 
		in
    mk_abs_set_sub vars item_vars (get_values false Sfn_set (p,sl)) 
	in
  map_uform sub (p,sl)

(* HACK *)
let mk_abs_set_sub list_vars xs = mk_abs_set_sub list_vars IdSet.empty xs

(** Convert to a normal form *)
let abs_fv_to_sub exfv =
  mk_subst (idpool_combine bogus_ids exfv)

(* -------------------------------------------------------------------------- *)
(** {2 Shape abstraction} *)
(* -------------------------------------------------------------------------- *)

let node_component = component_of_string "Node"

let is_maybe_link x =
  List.exists (fun y -> x==y) possible_link_fields.contents

let keep_numbers _c e = match e with
  | Enum _ -> true
  | _ -> false

(* Using the assumptions pl, if s is a singly-linked list segment
   with link field t and value field v, return
    (1) the type of node
    (2) the end of the list segment 
    (3) the value of the list segment
    (4) is the list possibly empty?
    (5) the set of expressions not contained in it
    (6) the list of other fields
 *)
let get_ends pl t v s = match s with
  | Csp_node(_,nid,e,fields) -> if not (is_maybe_link t) then None else 
      (try
	let f = Fld.get t fields in
	let fv = 
	  E.item (try Fld.get v fields
		   with Not_found -> E.gensym_str_ex "VAL") in
	let fields = Fld.remove t fields in
	let fields = Fld.filter keep_numbers fields in
	Some (nid,f,fv,Cem_NE,Pure.get_uneql e pl,fields)
      with Not_found ->
        None)
  | Csp_listsegi(_,SINGLE(snode,flds),_,f1,e2,_,isEmp,el) when snode==t ->
      Some (node_component,f1,e2,isEmp,el,flds)
  | _ -> None

(* Using the assumptions pl, if s is a singly-linked list segment
   ending at e0, return
    (1) the type of node
    (2) its start
    (3) its link field
    (4) its value
    (5) the list of other fields
    (6) is the list possibly empty?
    (7) the set of expressions not contained in it
 *)
let get_ends_with pl e0 s = match s with
  | Csp_node(_,nid,e,fields) -> 
			(* t is the link field *)
      let t = Fld.containing e0 fields in
      (* fv is the value *)
			let fv = 
	E.item (try Fld.get list_data_tag fields
		 with Not_found -> E.gensym_str_ex "VAL") in
      let fields = Fld.remove t fields in
      let fields = Fld.filter keep_numbers fields in
      (nid,e,t,fv,fields,Cem_NE,Pure.get_uneql e pl)
  | Csp_listsegi(_,SINGLE(snode,fields),e1,f1,e2,_,isEmp,el)
    when equal_exp f1 e0 ->
      (node_component,e1,snode,e2,fields,isEmp,el)
  | _ -> raise (Abstraction_error "ABS: Different field found")

let normal_uform prover uf =
  List.map fst (prover.nf_cform (uf,PNil))

let combine_isemp ie1 ie2 = match ie1 with
  | Cem_PE -> ie2
  | Cem_NE -> Cem_NE

let add_exist e el =
  if not (existential_id e) || mem_exp e el then el else e :: el

(** Find set of expressions reachable over a path *)
let my_reachable (e,xl) pure_sub sl res =
  let rec go res (e,xl) = match xl with
    | [] -> add_exist e res
    | x::xl -> List.fold_left 
	(fun res sp -> match sp with
	 | Csp_node (_,_,e0,fld) when equal_exp e e0 -> 
	     if Fld.hasfld x fld then
	       let e' = Fld.get x fld in
	       go (add_exist e' res) (e',xl)
	     else res
	 | _ -> res) res sl in
  go res (pure_sub e,xl) 

let heuristic_Q_tail_tl = 
  let spec = 
    (E.id (Id.create "Q"),
     [component_of_string ".tail";
      component_of_string ".tl";
      component_of_string ".tl"]) in
  my_reachable spec

let important_vars p sl =
  []
  |> heuristic_Q_tail_tl (Pure.to_sub p) sl
  |> List.fold 
      (fun s res ->
	 match s with
	   | Csp_node(_,_,e,fld) -> 
	       if Fld.exists (fun c e -> e == E.tid
                                      && is_lock_field c) fld
	       then add_exist e (Fld.fold_val add_exist fld res)
	       else res
	   | _ -> res) sl 

(** Applies the abstraction rules to [uf] to eliminate some existentials *)
let abs_uform prover aggressive uf =
  let start_of s = match s with
    | Csp_node(_,_,e,_) -> e
    | Csp_listsegi(_,SINGLE _,e,_,_,_,_,_) -> e
    | Csp_listsegi(_,_,_,_,_,_,_,_) ->
        raise  (Abstraction_error "ABS: Cannot use dllseg or xlseg")
    | Csp_arr (_,e,_,_,_,_,_) -> e
    | Csp_indpred _ ->
        raise (Abstraction_error "ABS: Cannot use inductive predicate") in
  let ends_with_exp e0 s = match s with
    | Csp_node(_,_,_,fields) -> Fld.exists (fun _ e -> equal_exp e0 e) fields
    | Csp_listsegi(_,SINGLE _,_,e,_,_,_,_) -> equal_exp e e0
    | Csp_listsegi(_,_,_,_,_,_,_,_) ->
        raise (Abstraction_error "ABS: Cannot use dllseg or xlseg")
    | Csp_arr _ -> false (*raise (Abstraction_error "ABS: Cannot use arr")*)
    | Csp_indpred _ ->
        raise (Abstraction_error "ABS: Cannot use inductive predicate") in
  let shape_abstract p sl = 
    let reach = important_vars p sl in
    let rec go changed sl2 sl1 = match sl1 with
      | [] -> if changed then go false [] sl2 else (p, sl2)
      | s::sl1 -> 
	  		let e_mid = start_of s in
	  		if not (existential_id e_mid) || mem_exp e_mid reach then
	    		go changed (s::sl2) sl1
	  		else
	    		let (sl1a,sl1b) = List.partition (ends_with_exp e_mid) sl1 in
	    		let (sl2a,sl2b) = List.partition (ends_with_exp e_mid) sl2 in
	    		begin match (sl1a@sl2a) with
	      		| [] -> if !allow_leaks then go changed sl2 sl1 else raise Junk
	      		| [s'] -> (* s' :: s is the new listsegment *)
		  				let (nid1,e,t,fv1,flds,ie1,el) = get_ends_with p e_mid s' in
		  				begin match get_ends p t list_data_tag s with
		    				| None -> go changed (s::sl2) sl1
		    				| Some (nid2,f,fv2,ie2,el',flds') ->
									if nid1 == nid2 then 
										begin
			  							let fv = E.list [fv1; fv2] in
			  							let ie = combine_isemp ie1 ie2 in
			  							let el'' = Dset.inter el el' in
			  							let flds'' = Fld.inter flds flds' in
                      let k = SINGLE(t,flds'') in
			  							go true sl2b (Csp_listsegi(tag_default,k,e,f,fv,E.zero,ie,el'')::sl1b)
										end 
									else
			  							go changed (s::sl2) sl1
		  				end
	      		| _::_::_ ->
		  				go changed (s::sl2) sl1
	    		end 
		in go false [] sl 
	in
  let first_pass sp sl = match sp with
  	| Csp_node(tag,nid,e,fld) ->
			let keep_fld c e = not (is_lock_field c)
	  		|| (match e with Enum _ -> true | _ -> e == E.tid) 
			in
				Csp_node(tag,nid,e,Fld.filter keep_fld fld) :: sl
    | sp -> sp :: sl 
	in
  let ufl =
    normal_uform prover uf
    |>  List.reduce normalize_uform_aggr (* Perform case splits *)
    |>> pr "ABS1" 
    |>  List.map (fun (p,sl) -> let sl = List.reduce first_pass sl in 
                                shape_abstract p sl)
		|>> pr "ABS2"
    |>  List.reduce_append do_tl_case_splits 
    |>  List.reduce normalize_uform_aggr (* More case splits... *)
    |>  (fun ufl -> if !value_abs then saturate_set_equalities ufl else ufl)
    |>  kill_garbage_vars_ufl 
    |>  List.reduce_append (normal_uform prover)
    |>> pr "ABS3" 
	in
  	if !value_abs then 
			begin
    		List.reduce_append (abs_list_values aggressive) ufl
    		|>> pr "ABS4"
    		|>  List.reduce_append abs_set_values 
    		|>> pr "ABS5"
  		end 
		else
    	List.reduce_append abs_all_values ufl


let abs_cform prover ((p,sl),scpl) : cform list = 
  let scpl = 
    let go ((p1,sl1),scpl) =       
      List.fold (fun uf res -> (uf,scpl)::res)
        (abs_uform prover false (Pure.conj p p1,sl1)) 
		in PList.map_val (List.reduce go) scpl 
	in
  let uf = (p,sl) in
  let uf = fst (List.hd (kill_garbage_vars ([(uf,scpl)]))) in
  List.map (fun uf -> (uf,scpl)) (abs_uform prover false uf)


(* -------------------------------------------------------------------------- *)
(** {2 Join for uform lists} *)
(* -------------------------------------------------------------------------- *)
(** These do not generate arithmetic programs. *)

let uf_to_nf uf r =
  let ufl = normalize_uform uf in
  List.fold (fun (p,sl) r -> 
    let sl = List.sort abs_compare_can_spred sl in
    let exfv = abs_fv_uform (p,sl) in
    let sub = abs_fv_to_sub exfv in
    match map_uform sub (p,sl) with ([]|_::_::_) -> assert false | [(p,sl)] ->
    let sl = List.sort compare_can_spred sl in
    (p,sl)::r) ufl r

(** Just abstract; do not attempt to remove redundant disjuncts *)
let uform_list_abs prover aggr ufl =
  ufl
  |> List.reduce_append (abs_uform prover aggr)
  |> List.reduce_append (normal_uform prover) 
  |> List.reduce uf_to_nf
  |> List.sort compare_uform 
  |> remove_uform_duplicates

(** Test whether [uf] adds any new information as a disjunct to [ufl] *)
let uform_adds_info1 ufl uf = 
  List.for_all (fun uf2 -> compare_uform uf uf2 <> 0) ufl

(** Test whether [uf] adds any new information as a disjunct to [ufl] *)
let uform_adds_info2 prover ufl uf = match ufl with 
  | [] -> true 
  | _ ->
      (* 2. Provably weaker disjunct does not already exist in ufl *)
      let cf = (uf,PNil) in
      let exfv = IdSet.elements (form_exfv cf IdSet.empty) in
      let cf = map_cform (mk_subst (idpool_combine normal_ids exfv)) cf in
      List.for_all
        (fun uf2 ->
           incr prover_calls;
           prover.entails_cprop cf [(uf2,PNil)] = [])
        ufl

(** @deprecated  *)
let uform_adds_info2a prover uf2 uf =
  let cf = (uf,PNil) in
  let exfv = IdSet.elements (form_exfv cf IdSet.empty) in
  let cf = map_cform (mk_subst (idpool_combine normal_ids exfv)) cf in
  incr prover_calls;
  prover.entails_cprop cf [(uf2,PNil)] = []


(** Test whether [uf] adds any new information as a disjunct to [ufl] *)
let uform_adds_info prover ufl uf = 
  uform_adds_info1 ufl uf && uform_adds_info2 prover ufl uf

(** @deprecated  *)
(** Count the number of |->, lsPE, and lsNE in formula. *)
let spat_count =
  let rec cou n_pt n_ne sl = match sl with
    | [] -> (n_pt,n_ne)
    | sp :: sl -> 
	begin match sp with
	| Csp_node _ -> cou (n_pt+1) n_ne sl
	| Csp_listsegi (_,_,_,_,Eident _,_,Cem_NE,_) -> cou n_pt (n_ne+1) sl
	| _ -> cou n_pt n_ne sl
	end
  in
  cou 0 0

(** @deprecated *)
let join1 prover uf (ufl, ufl_drop, ufl_new) = 
  let make_pe sp = match sp with
    | Csp_listsegi (tag,k,e1,f1,(Eident _ as e2),f2,Cem_NE,ds) -> 
	Csp_listsegi (tag,k,e1,f1,e2,f2,Cem_PE,ds)
    | sp -> sp in
  let (_pt1,_ne1) = spat_count (snd uf) in
  let rec join_list ufl_drop acc ufl = match ufl with
    | [] -> (List.rev acc, ufl_drop, uf :: ufl_new)
    | uf2 :: ufl ->
	let (_pt2,_ne2) = spat_count (snd uf2) in
	if _pt1 <= _pt2 && _ne2 <> 0 then
	  let uf2_pe = (fst uf2, List.map make_pe (snd uf2)) in
	  if uform_adds_info2a prover uf uf2_pe then begin
	    (List.rev_append acc ufl, ufl_drop, uf2_pe :: ufl_new)
	  end else
	    join_list ufl_drop (uf2 :: acc) ufl
	else join_list ufl_drop (uf2 :: acc) ufl
  in
  if _ne1 <> 0 then
    let uf_pe = (fst uf, List.map make_pe (snd uf)) in
    let (ufl, ufl_drop_new) =
      List.partition (uform_adds_info2a prover uf_pe) ufl in
    if List.exists (uform_adds_info2 prover [uf]) ufl_drop_new then
      (ufl, ufl_drop_new @ ufl_drop, uf_pe :: ufl_new)
    else
      join_list (ufl_drop_new @ ufl_drop) [] ufl
  else
    let (ufl, ufl_drop_new) = 
       List.partition (uform_adds_info2a prover uf) ufl in
    join_list (ufl_drop_new @ ufl_drop) [] ufl


(** Abstract and remove redundant disjuncts *)
let uform_list_join prover udom ufl_new =
  let rec rem_disj ufl1 ufl2 = match ufl1 with
    | [] -> ufl2
    | uf::ufl1 -> 
			if uform_adds_info2 prover ufl2 uf
        && uform_adds_info2 prover ufl1 uf then
          rem_disj ufl1 (uf :: ufl2)
      else rem_disj ufl1 ufl2 
	in
  let (ufl_old, ufl) = udom in
  let ufl_new = uform_list_abs prover false ufl_new in
  let ufl_new = List.filter 
    (fun uf -> uform_adds_info1 ufl uf && uform_adds_info1 ufl_old uf
       && uform_adds_info2 prover ufl uf && uform_adds_info2 prover ufl_old uf)
    ufl_new 
	in
  match ufl_new with
    | [] -> (udom, [])
    | _ ->
        let ufl_new = rem_disj ufl_new [] in
        let (ufl, ufl_dropped) =
          List.partition (uform_adds_info prover ufl_new) ufl in
        let ufl = List.sort compare_uform (List.rev_append ufl_new ufl) in
        let udom = (List.rev_append ufl_dropped ufl_old, ufl) in
        (udom, ufl_new)

(* -------------------------------------------------------------------------- *)
(** {2 Join for extended props} *)
(* -------------------------------------------------------------------------- *)
(** Also generates an arithmetic program *)

(** Put into a normal form *)
let ef_to_nf (uf,scpl) =
  let exfv = abs_fv_uform uf in
  let uf = match map_uform (abs_fv_to_sub exfv) uf with
    | [] | _::_::_ -> assert false
    | [uf] -> uf in
  let rec go (uf',scpl') res =
    let exfv' = abs_fv_uform uf' in
    let exfv' = exfv @ List.filter (fun x -> not (List.memq x exfv)) exfv' in
    let sub = abs_fv_to_sub exfv' in
    List.fold
      (fun ((pl',sl'),scpl') res ->
         let sl' = List.sort compare_can_spred sl' in
         ((pl',sl'), scpl') :: res)
      (map_cform sub (uf',scpl'))
      res in
  let scpl =
    PList.map_val (List.reduce go >> List.sort compare_cform) scpl in
  if PList.exists (fun _ cp -> cp == []) scpl then
    cprop_false
  else
    cprop_cform (uf,scpl)

(** Just abstract; do not attempt to remove redundant disjuncts. *)
let prop_abs prover ep =
  let rec star_box res = function
    | PNil -> res
    | PCons (rid, cp, scpl) ->
        let res =
          List.fold
            (fun (uf,scpl) -> 
               List.fold
                 (fun cf res -> (uf, PCons (rid, cprop_cform cf, scpl))::res)
                 cp)
            res [] 
				in
        star_box res scpl 
	in
  let abs_fn cf = 
    let go r cf = cprop_or (prover.nf_cform cf) r in
    List.fold_left go cprop_false (abs_cform prover cf) 
	in
  ep
  |> ext_transform (fun (uf,scpl) -> star_box (cprop_uform uf) scpl)
	(**|>> pp "@.ext_tranform:@.%a@." pp_eprop*)
  |> ext_transform abs_fn
	(**|>> pp "@.ext_transform:@.%a@." pp_eprop*)
  |> ext_transform ef_to_nf
	(**|>> pp "@.ext_transform:@.%a@." pp_eprop*)
  |> remove_eform_duplicates

(** Test whether [ef] adds any new information as a disjunct to [efl].
    If not, add the appropriate edge for the generated arithmetic program. *)
let ext_adds_info prover efl ef = match efl with 
  | [] -> true 
  | _ ->
      let cf = cform_of_eform ef in
      (* 1. Same disjunct does not already exist in [efl] *)
      List.for_all
        (fun ef2 ->
           compare_cform cf (cform_of_eform ef2) <> 0
           || (put_edge_skip ef ef2; false))
        efl
      && begin
        (* 2. Provably weaker disjunct does not already exist in [efl] *)
        let exfv = form_exfv cf IdSet.empty in
        let (sub, sub2) = idpool_combine2 normal_ids exfv in
        let cp = map_cform sub cf in
        List.for_all 
          (fun ef2 -> 
             incr prover_calls; 
             let cf2 = cform_of_eform ef2 in
             let pl = prover.entails_cprop cp (cprop_cform cf2) in
             List.iter (fun p -> put_edge_implication ef sub2 p ef2) pl;
             pl = [])
          efl
      end

let prop_join prover ep_total ep ep_new =
  let rec rem_disj efl1 efl2 = match efl1 with
    | [] -> efl2
    | ef::efl1 -> 
        if ext_adds_info prover (List.rev_append efl1 efl2) ef then
          rem_disj efl1 (ef::efl2)
        else rem_disj efl1 efl2 in
	(**let _ = pp "@.ep_new:@.%a@." pp_eprop ep_new in*)
  let efl_new = prop_abs prover ep_new in
	(**let _ = pp "@.ep_new':@.%a@." pp_eprop efl_new in*)
  let efl_new = List.filter (ext_adds_info prover ep_total) efl_new in
  match efl_new with
    | [] -> (ep_total, ep, [])
    | _ ->
        let efl_new = rem_disj efl_new [] in
        let efl_total = List.rev_append efl_new ep_total in
        let efl = List.filter (ext_adds_info prover efl_new) ep in
        let efl = remove_eform_duplicates (List.rev_append efl_new efl) in
        (efl_total, efl, efl_new)

(** Main entry point *)
let mk_abstraction prover =
  { uform_abs  = uform_list_abs prover
  ; uform_join = uform_list_join prover
  ; prop_abs   = prop_abs prover
  ; prop_join  = prop_join prover
  }

