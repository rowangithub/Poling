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

(** Non-disjuctive pure assertions are of the form:
      x1=E1 & ... & xn=En & A1 & ... & Am 
    where:
     - the xi are distinct
     - the Ei do not contain occurrences of any xj
     - the Ai do not contain occurrences of any xj
     - xi < fv(Ei)
    All operations should preserve these invariants.
 *)
type t = (Id.t, exp) plist * exp list

let rec compare_eqs l1 l2 = 
  if l1 == l2 then 0 else match l1 with
    | PNil -> -1
    | PCons (k1, v1, l1) -> (match l2 with
      | PNil -> 1
      | PCons (k2, v2, l2) ->
          let n = Id.compare k1 k2 in if n <> 0 then n else
          let n = compare_exp v1 v2 in if n <> 0 then n else
          compare_eqs l1 l2)

let compare (eq1,al1) (eq2,al2) = 
  let n = compare_eqs eq1 eq2 in if n <> 0 then n else
  compare_exp_list al1 al2


(* -------------------------------------------------------------------------- *)
(** {2 Pretty printing} *)
(* -------------------------------------------------------------------------- *)

let rec pp_starsep pp f = function
  | [] -> Format.pp_print_string f "emp"
  | [x] -> pp f x
  | x::l -> pp f x; Format.fprintf f "@ * "; pp_starsep pp f l

let rec pp_non_empty_eqs f l = match l with
  | PNil -> assert false
  | PCons (i, e, l) ->
      Format.pp_print_string f (Id.to_string i);
      Format.pp_print_char f '=';
      pp_exp f e;
      begin match l with PNil -> () | _ ->
	Format.fprintf f "@ * ";
	pp_non_empty_eqs f l
      end

let pp f (eq,al) =
  match al with
    | [] -> 
			if eq == PList.nil then Format.pp_print_string f "emp"
			else pp_non_empty_eqs f eq
    | _::_ ->
			if eq != PList.nil then begin
	  		pp_non_empty_eqs f eq;
	  		Format.fprintf f "@ * ";
			end;
			pp_starsep pp_exp f al

(* -------------------------------------------------------------------------- *)
(** {2 Constructors & basic operations }  *)
(* -------------------------------------------------------------------------- *)

let ptrue = (PNil,[])
let pfalse = (PNil,[E.zero])

let has_neql (_,l) = l != []

let eq_length (eq,_) = PList.length eq

(** Is the pure formula true. *)
let is_true = function (PNil,[]) -> true | _ -> false

(** Is it satisfiable (i.e. of the form [_x1=E1 & ... & _xn=En]) *)
let is_sat = function 
  | (eq,[]) -> PList.for_all (fun i _ -> Id.is_existential i) eq
  | _ -> false

(** Does it contain an equality where the LHS is not an ex.variable *)
let has_unsat_eq (eq,_) =
  not (PList.for_all (fun i _ -> Id.is_existential i) eq)

(** Is the pure formula false. *)
let is_false (_,al) = mem_exp E.zero al

let rec opt_findq l x = match l with
  | PCons (k, v, ln) ->
      if k == x then v else opt_findq ln x
  | PNil -> E.id x

(** Generate a substitution. *)
let to_sub (eq,_) = mk_subst eq

(** Convert to an expression. *)
let to_exp (eq,al) =
  E.band (PList.fold (fun i e res -> E.eq (E.id i) e :: res) eq al)

(** Only equalities of x=e where [exfv(e)={}] *)
let only_inst_eqs (eq,al) =
  (PList.filter (fun i e -> IdSet.is_empty (E.exfv e IdSet.empty)) eq,[])

let remove_eqs (eq,al) =
  (PList.filter (fun i e -> not (Id.is_existential i)) eq,al)


(** Apply substitution [f] to each expression in [el].
    If the result is an equality, add it to [acc2].
    Otherwise, add it to [acc1]. *)
let rec map_sub2 f acc1 acc2 el = match el with
  | e :: el ->
      let e' = f e in
      begin match e' with
      | Efun(Sfn_AND, ml) -> go_add2 f acc1 acc2 el ml
      | Eeq(Eident _, _)
      | Eeq(_, Eident _) -> map_sub2 f acc1 (e' :: acc2) el
      | Enum 0 -> ([E.zero], [])
      | Enum _ -> map_sub2 f acc1 acc2 el
      | _ -> map_sub2 f (e' :: acc1) acc2 el
      end
  | [] -> (acc1, acc2)

(** Sort out all the expressions in [ml] and then do [map_sub2 f acc1 acc2 el]. *)
and go_add2 f acc1 acc2 el ml = match ml with
  | m :: ml ->
      begin match m with
      | Eeq (Eident _, _) 
      | Eeq (_, Eident _) -> go_add2 f acc1 (m :: acc2) el ml
      | Enum 0 -> ([E.zero], [])
      | Enum _ -> go_add2 f acc1 acc2 el ml
      | _ -> go_add2 f (m :: acc1) acc2 el ml
      end
  | [] -> map_sub2 f acc1 acc2 el 

(** Assumption: [i] does not appear in the LHS of [eq]. *)
let rec add_one_eq eq al i e = 
  let sub = mk_single_subst i e in
  let eq = PList.cons i e (PList.map_val sub eq) in
  let (al, al_new) = map_sub2 sub [] [] al in
  match al_new with 
    | [] -> (eq, al)
    | [Eeq ((Eident _ as i), e)] -> add_one_eq eq al (Id.of_exp i) e
    | [Eeq (e, (Eident _ as i))] -> add_one_eq eq al (Id.of_exp i) e
    | _ -> add_multiple_eqs eq al al_new

and add_multiple_eqs eq al al_new = match al_new with
  | Eeq ((Eident _ as i), e) :: al_new -> 
      let i = Id.of_exp i in
      let sub = mk_single_subst i e in
      let eq = PList.cons i e (PList.map_val sub eq) in
      let (al, al_new) = map_sub2 sub al [] al_new in
      add_multiple_eqs eq al al_new
  | Eeq (e, (Eident _ as i)) :: al_new ->
      let i = Id.of_exp i in
      let sub = mk_single_subst i e in
      let eq = PList.cons i e (PList.map_val sub eq) in
      let (al, al_new) = map_sub2 sub al [] al_new in
      add_multiple_eqs eq al al_new
  | _ :: _ -> assert false
  | [] ->
      let sub = mk_subst eq in
      let (al, al_new) = map_sub2 sub [] [] al in
      match al_new with 
        | [] -> (eq, al)
        | [Eeq ((Eident _ as i), e)] -> add_one_eq eq al (Id.of_exp i) e
        | [Eeq (e, (Eident _ as i))] -> add_one_eq eq al (Id.of_exp i) e
        | _ -> add_multiple_eqs eq al al_new

let add_one_sub_atom a (eq,al) = 
  let a' = mk_subst eq a in
  match a' with
  | Efun(Sfn_AND, el) ->
      let (el_eq, el) = List.partition 
        (function Eeq (Eident _, _) -> true
                | Eeq (_, Eident _) -> true
                | _ -> false) el in
      add_multiple_eqs eq (List.rev_append el al) el_eq
      (* List.fold add_one_sub_atom el (eq,al) *)
  | Eeq((Eident _ as i), e) -> add_one_eq eq al (Id.of_exp i) e
  | Eeq(e, (Eident _ as i)) -> add_one_eq eq al (Id.of_exp i) e
  | Enum n -> if n = 0 then pfalse else (eq,al)
  | _ -> (eq, a'::al)

let add_one_sub_eq i e p =
  add_one_sub_atom (E.eq (E.id i) e) p


let rec check_consistent_one al = function
  | Enum 0 -> false 
  | Efun2 (Sfn_list_lt, Efun1 (Sfn_item, x1), x2) ->
      List.for_all 
				(function
				   | Efun2 (Sfn_list_lt, y1, Efun1 (Sfn_item, y2)) ->
			               not (equal_exp y1 x2 && equal_exp y2 x1)
				   | Efun2 (Sfn_subset, Efun1 (Sfn_item, y1),
			             Efun1 (Sfn_set_of_list, y2)) ->
			               not (equal_exp y1 x1 && equal_exp y2 x2)
				   | _ -> true) al 
  | Efun2 (Sfn_list_lt, x1, Efun1 (Sfn_item, x2)) ->
      List.for_all 
				(function
				   | Efun2 (Sfn_list_lt, Efun1 (Sfn_item, y1), y2) ->
			               not (equal_exp y1 x2 && equal_exp y2 x1)
				   | Efun2 (Sfn_subset, Efun1 (Sfn_item, y1),
			                      Efun1 (Sfn_set_of_list, y2)) ->
			               not (equal_exp y1 x1 && equal_exp y2 x2)
				   | _ -> true) al 
  | Efun2 (Sfn_subset, Efun1 (Sfn_item, x1),
             Efun1 (Sfn_set_of_list, x2)) ->
      List.for_all
				(function
				   | Efun2 (Sfn_list_lt, Efun1 (Sfn_item, y1), y2) ->
				       not (equal_exp y1 x1 && equal_exp y2 x2)
				   | Efun2 (Sfn_list_lt, y2, Efun1 (Sfn_item, y1)) ->
				       not (equal_exp y1 x1 && equal_exp y2 x2)
				   | _ -> true) al 
  | Eeq (x, y) ->
      List.for_all
				(function
				   | Efun2 (Sfn_list_lt, Efun1 (Sfn_item, x1), Efun1 (Sfn_item, y1)) ->
				       not (equal_exp x x1 && equal_exp y y1 || equal_exp y x1 && equal_exp y1 x)
				   | _ -> true) al 
  | _ -> true

let rec check_consistent al0 = function
(*  | Efun (Sfn_OR, el) :: al ->
      List.exists (check_consistent_one al0) el && check_consistent al0 al  *)
  | a :: al -> 
      check_consistent_one al a && check_consistent al0 al
  | [] -> true

(*

let rec check_consistent al0 = function
  | Enum 0 :: _ -> false 
(*  | Eident _ :: al -> check_consistent al *)
  | Efun2 (Sfn_list_lt, Efun1 (Sfn_item, x1), x2) :: al ->
      List.for_all 
	(function
	   | Efun2 (Sfn_list_lt, y1, Efun1 (Sfn_item, y2)) ->
               not (equal_exp y1 x2 && equal_exp y2 x1)
	   | Efun2 (Sfn_subset, Efun1 (Sfn_item, y1),
             Efun1 (Sfn_set_of_list, y2)) ->
               not (equal_exp y1 x1 && equal_exp y2 x2)
	   | _ -> true) al 
      && check_consistent al0 al
  | Efun2 (Sfn_list_lt, x1, Efun1 (Sfn_item, x2)) :: al ->
      List.for_all 
	(function
	   | Efun2 (Sfn_list_lt, Efun1 (Sfn_item, y1), y2) ->
               not (equal_exp y1 x2 && equal_exp y2 x1)
	   | Efun2 (Sfn_subset, Efun1 (Sfn_item, y1),
                      Efun1 (Sfn_set_of_list, y2)) ->
               not (equal_exp y1 x1 && equal_exp y2 x2)
	   | _ -> true) al 
      && check_consistent al0 al
  | Efun2 (Sfn_subset, Efun1 (Sfn_item, x1),
             Efun1 (Sfn_set_of_list, x2)) :: al ->
      List.for_all
	(function
	   | Efun2 (Sfn_list_lt, Efun1 (Sfn_item, y1), y2) ->
	       not (equal_exp y1 x1 && equal_exp y2 x2)
	   | Efun2 (Sfn_list_lt, y2, Efun1 (Sfn_item, y1)) ->
	       not (equal_exp y1 x1 && equal_exp y2 x2)
	   | _ -> true) al 
      && check_consistent al0 al
  | Efun (Sfn_OR, el) :: al ->
      List.exists (fun e -> check_consistent [] (e::al0)) el
      && check_consistent al0 al
  | Eeq (x, y) :: al ->
      List.for_all
	(function
	   | Efun2 (Sfn_list_lt, Efun1 (Sfn_item, y1), y2) ->
	       not (equal_exp y1 x1 && equal_exp y2 x2)
	   | Efun2 (Sfn_list_lt, y2, Efun1 (Sfn_item, y1)) ->
	       not (equal_exp y1 x1 && equal_exp y2 x2)
	   | _ -> true) al 

  | _ :: al -> 
      check_consistent al0 al
  | [] -> true
*)

(** Conjoin one expression to an pure formula. *)
let conj_one (a : exp)  (p : t) : t = 
  let p' = add_one_sub_atom a p in
  if check_consistent (snd p') (snd p') then p' else pfalse

(** Conjoin two pure formulae. *)
let conj ((eq1,al1) : t) (p2 : t) = 
  let (p3 : t) = PList.fold add_one_sub_eq eq1 p2 in
  let p' = List.fold add_one_sub_atom al1 p3 in
  if check_consistent (snd p') (snd p') then p' else pfalse

let one a = conj_one a ptrue

let filter f (eq,el) = (eq,List.filter f el)

let fold f (eq,el) acc =
  PList.fold (fun i e acc -> f (E.eq (E.id i) e) acc) eq
    (List.fold f el acc)

let normalize (eq,al) = 
  let al = remdup_exp al in
  if is_false (eq,al) then []
  else [(eq, al)]

(** Return the list of equalities between set expressions
    in the pure formula. *)
let get_set_eqs (eq,al) =
  let rec go r x = match x with
    | Eeq(Efun(Sfn_set, el1), Efun(Sfn_set, el2)) -> (el1,el2)::r
    | _ -> r in
  List.fold_left go [] al


(* -------------------------------------------------------------------------- *)
(** {2 Top-level pure disjunctions} *)
(* -------------------------------------------------------------------------- *)

let list_conj pll1 pll2 = 
  List.fold_left (fun res pl1 -> 
    List.fold_left (fun res pl2 -> conj pl1 pl2 :: res) res pll2) [] pll1

let lifted_list_conj pll1 pll2fn = 
  match pll1 with
  | [] -> [] 
  | _  -> list_conj pll1 (pll2fn ())

let common (eq1,al1) (eq2,al2) =
  let mem_eq l i e = 
    let equal_ident_exp i1 e1 i2 e2 = i1==i2 && equal_exp e1 e2 in
    PList.exists (equal_ident_exp i e) l in
  let mem_atom l x = List.exists (equal_exp x) l in
  (PList.filter (mem_eq eq1) eq2, List.filter (mem_atom al1) al2)
	
(** MCPA major update: 
* This procedure is really a hack. SUCKS!!!!
* Because normalization will replace some variable into integer .... FUCK!
* We have to change such variables back in order to get common ...
* Bullshit ...
*)	
let mcpa_common (eq1,al1) (eq2,al2) =
	let f eq al = 
		List.fold_left (fun res exp -> match exp with
			| Enum _ | Eident _ | Efun _ | Egrp _ | Efun1 _ -> exp :: res
			| Eeq (e1,e2) | Efun2(_,e1,e2) -> (
					let se = map_id_exp_sub (fun exp ->
						PList.get_first (fun id exp' -> 
							if ((Exp.compare_exp exp exp') = 0) then Some (E.id id)
							else None
							) eq
						) exp in
					if ((Exp.compare_exp se exp) = 0) then exp :: res
					else se :: (exp :: res)
				)
			) [] al in
	let al1 = f eq1 al1 in
	let al2 = f eq2 al2 in
  let mem_eq l i e = 
    let equal_ident_exp i1 e1 i2 e2 = i1==i2 && equal_exp e1 e2 in
    PList.exists (equal_ident_exp i e) l in
  let mem_atom sub1 sub2 l x = 
		(*let l = Exp.map_sub sub2 l in
		let x = List.hd (Exp.map_sub sub1 [x]) in*)
		List.exists (equal_exp x) l in
	let sub1 = mk_subst eq1 in
	let sub2 = mk_subst eq2 in
  (PList.filter (mem_eq eq1) eq2, List.filter (mem_atom sub1 sub2 al1) al2)	


(* -------------------------------------------------------------------------- *)
(** {2 Pure prover} *)
(* -------------------------------------------------------------------------- *)

(** Pure entailment *)
let entails_exp (eq,al) e = 
  let e = mk_subst eq e in
  let (eq2, al2) = add_one_sub_atom e ptrue in
  eq2 == PList.nil && List.for_all (fun x -> mem_exp x al) al2

(** Find a simpler [pl3] such that [pl1 |- pl3] iff [pl1 |- pl2]. *)
let simplify pl1 pl2 = 
  let e2 = (to_sub pl1) (to_exp pl2) in
  let (eq2,al2) = add_one_sub_atom e2 ptrue in
  let (_,al1) = pl1 in
  (eq2, List.filter (fun x -> not (mem_exp x al1)) al2)

let entails pl1 pl2 =
  is_sat (simplify pl1 pl2)

let (@&) = conj_one


let normalize_aggr (eq,al) =
  let al = remdup_exp al in
  let rec goexp eq res al1 al2 = match al2 with 
    | Enum 0 :: al2 -> res
    | Enum _ :: al2 -> goexp eq res al1 al2
    | Efun1(Sfn_NOT, Efun2(Sfn_list_lt, (Efun1 (Sfn_item, _) as e1),
                               (Efun1 (Sfn_item, _) as e2)))::al2 ->
	let p = (eq, List.rev_append al1 al2) in
	let pl = [E.eq e1 e2 @& p; E.fun2 Sfn_list_lt e2 e1 @& p] in
	List.fold_left gopure res pl
    | (Efun1(Sfn_NOT, e) as a)::al2 ->
        if mem_exp e al1 || mem_exp e al2 then res 
        else goexp eq res (a::al1) al2
    | Efun(Sfn_OR,el) :: al2 ->
	let p = (eq, List.rev_append al1 al2) in
	let pl = List.map (fun e -> e @& p) el in
	List.fold_left gopure res pl
(* TODO *)
    | Efun2(Sfn_subset, (Efun1 (Sfn_item, _) as x1), Efun1 (Sfn_set_of_list, x2))::al2 ->
	let p = (eq, List.rev_append al1 al2) in
        let id1 = E.gensym_str_ex "listid" in
        let id2 = E.gensym_str_ex "listid" in
        gopure res (E.eq (E.list [id1; x1; id2]) x2 @& p)
    | Eeq(Efun(Sfn_list,e1::el1), Efun(Sfn_list,e2::el2)) :: al2
        when not (mem_exp e1 el2) && not (mem_exp e2 el1) ->
	let id = E.gensym_str_ex "listid" in
	let p = (eq, List.rev_append al1 al2) in
	gopure 
	  (gopure res
	     (E.eq e1 (E.list [e2;id])
              @& E.eq (E.list (id::el1)) (E.list el2) @& p))
	  (E.eq (E.list [e1;id]) e2
           @& E.eq (E.list el1) (E.list (id::el2)) @& p)
    | Eeq((Efun1(Sfn_item,_) as e1), Efun(Sfn_list,e2::el2))::al2 ->
	let p = (eq, List.rev_append al1 al2) in
	gopure 
	  (gopure res
	     (E.eq (E.list []) e2 @& E.eq e1 (E.list el2) @& p))
	  (E.eq e1 e2 @& E.eq (E.list []) (E.list el2) @& p)
    | Eeq(Efun(Sfn_list,e1::el1), (Efun1(Sfn_item,_) as e2))::al2 ->
	let p = (eq, List.rev_append al1 al2) in
	gopure 
	  (gopure res
	     (E.eq (E.list []) e1 @& E.eq e2 (E.list el1) @& p))
	  (E.eq e2 e1 @& E.eq (E.list []) (E.list el1) @& p)
    | a::al2 -> goexp eq res (a::al1) al2
    | [] -> (eq, List.rev al1)::res
  and gopure res (eq,al) =
(*    let _ = if !Config.verbose2 then
      Format.fprintf (!Config.formatter) "norm @[%a@]@." pp (eq,al) in *)
    if is_false (eq,al) then res else goexp eq res [] al
  in
  let add_trans res (eq,al) =
    let (@+) x l = if List.exists (equal_exp x) l then l else x::l in
    let go1 x1 x2 res e = match e with
      | Efun2(Sfn_list_lt, Efun1 (Sfn_item, y1), y2) when equal_exp y1 x2 ->
	  E.fun2 Sfn_list_lt x1 y2 @+ res
      | _ -> res in
    let go2 x1 x2 res e = match e with
      | Efun2(Sfn_list_lt, y1, Efun1 (Sfn_item, y2)) when equal_exp y2 x1 ->
	  E.fun2 Sfn_list_lt y1 x2 @+ res
      | _ -> res in
    let rec go l res = match l with
      | Efun2(_, x1, x2)::l ->
          let res = match x1 with
            | Efun1 (Sfn_item, x1) -> List.fold_left (go2 x1 x2) res res
            | _ -> res in
          let res = match x2 with
            | Efun1 (Sfn_item, x2) -> List.fold_left (go1 x1 x2) res res
            | _ -> res in
          go l res
      | _ :: _ -> assert false
      | [] -> res in
    let (al0,al1) =
      List.partition 
	(function Efun2(Sfn_list_lt,_,_) -> true | _ -> false) al in
    let al0 = go al0 al0 in
    if List.exists 
      (function 
	 | Efun2 (Sfn_subset, Efun1 (Sfn_item, x1), Efun1 (Sfn_set_of_list, x2)) ->
	     List.exists 
	       (function
		  | Efun2 (_, Efun1 (Sfn_item, y1), y2) -> equal_exp x1 y1 && equal_exp x2 y2
		  | Efun2 (_, y2, Efun1 (Sfn_item, y1)) -> equal_exp x1 y1 && equal_exp x2 y2
		  | _ -> false) al0 
	 | _ -> false) al1
    then res
    else (eq,List.rev_append al0 al1)::res
  in
(*  let _ = if !Config.verbose2 then
    Format.fprintf (!Config.formatter) "normalize_aggr@." in *)
  let res = gopure [] (eq,al) in
  let res = List.fold_left add_trans [] res in
(*  let _ = if !Config.verbose2 then
    Format.fprintf (!Config.formatter) "done@." in *)
  res

(*let normalize_aggr p =
  let mapexp sp = match sp with
    | Efun2 (Sfn_subset, (Efun1 (Sfn_item, _) as x1), Efun1 (Sfn_set_of_list, x2)) ->
        E.eq (E.list [E.gensym_str_ex "listid"; x1; E.gensym_str_ex "listid"]) x2 
    | _ -> sp in
  List.reduce_append
    (fun (eq,al) -> normalize_aggr (eq, List.map mapexp al))
    (normalize_aggr p)
*)
(*
let normalize_aggr (eq,al) =
  let mapexp sp = match sp with
    | Efun2 (Sfn_subset, (Efun1 (Sfn_item, _) as x1), Efun1 (Sfn_set_of_list, x2)) ->
        E.eq (E.list [E.gensym_str_ex "listid"; x1; E.gensym_str_ex "listid"]) x2 
    | _ -> sp in
  normalize_aggr (eq, List.map mapexp al)
*)

(* -------------------------------------------------------------------------- *)
(** {2 Free variables} *)
(* -------------------------------------------------------------------------- *)

let no_s s (eq,al) =
  PList.for_all (fun i e -> exp_no_s s (E.id i) && exp_no_s s e) eq
  && List.for_all (exp_no_s s) al

let fv (eq,al) acc =
  PList.fold (fun i e acc -> IdSet.add i (E.fv e acc)) eq
    (List.fold E.fv al acc)

let exfv (eq,al) acc =
  PList.fold (fun i e acc -> 
		let acc = E.exfv e acc in
		if Id.is_existential i then IdSet.add i acc else acc) eq
    (List.fold E.exfv al acc)

let fhd (eq,al) acc =
  PList.fold_val E.fhd eq
    (List.fold E.fhd al acc)


(* -------------------------------------------------------------------------- *)
(** {2 Substitutions} *)
(* -------------------------------------------------------------------------- *)

(* TODO: inefficient *)
(*let map f_e p = conj_one (f_e (to_exp p)) true *)

let rec map_al f_e acc1 acc2 al = match al with
  | e :: al ->
      let e' = f_e e in
      if e' == e then 
	map_al f_e (e' :: acc1) acc2 al
      else begin match e' with
	| Enum n -> if n = 0 then ([], [E.zero])
                      else map_al f_e acc1 acc2 al
	| _ -> map_al f_e acc1 (e' :: acc2) al
      end
  | [] -> (acc1, acc2)


let rec map_eqs f_e acc1 acc2 eqs = match eqs with
  | PNil -> (acc1, acc2)
  | PCons (i, e, l) ->
      let i = E.id i in
      let i' = f_e i in
      let e' = f_e e in
      if i' == i && e' == e then
	map_eqs f_e (PList.cons (Id.of_exp i') e' acc1) acc2 l
      else begin match i', e' with
	| Eident _, Eident _ ->
	    if compare_exp i' e' < 0 then
	      map_eqs f_e (PList.cons (Id.of_exp i') e' acc1) acc2 l
	    else 
	      map_eqs f_e acc1 (E.eq i' e' :: acc2) l
	| Eident _, _ ->
	    map_eqs f_e (PList.cons (Id.of_exp i') e' acc1) acc2 l
	| _ ->
	    map_eqs f_e acc1 (E.eq i' e' :: acc2) l
      end 

let map f_e (eq0, al0) =
  let (al, al_new) = map_al f_e [] [] al0 in
  let (eq, al_new) = map_eqs f_e PNil al_new eq0 in
  let p' = List.fold add_one_sub_atom al_new (eq,al) in
  let p' = (fst p', remdup_exp (snd p')) in
  if check_consistent (snd p') (snd p') then p' else pfalse


let identical_eq (eq1,_) (eq2,_) = eq1 == eq2

let exp_has_no_can_return e =
  exp_fold (fun e r -> r && match e with 
              | Efun1 (Sfn_can_return, _) -> false
              | _ -> true)
    e true

(* HACK *)
let has_can_return (eq,el) =
  not (List.for_all exp_has_no_can_return el)

(** Compute a weaker pure assertion that does not mention variables [kill]. *)
let kill_vars kill (eq,el) =
  let killable i = IdSet.mem i kill in
  let eq = PList.filter
     (fun i e -> not (killable i) 
	&& not (IdSet.exists killable (E.exfv e IdSet.empty))) eq in
  let el = List.filter
     (fun e -> not (IdSet.exists killable (E.exfv e IdSet.empty))) el in
  (eq,el)

let kill_can_return (eq,el) =
  let eq = PList.filter (fun _i e -> exp_has_no_can_return e) eq in
  let el = List.filter exp_has_no_can_return el in
  (eq,el)


(* -------------------------------------------------------------------------- *)
(** {2 Disjoint sets} *)
(* -------------------------------------------------------------------------- *)

(** Returns the set of expresssions that are not equal to e in pl *)
let get_uneql e (_,el) = 
  let rec go = function
    | [] -> Dset.emp
    | Efun1(Sfn_NOT,Eeq(e1,e2))::pl ->
	if equal_exp e1 e then Dset.add e2 (go pl)
	else if equal_exp e2 e then Dset.add e1 (go pl)
	else go pl
    | _::pl -> go pl
  in go el
