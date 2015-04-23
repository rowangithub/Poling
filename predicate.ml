(* Poling: Proof Of Linearizability Generator 
 * Poling is built on top of CAVE and shares the same license with CAVE 
 * See LICENSE.txt for license.
 * Contact: He Zhu, Department of Computer Science, Purdue University
 * Email: zhu103@purdue.edu
 *)

open Format
open Exp
open Misc
open Parsetree

exception Unfold_ex

type binop =
    Plus
  | Minus
  | Times
  | Div

type binrel =
    Eq
  | Ne
  | Gt
  | Ge
  | Lt
  | Le

type patpexpr =
    PPInt of int list
  | PVar of Id.t list
  | PFunApp of string * patpexpr list 
  | PBinop of patpexpr * binop list * patpexpr
  | PField of string * patpexpr
  | PProj of int * patpexpr
	| PUnion of patpexpr * patpexpr
	| PConcat of patpexpr * patpexpr

type tpat =
    PTrue
  | PAtom of patpexpr * binrel list * patpexpr
  | PIff of patpexpr * tpat
  | PNot of tpat
  | PAnd of tpat * tpat
  | POr of tpat * tpat
	| PIn of patpexpr * patpexpr
	| PRecpred of string * patpexpr

type pexpr =
    PInt of int 
  | Var of Id.t
  | FunApp of string * pexpr list  
  | Binop of pexpr * binop * pexpr
  | Field of string * pexpr
  | Proj of int * pexpr
	| Union of pexpr * pexpr (* Support set union operation *)
	| Concat of pexpr * pexpr (* Support concatation operation *)

type t =
    True
  | Atom of pexpr * binrel * pexpr 
  | Iff of pexpr * t
  | Not of t
  | And of t * t 
  | Or of t * t
	| In of pexpr * pexpr (* Support set in opertion *)
	| Recpred of string * pexpr

let pprint_rel = function
    Eq -> "="
  | Ne -> "!="
  | Gt -> ">"
  | Ge -> ">="
  | Lt -> "<"
  | Le -> "<="

let rec pprint_pexpr ppf = function
  | PInt n ->
      if n < 0 then fprintf ppf "(0 - %d)" (-n)
      else fprintf ppf "%d" n
  | Var x ->
      fprintf ppf "%s" (Id.to_string x) 
  | FunApp (f, pexp) ->
			let _ = fprintf ppf "%s" f in
			List.iter (fun p -> (fprintf ppf "%s" " "; (pprint_pexpr ppf p))) pexp
  | Binop (p, op, q) ->
      let opstr = match op with
        | Plus -> "+"
        | Minus -> "-"
        | Times -> "*"
				| Div -> "/"
      in fprintf ppf "@[(%a@ %s@ %a)@]" pprint_pexpr p opstr pprint_pexpr q
  | Field (f, pexp) ->
      fprintf ppf "@[%a.%s@]" pprint_pexpr pexp f
  | Proj (n, pexp) ->
      fprintf ppf "@[%a.%d@]" pprint_pexpr pexp n
	| Union (p, q) ->
			fprintf ppf "@[(%a@ %s@ %a)@]" pprint_pexpr p "Um" pprint_pexpr q
	| Concat (p, q) ->
			fprintf ppf "@[(%a@ %s@ %a)@]" pprint_pexpr p "::" pprint_pexpr q

let rec pprint ppf = function
  | True ->
      fprintf ppf "true"
  | Atom (p, rel, q) ->
      fprintf ppf "@[(%a@ %s@ %a)@]" pprint_pexpr p (pprint_rel rel) pprint_pexpr q
  | Iff (px, q) ->
      fprintf ppf "@[(%a@ <=>@;<1 2>%a)@]" pprint_pexpr px pprint q
  | Not p ->
      fprintf ppf "@[(not@ %a)@]" pprint p
  | And (p, q) ->
      fprintf ppf "@[(%a@ and@;<1 2>@;<1 2>%a)@]" flatten_conjuncts p flatten_conjuncts q
  | Or (p, q) ->
      fprintf ppf "@[(%a@ or@;<1 2>@;<1 2>%a)@]" flatten_disjuncts p flatten_disjuncts q
	| In (px, qx) -> 
			fprintf ppf "@[(%a@ <=>@;<1 2>%a)@]" pprint_pexpr px pprint_pexpr qx
	| Recpred (name, px) ->
			fprintf ppf "@[(%s %a)@]" name pprint_pexpr px
and flatten_conjuncts ppf = function
  | And (And (p1, p2), And (q1, q2)) ->
      fprintf ppf "@[%a@;<1 0>%a@;<1 0>%a@;<1 0>%a@]"
        flatten_conjuncts p1 flatten_conjuncts p2
        flatten_conjuncts q1 flatten_conjuncts q2
  | And (And (p1, p2), q)
  | And (q, And (p1, p2)) ->
      fprintf ppf "@[%a@;<1 0>%a@;<1 0>%a@]"
        pprint q flatten_conjuncts p1 flatten_conjuncts p2
  | p -> pprint ppf p
and flatten_disjuncts ppf = function
  | Or (Or (p1, p2), Or (q1, q2)) ->
      fprintf ppf "@[%a@;<1 0>%a@;<1 0>%a@;<1 0>%a@]"
        flatten_disjuncts p1 flatten_disjuncts p2
        flatten_disjuncts q1 flatten_disjuncts q2
  | Or (Or (p1, p2), q)
  | Or (q, Or (p1, p2)) ->
      fprintf ppf "@[%a@;<1 0>%a@;<1 0>%a@]"
        pprint q flatten_disjuncts p1 flatten_disjuncts p2
  | p -> pprint ppf p

let equals(p, q) = Atom(p, Eq, q)

let (==.) p q = equals (p, q)

let (!=.) p q = Atom (p, Ne, q)

let (>=.) p q = Atom (p, Ge, q)

let (>.) p q = Atom (p, Gt, q)

let (<=.) p q = Atom (p, Le, q)

let (<.) p q = Atom (p, Lt, q)

let (&&.) p q = And (p, q)

let (||.) p q = Or (p, q)

let (!.) p = Not p

let (<=>.) p q = Iff (p, q)

let (+-) p q = Binop (p, Plus, q)

let ( *-) p q = Binop (p, Times, q)

let (/-) p q = Binop (p, Div, q)

let (--) p q = Binop (p, Minus, q)         

let implies(p, q) = (!. p) ||. q

let (=>.) p q = implies (p, q)

let (?.) px qx = In (px, qx) (* Ask if px is \in q *)

let (int_true, int_false) = (PInt 1, PInt 0)

let expand_iff = function
  | Iff (px, q) -> ((px ==. int_true) &&. q) ||. ((px ==. int_false) &&. (!. q))
  | _ -> assert false

let big_and = function
  | c :: cs -> List.fold_left (&&.) c cs
  | [] -> True

let big_or = function
  | c :: cs -> List.fold_left (||.) c cs
  | [] -> Not True

let rec pexp_map_vars f pexp =
  let rec map_rec = function
      Var x -> f x
    | FunApp (fn, e) ->
        FunApp (fn, List.map map_rec e)
    | Binop (e1, op, e2) ->
        Binop (map_rec e1, op, map_rec e2)
    | Field (f, pexp) ->
        Field (f, map_rec pexp)
    | Proj (n, pexp) ->
        Proj (n, map_rec pexp)
		| Union (e1, e2) ->
				Union (map_rec e1, map_rec e2)
		| Concat (e1, e2) -> 
				Concat (map_rec e1, map_rec e2)
    | e -> e
  in map_rec pexp

let rec map_vars f pred =
  let rec map_rec = function
      True ->
        True
    | Atom (e1, rel, e2) ->
        Atom (pexp_map_vars f e1, rel, pexp_map_vars f e2)
    | Iff (px, q) -> Iff (pexp_map_vars f px, map_rec q)
    | Not p ->
        Not (map_rec p)
    | And (p, q) ->
        And (map_rec p, map_rec q)
    | Or (p, q) ->
        Or (map_rec p, map_rec q)
		| In (px, qx) -> In (pexp_map_vars f px, pexp_map_vars f qx)
		| Recpred (fn, e) -> Recpred (fn, pexp_map_vars f e)
  in map_rec pred
	
let rec pexp_map_fields f pexp =
  let rec map_rec = function
      Var x -> Var x
    | FunApp (fn, e) ->
        FunApp (fn, List.map map_rec e)
    | Binop (e1, op, e2) ->
        Binop (map_rec e1, op, map_rec e2)
    | Field (fe, pexp) ->
        Field (f fe, map_rec pexp)
    | Proj (n, pexp) ->
        Proj (n, map_rec pexp)
		| Union (e1, e2) ->
				Union (map_rec e1, map_rec e2)
		| Concat (e1, e2) ->
				Concat (map_rec e1, map_rec e2)
    | e -> e
  in map_rec pexp

let rec map_fields f pred =
  let rec map_rec = function
      True ->
        True
    | Atom (e1, rel, e2) ->
        Atom (pexp_map_fields f e1, rel, pexp_map_fields f e2)
    | Iff (px, q) -> Iff (pexp_map_fields f px, map_rec q)
    | Not p ->
        Not (map_rec p)
    | And (p, q) ->
        And (map_rec p, map_rec q)
    | Or (p, q) ->
        Or (map_rec p, map_rec q)
		| In (px, qx) -> In (pexp_map_fields f px, pexp_map_fields f qx)
		| Recpred (fn, e) -> Recpred (fn, pexp_map_fields f e)
  in map_rec pred	

let subst v x pred = map_vars (fun y -> if (Id.compare x y == 0) then v else Var y) pred

let apply_substs subs pred =
  let substitute p (x, e) = subst e x p in List.fold_left substitute pred subs

let rec instantiate_named_vars subs pred =
  map_vars (fun y -> Var (List.assoc (Id.to_string y) subs)) pred

let exp_vars_unexp = function
  | PInt _ -> ([], [])
  | Var x -> ([], [x])
  | Binop (e1, _, e2) -> ([e1; e2], [])
  | FunApp (_, es) -> (es, [])
  | Field (_, e) | Proj (_, e) -> ([e], [])
	| Union (e1, e2) -> ([e1; e2], [])
	| Concat (e1, e2) -> ([e1; e2], [])

let exp_vars e =
  List.expand exp_vars_unexp [e] []

let var_unexp = function
  | True -> ([], [])
  | Atom (e1, _, e2) -> ([], exp_vars e1 @ exp_vars e2)
  | Iff (e, q) -> ([q], exp_vars e)
  | Not p -> ([p], [])
  | And (p, q) | Or (p, q) -> ([p; q], [])
	| In (e1, e2) -> ([], exp_vars e1 @ exp_vars e2)
	| Recpred (_, e) -> ([], exp_vars e)

let vars e =
	List.expand var_unexp [e] []

(** Flatten the Union elmements *)
let rec flatten_union = function
  | Union (Union (p1, p2), Union (q1, q2)) ->
  	(flatten_union p1 @ (flatten_union p2 @ (flatten_union q1 @ flatten_union q2)))
  | Union (Union (p1, p2), q)
  | Union (q, Union (p1, p2)) -> (q :: (flatten_union p1 @ flatten_union p2))
	| Union (q1, q2) -> [q1; q2]
  | p -> [p]

let rec flatten_concat = function
	| Concat (Concat (p1, p2), Concat (q1, q2)) ->
  	(flatten_concat p1 @ (flatten_concat p2 @ (flatten_concat q1 @ flatten_concat q2)))
  | Concat (Concat (p1, p2), q)
  | Concat (q, Concat (p1, p2)) -> 
		(q :: (flatten_concat p1 @ flatten_concat p2))
	| Concat (q1, q2) -> [q1; q2]
  | p -> [p]

(** Flatten the and elements *)
let rec flatten_and = function
	| And (And (p1, p2), And (q1, q2)) ->
  	(flatten_and p1 @ (flatten_and p2 @ (flatten_and q1 @ flatten_and q2)))
  | And (And (p1, p2), q)
  | And (q, And (p1, p2)) -> (q :: (flatten_and p1 @ flatten_and p2))
	| And (q1, q2) -> [q1; q2]
  | p -> [p]

let transl_op = function
  | Predexp_plus -> Plus
  | Predexp_minus -> Minus
  | Predexp_times -> Times
  | Predexp_div -> Div
 
let transl_rel = function
  | Pred_eq -> Eq
  | Pred_ne -> Ne
  | Pred_gt -> Gt
  | Pred_ge -> Ge
  | Pred_lt -> Lt
  | Pred_le -> Le

(** unfolding based on separation logic formula *)
(** FIXME: Note this implementation is tailored for list linking data structure *)
let unfold_recursive_defnition pred unfold_func unfold_pred unfold_field = 
	let rec unfold_pexp pexp = match pexp with
		| Var x -> pexp
    | FunApp (fn, es) ->
				(** unfolding recursive function definition *)
				if (List.length es == 1) then 
					let ele = List.hd es in
					(*let exps = f fn ele in 
					if (List.length exps = 0) then pexp (* with soley data argument it cannot be unfoled *)
					else (* with only soley pointer argument it is unfolded *) 
						(** 1. sort the unfoldings *)
						let exps = List.stable_sort compare exps in
						let (hdexp, tlexps) = (List.hd exps, List.tl exps) in
						List.fold_right (fun exp res -> Union (exp, res)) tlexps hdexp*)
					try unfold_func fn ele with Unfold_ex -> pexp
				else (* with multiple arguments it is not unfolded. FIXME ? *)  pexp
    | Binop (e1, op, e2) ->
        Binop (unfold_pexp e1, op, unfold_pexp e2)
    | Field _ -> unfold_field pexp
        (*Field (f, unfold_pexp pexp)*)
    | Proj (n, pexp) ->
        Proj (n, unfold_pexp pexp)
		| Union (e1, e2) ->
			  (** 2. sort the union elements * and also remove empty set * *)
				let p = Union (unfold_pexp e1, unfold_pexp e2) in
				let eles = flatten_union p in 
				let eles = List.fold_right (fun ele res -> match ele with 
					| Var v -> (** see if this is empty set *)
						if ((Id.compare 
						Id.junk 
						v) = 0) then 
							res else 
								(ele :: 
								res)
					| _ -> ele :: res) eles [] in
				let eles = List.stable_sort compare eles in
				let (hdele, tleles) = (List.hd eles, List.tl eles) in
				List.fold_left (fun res ele -> Union (res, ele)) hdele tleles
		| Concat (e1, e2) ->
				(** The order of e1 and e2 should be preserved
					* However we still need to reassign hierachy relation
					*)
				let p = Concat (unfold_pexp e1, unfold_pexp e2) in
				let eles = flatten_concat p in 
				let eles = List.fold_right (fun ele res -> match ele with 
					| Var v -> (** see if this is empty set *)
						if ((Id.compare 
						Id.junk 
						v) = 0) then 
							res else 
								(ele :: 
								res)
					| _ -> ele :: res) eles [] in
				let (hdele, tleles) = (List.hd eles, List.tl eles) in
				List.fold_left (fun res ele -> Concat (res, ele)) hdele tleles
    | e -> e in 
	let rec unfold_def pred = match pred with
		| True -> True
    | Atom (e1, rel, e2) -> Atom (unfold_pexp e1, rel, unfold_pexp e2)
    | Iff (px, q) -> Iff (unfold_pexp px, unfold_def q)
    | Not p -> Not (unfold_def p)
    | And (p, q) -> And (unfold_def p, unfold_def q)
    | Or (p, q) -> Or (unfold_def p, unfold_def q)
		| In (px, qx) -> In (unfold_pexp px, unfold_pexp qx)
		| Recpred (fn, e) -> 
			(try unfold_pred fn e with Unfold_ex -> 
				(Misc.pp "Recursive predicate undefined.@."; assert false)) in
			(*| FunApp (fn', es) -> 
				(** unfolding recursive predicate definition *)
				if (List.length es == 1) then
					let ele = List.hd es in
					(** Do not sort *)
					let exps = f fn' ele in  
					let exps_len = List.length exps in
					if (exps_len = 0) then 
						(Misc.pp "Recursive predicate must be defined on pointer argument@."; assert false)
					else if (exps_len = 1) then Recpred (fn, List.hd exps)
					else	
						let (hdexp1, hdexp2) = (List.hd exps, List.hd (List.tl exps)) in
						(* our implementation provides some built-in resursive predicate *)
						if (String.compare fn "sorted" == 0) then
							snd (List.fold_left 
								(fun (prev, fm) exp -> 
									(exp, And (Recpred (fn, exp), And (Atom (prev, Le, exp), fm)))) 
								(hdexp2, 
									And (Recpred (fn, hdexp1), And (Recpred (fn, hdexp2), Atom (hdexp1, Le, hdexp2)))) 
								(List.tl (List.tl exps)))
						else (Misc.pp "Recursive predicate undefined.@."; assert false) 
				else (Misc.pp "multiple arguments in recursive function in recursive predicate?@."; assert false)
			| _ -> (Misc.pp "Recursive predicate should be defined upon recursive functions@."; assert false)*)
	unfold_def pred
	
	
let rec transl_pexp pexp = match pexp with
  | Enum n -> PInt n
  | Eident _ -> Var (Exp.Id.of_exp pexp)
  | Efun1 (i, e1) -> (match i with
		| Sfn_NOT -> ((*Misc.pp "Cannot translate not into pexpr@.";*) assert false) 
  	| Sfn_item -> transl_pexp e1
  	| Sfn_sorted -> (*Predicate.FunApp ("sorted", [transl_pexp e1])*)
				((*Misc.pp "Cannot translate sfn_sorted into pexpr@.";*) assert false) 
  	| Sfn_hd -> ((*Misc.pp "Cannot translate hd into pexpr@.";*) assert false)
  	| Sfn_tl -> ((*Misc.pp "Cannot translate tl into pexpr@.";*) assert false)
  	| Sfn_set_of_list -> ((*Misc.pp "Cannot translate set_of_list into pexpr@.";*) assert false)
  	| Sfn_can_return -> ((*Misc.pp "Cannot translate can_return into ppexpr@.";*) assert false)) 
	| Efun (i, el) -> (match i with
		| Sfn_list -> 
			if (List.length el = 0) then 
				((*Misc.pp "Cannot translate empty Sfn_list into pexpr@.";*) assert false)
			else transl_pexp (List.hd (List.rev el))
		| Sfn_set -> ((*Misc.pp "Cannot translate Sfn_set into pexpr@.";*) assert false)
		| _ -> ((*Misc.pp "Cannot translate Efun into pexpr@.";*) assert false) 
		)
	| _ -> ((*Misc.pp "Cannot translate pure into pexpr@.";*) assert false)

let rec transl_pred = function
		| Efun1 (Sfn_NOT, e) ->
	     Not (transl_pred e)	
		| Efun1 (Sfn_sorted, e) -> Recpred ("sorted", transl_pexp e)
	| Eeq (e1,e2) ->
      (try Atom (transl_pexp e1, Eq, transl_pexp e2)	with _ -> True)
	| Efun2 (i, e1, e2) ->
      (match i with 
				| Sfn_list_lt -> Atom (transl_pexp e1, Lt, transl_pexp e2)
  			| Sfn_subset -> True
  			| Sfn_set_minus -> True)
	| Efun (i, el) -> 
      (match i with
				| Sfn_AND ->   big_and (List.map transl_pred el)
  			| Sfn_OR  ->   big_or (List.map transl_pred el)
				| Sfn_list ->  ((*Misc.pp "Cannot translate Sfn_list into predicate@.";*) assert false)
  			| Sfn_set ->   ((*Misc.pp "Cannot translate Sfn_set into predicate@.";*) assert false)
  			| Sfn_XOR  ->  ((*Misc.pp "Cannot translate Sfn_XOR into predicate@.";*) assert false)
  			| Sfn_undef -> True) 
	| e -> ((*Misc.pp "Cannot translate pure into predicate%a@." pp_exp e;*) assert false)


(** FIXME: Not fully implemented *)
let rec transl_exp = function 
	| PInt i -> E.num i
  | Var x -> E.id x
  | Binop (e1, _, e2) -> (Misc.pp "Cannot translate FunApp into exp@."; assert false)
  | FunApp (_, es) -> (Misc.pp "Cannot translate FunApp into exp@."; assert false)
  | Field (_, e) | Proj (_, e) -> (Misc.pp "Cannot translate Field/Proj into exp@."; 
																		assert false)
	| Union (e1, e2) | Concat (e1, e2) -> 
			(Misc.pp "Cannot translate Union/Concat into exp@."; assert false)
	
	
(** For substituition *)
let transl_subs pred = 
	let rec rec_transl_subs pred res = match pred with
		| True -> res
	  | Atom (e1, rel, e2) -> (match rel with
			| Eq -> (match e1 with
				| Var var1 -> PList.cons var1 (transl_exp e2) res
				| _ -> (match e2 with
					| Var var2 -> PList.cons var2 (transl_exp e1) res
					| _ -> res
					)	
				)
			| _ -> res 
			)
	  | Iff (e, q) -> res
	  | Not p -> res
	  | And (p, q) -> rec_transl_subs p (rec_transl_subs q res)
		| Or (p, q) -> res
		| In (e1, e2) -> res
		| Recpred (_, e) -> res
	in Exp.mk_subst (rec_transl_subs pred PList.nil)
	
	
(** is using concatation? *)
let is_concat_pred pred = 	
	let rec map_rec' = function
			Var x -> false
    | FunApp (fn, e) -> List.exists map_rec' e
    | Binop (e1, op, e2) -> map_rec' e1 || map_rec' e2
    | Field (fe, pexp) -> map_rec' pexp
    | Proj (n, pexp) -> map_rec' pexp
		| Union (e1, e2) -> map_rec' e1 || map_rec' e2
		| Concat (e1, e2) -> true
    | e -> false in
	let rec map_rec = function
      True -> false
    | Atom (e1, rel, e2) -> map_rec' e1 || map_rec' e2
    | Iff (px, q) -> map_rec' px || map_rec q
    | Not p -> map_rec p
    | And (p, q) -> map_rec p || map_rec q
    | Or (p, q) -> map_rec p || map_rec q
		| In (px, qx) -> map_rec' px || map_rec' qx
		| Recpred (fn, e) -> map_rec' e in
  map_rec pred	
	
	
(** translate pred using concatatoin to union *)
let transl_concat_union pred =
	let rec map_rec' = function
			Var x -> Var x
    | FunApp (fn, e) ->
				let (fn', connection) = 
					try let index = String.index fn '_' 
					in (String.sub fn 0 index, String.sub fn (index+1) (String.length fn - index - 1))
					with _ -> (fn, "") in
				(*let _ = Misc.pp "fn' = %s and connection = %s\n" fn' connection in*)
				if (String.compare connection "c" = 0) then
        	FunApp (fn', List.map map_rec' e)
				else FunApp (fn, List.map map_rec' e)
    | Binop (e1, op, e2) ->
        Binop (map_rec' e1, op, map_rec' e2)
    | Field (fe, pexp) ->
        Field (fe, map_rec' pexp)
    | Proj (n, pexp) ->
        Proj (n, map_rec' pexp)
		| Union (e1, e2) ->
				Union (map_rec' e1, map_rec' e2)
		| Concat (e1, e2) ->
				Union (map_rec' e1, map_rec' e2)
    | e -> e in
	let rec map_rec = function
      True -> True
    | Atom (e1, rel, e2) ->
        Atom (map_rec' e1, rel, map_rec' e2)
    | Iff (px, q) -> Iff (map_rec' px, map_rec q)
    | Not p ->
        Not (map_rec p)
    | And (p, q) ->
        And (map_rec p, map_rec q)
    | Or (p, q) ->
        Or (map_rec p, map_rec q)
		| In (px, qx) -> In (map_rec' px, map_rec' qx)
		| Recpred (fn, e) -> Recpred (fn, map_rec' e) in
  map_rec pred	

  
	

 

