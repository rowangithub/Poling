(* Poling: Proof Of Linearizability Generator 
 * Poling is built on top of CAVE and shares the same license with CAVE 
 * See LICENSE.txt for license.
 * Contact: He Zhu, Department of Computer Science, Purdue University
 * Email: zhu103@purdue.edu
 *)

open Parsetree
open Predicate
open Misc

(** Transformers for qualifiers and specifications *)

(** Constant definition *)

let rel_star = [Ge; Le; Ne]
let op_star = [Plus; Minus; Times; Div]
let transl_ops ops = 
  match ops with 
      [] -> op_star 
    | _ -> List.map transl_op ops
let transl_rels rels = 
  match rels with 
      [] -> rel_star 
    | _ -> List.map transl_rel rels

(** A fast transformer for specificaions *)

let transl_patpred_single p =
	let rec transl_expr_rec pe =
  	match pe.ppredpatexp_desc with
    	| Ppredpatexp_int (n) ->
          let _ = if List.length n != 1 then assert false in
	        PInt (List.hd n)
      | Ppredpatexp_var (y) ->
          let y = match y with 
						| [sty] -> sty 
						| _ -> failwith "Var ident set used in single qualifier or predicate" in
	        Var (Exp.Id.create y)
      | Ppredpatexp_funapp (f, es) ->
	        FunApp (f, List.map transl_expr_rec es)
      | Ppredpatexp_binop (e1, ops, e2) ->
	        Binop (transl_expr_rec e1, transl_op (List.hd ops), transl_expr_rec e2)
      | Ppredpatexp_field (f, e1) ->
          Field (f, transl_expr_rec e1)
      | Ppredpatexp_proj (n, e1) ->
          Proj (n, transl_expr_rec e1)
			| Ppredpatexp_union (e1, e2) ->
					Union (transl_expr_rec e1, transl_expr_rec e2)
			| Ppredpatexp_concat (e1, e2) ->
					Concat (transl_expr_rec e1, transl_expr_rec e2)
      | _ -> failwith "Wildcard used in single qualifier or predicate"
  in
  let rec transl_pred_rec pd =
    match pd.ppredpat_desc with
      | Ppredpat_true -> 
          True
      | Ppredpat_atom (e1, rels, e2) ->
	        Atom (transl_expr_rec e1, transl_rel (List.hd rels), transl_expr_rec e2)
      | Ppredpat_not (p) -> 
          Not (transl_pred_rec p)
      | Ppredpat_and (p1, p2) -> 
          And (transl_pred_rec p1, transl_pred_rec p2)
      | Ppredpat_or (p1, p2) -> 
          Or (transl_pred_rec p1, transl_pred_rec p2)
			| Ppredpat_in (e1, e2) ->
					In (transl_expr_rec e1, transl_expr_rec e2)
			| Ppredpat_predrec (f, e) -> 
					Recpred (f, transl_expr_rec e)
  in transl_pred_rec p
             
(** A standard transformer for qualifiers *)						
						
let transl_patpred (v, nv) p =
  let rec transl_expr_rec pe =
    match pe.ppredpatexp_desc with
      | Ppredpatexp_int (n) ->
	        PPInt (n)
      | Ppredpatexp_any_int ->
          failwith "Any int qualfier feature is not available."     
      | Ppredpatexp_var (y) -> 
          let flat_or_nv y =
            let y = if y = v then nv else y in Exp.Id.create y
          in
	        PVar (List.map flat_or_nv y)
      | Ppredpatexp_mvar (y) ->
          failwith "Any variable qualifier feature is not available." 
      | Ppredpatexp_funapp (f, es) ->
	        PFunApp (f, List.map transl_expr_rec es)
      | Ppredpatexp_binop (e1, ops, e2) ->
	        PBinop (transl_expr_rec e1, transl_ops ops, transl_expr_rec e2)
      | Ppredpatexp_field (f, e1) ->
          PField (f, transl_expr_rec e1)
      | Ppredpatexp_proj (n, e1) ->
          PProj (n, transl_expr_rec e1)
			| Ppredpatexp_union (e1, e2) ->
					PUnion (transl_expr_rec e1, transl_expr_rec e2)
			| Ppredpatexp_concat (e1, e2) ->
					PConcat (transl_expr_rec e1, transl_expr_rec e2)
  in
  let rec transl_pred_rec pd =
    match pd.ppredpat_desc with
      | Ppredpat_true -> 
          PTrue
      | Ppredpat_atom (e1, rels, e2) ->
	        PAtom (transl_expr_rec e1, transl_rels rels, transl_expr_rec e2)
      | Ppredpat_not (p) -> 
          PNot (transl_pred_rec p)
      | Ppredpat_and (p1, p2) -> 
          PAnd (transl_pred_rec p1, transl_pred_rec p2)
      | Ppredpat_or (p1, p2) -> 
          POr (transl_pred_rec p1, transl_pred_rec p2)
			| Ppredpat_in (e1, e2) ->
					PIn (transl_expr_rec e1, transl_expr_rec e2)
			| Ppredpat_predrec (f, e) ->
				  PRecpred (f, transl_expr_rec e)
  in transl_pred_rec p

let gen_preds p =
  let rec gen_expr_rec pe =
    match pe with
      | PPInt (ns) ->
          List.map (fun c -> PInt (c)) ns  
      | PVar (ps) ->
          List.map (fun c -> Var (c)) ps
      | PFunApp (f, es) ->
          let ess = List.map gen_expr_rec es in
            List.map (fun e -> FunApp (f, e)) (List.lflap ess) 
      | PBinop (e1, ops, e2) ->
          let e1s = gen_expr_rec e1 in
          let e2s = gen_expr_rec e2 in
            List.tflap3 (e1s, ops, e2s) (fun c d e -> Binop (c, d, e))
      | PField (f, e1) ->
          let e1s = gen_expr_rec e1 in
            List.map (fun e -> Field(f, e)) e1s
      | PProj (n, e1) ->
          let e1s = gen_expr_rec e1 in
            List.map (fun e -> Proj(n, e)) e1s
			| PUnion (e1, e2) ->
					let e1s = gen_expr_rec e1 in
					let e2s = gen_expr_rec e2 in 
					List.tflap2 (e1s, e2s) (fun c d -> Union (c, d))
			| PConcat (e1, e2) ->
					let e1s = gen_expr_rec e1 in
					let e2s = gen_expr_rec e2 in 
					List.tflap2 (e1s, e2s) (fun c d -> Concat (c, d)) 
  in    
  let rec gen_pred_rec pd =
    match pd with
      | PTrue ->
          [True] 
      | PNot (p) ->  
          List.map (fun c -> Not (c)) (gen_pred_rec p) 
      | POr (p1, p2) ->
          let p1s = gen_pred_rec p1 in
          let p2s = gen_pred_rec p2 in
            List.tflap2 (p1s, p2s) (fun c d -> Or (c, d))
      | PAnd (p1, p2) ->
          let p1s = gen_pred_rec p1 in
          let p2s = gen_pred_rec p2 in
            List.tflap2 (p1s, p2s) (fun c d -> And (c, d))
      | PAtom (e1, rels, e2) ->      
          let e1s = gen_expr_rec e1 in
          let e2s = gen_expr_rec e2 in
            List.tflap3 (e1s, rels, e2s) (fun c d e -> Atom (c, d, e))
      | PIff (e1, p1) ->
          let e1s = gen_expr_rec e1 in
          let p1s = gen_pred_rec p1 in
            List.tflap2 (e1s, p1s) (fun c d -> Iff (c, d))
			| PIn (e1, e2) ->
					let e1s = gen_expr_rec e1 in
					let e2s = gen_expr_rec e2 in
					List.tflap2 (e1s, e2s) (fun c d -> In (c, d))
			| PRecpred (f, e) ->
					let es = gen_expr_rec e in
					List.map (fun e -> Recpred (f, e)) es
  in gen_pred_rec p

let ck_consistent patpred pred =
  let m = ref [] in
  let addm a = m := a::!m in
  let gtm (a, b) = 
    try List.find (fun (c, _) -> a = c) !m 
      with Not_found -> addm (a, b); (a,b) in
  let ckm (a, b) = (fun (_, d) -> b = d) (gtm (a, b)) in
  let rec ck_expr_rec pred pat =
    match (pred.ppredpatexp_desc, pat) with
      | (Ppredpatexp_var (_), Var(_))
      | (Ppredpatexp_any_int, PInt (_)) 
      | (Ppredpatexp_int (_), PInt (_)) ->
	        true
      | (Ppredpatexp_funapp (_, es), FunApp (_, el)) ->
          List.for_all2 ck_expr_rec es el
      | (Ppredpatexp_binop (e1, _, e2), Binop (e1', _, e2')) ->
          ck_expr_rec e1 e1' && ck_expr_rec e2 e2'  
      | (Ppredpatexp_field (_, e1), Field(_, e1')) ->
          ck_expr_rec e1 e1'
      | (Ppredpatexp_mvar (x), Var(y)) ->
          ckm (x, Exp.Id.to_string y)
      | (Ppredpatexp_proj (_, e), Proj (_, e')) ->
          ck_expr_rec e e'
			| (Ppredpatexp_union (e1, e2), Union (e1', e2')) ->
					ck_expr_rec e1 e1' && ck_expr_rec e2 e2'
			| (Ppredpatexp_concat (e1, e2), Concat (e1', e2')) ->
					ck_expr_rec e1 e1' && ck_expr_rec e2 e2'
      | _ -> assert false in
  let rec ck_pred_rec pred pat =
    match (pred.ppredpat_desc, pat) with
      | (Ppredpat_true, True) -> 
          true
      | (Ppredpat_atom (e1, _, e2), Atom (ee1, _, ee2)) ->
          ck_expr_rec e1 ee1 && ck_expr_rec e2 ee2
      | (Ppredpat_not (p), Not (pp)) -> 
          ck_pred_rec p pp
      | (Ppredpat_or (p1, p2), Or (pp1, pp2))
      | (Ppredpat_and (p1, p2), And (pp1, pp2)) -> 
          ck_pred_rec p1 pp1 && ck_pred_rec p2 pp2
			| (Ppredpat_in (e1, e2), In (ee1, ee2)) ->
				 ck_expr_rec e1 ee1 && ck_expr_rec e2 ee2
			| (Ppredpat_predrec (f1, e1), Recpred (f2, e2)) ->
				 ck_expr_rec e1 e2
      | _ -> assert false in
    ck_pred_rec patpred pred
     
let transl_pattern {Parsetree.pqual_pat_desc = (v, anno, pred)} nv =
	let preds = gen_preds (transl_patpred (v, nv) pred) in
  List.filter (fun p -> ck_consistent pred p) preds

(** Interface to parse qualifiers. name is the qualifer name and p is qualifer pattern *)
let transl_pattern_valu name ({Parsetree.pqual_pat_desc = (valu, anno, pred)} as p) =
  let normal_valu = "_V" in
  let num = ref 0 in
  let fresh name = incr num; name ^ (string_of_int !num) in
  let preds = transl_pattern p normal_valu in
  List.map (fun p -> (fresh name, normal_valu, p)) preds
