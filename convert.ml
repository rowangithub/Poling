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
open Parsetree
open Exp
open Assertions
open Commands

exception Undef_non_pure_expression 
exception Conversion_error of string * Location.t

let convert_fun s el loc = match s with
  | "@item"   -> E.fun1 Sfn_item (List.hd el)
  | "@sorted" -> E.fun1 Sfn_sorted (List.hd el)
  | "@hd"     -> E.fun1 Sfn_hd (List.hd el)
  | "@tl"     -> E.fun1 Sfn_tl (List.hd el)
  | "@set_of_list" -> E.fun1 Sfn_set_of_list (List.hd el)
  | "@can_return"  -> E.fun1 Sfn_can_return (List.hd el)
  | "@lt"         -> E.fun2 Sfn_list_lt (List.hd el) (List.hd (List.tl el))
  | "@subset"     -> E.fun2 Sfn_subset (List.hd el) (List.hd (List.tl el))
  | "@minus"      -> E.fun2 Sfn_set_minus (List.hd el) (List.hd (List.tl el))
  | "@list" -> E.list el
  | "@set"  -> E.set el
  | _ -> raise (Conversion_error ("Unknown built-in function "^s^".", loc))

let exp_to_bool e = match e with
  | Efun (Sfn_AND, _)
  | Efun (Sfn_OR, _)
  | Efun1 (Sfn_NOT, _)
  | Efun2 (Sfn_list_lt, _, _)
  | Efun2 (Sfn_subset, _, _)
  | Efun1 (Sfn_sorted, _)
  | Efun1 (Sfn_can_return, _) -> e
  | _ -> E.neq E.zero e

(** {2 Conversion to canonical form} *)

let rec convert_exp e = match e.pexp_desc with
  | Pexp_ident s -> E.id (Id.create s)
  | Pexp_num n -> E.num n
  | Pexp_bool b -> if b then E.one else E.zero
  | Pexp_prefix (op,e1) -> 
      let ce1 = convert_exp e1 in 
      begin match op with
	| "+" -> ce1
	| "-" -> E.sub E.zero ce1
	| _ -> assert false
      end
  | Pexp_infix (op,e1,e2) -> 
      let ce1 = convert_exp e1 in 
      let ce2 = convert_exp e2 in 
      if Pervasives.(=) op "+" then E.add ce1 ce2
      else if Pervasives.(=) op "^" then E.xor [ce1;ce2]
      else if Pervasives.(=) op "-" then E.sub ce1 ce2
      else assert false (*E.fun (sfn_of_string op) [ce1;ce2]*)
  | Pexp_cast(e1,_) -> convert_exp e1
  | Pexp_fun(i,el) -> convert_fun i (List.map convert_exp el) e.pexp_loc
  | Pexp_fcall _
  | Pexp_new _
  | Pexp_fld(_,_) -> raise Undef_non_pure_expression

(** [convert_exp_se exp statements] returns the statements
 required to evaluate [exp] appended to [statements] and a canonical
 expression ({!Exp.exp}) *)
let rec convert_exp_se rgnl e stmts = match e.pexp_desc with
  | Pexp_ident s -> (stmts, E.id (Id.create s))
  | Pexp_num n -> (stmts, E.num n)
  | Pexp_bool b -> (stmts, if b then E.one else E.zero)
  | Pexp_prefix (op,e1) -> 
      let (stmts, ce1) = convert_exp_se rgnl e1 stmts in 
      let ce = match op with
	| "+" -> ce1
	| "-" -> E.sub E.zero ce1
	| _ -> assert false
      in (stmts, ce)
  | Pexp_infix (op,e1,e2) -> 
      let (stmts, ce1) = convert_exp_se rgnl e1 stmts in 
      let (stmts, ce2) = convert_exp_se rgnl e2 stmts in 
      (stmts, if Pervasives.(=) op "+" then E.add ce1 ce2
              else if Pervasives.(=) op "^" then E.xor [ce1;ce2]
              else if Pervasives.(=) op "-" then E.sub ce1 ce2
	      else assert false)
  | Pexp_cast(e1,_) -> convert_exp_se rgnl e1 stmts
  | Pexp_fun(i,el) -> 
      let (stmts, cel) = convert_exp_list_se rgnl el stmts in 
      (stmts, convert_fun i cel e.pexp_loc)
  | Pexp_fcall(s,(idl,el)) -> 
      let id = Id.tempid () in
      let idl = List.map (fun (x,_) -> Id.create x) idl in
      let (stmts2, cel) = convert_exp_list_se rgnl el [] in
      (stmts2 @ mk_cmd (Cst_pfcall[(Some id,s,idl,cel)]) e.pexp_loc @ stmts, E.id id)
  | Pexp_new (_,e1) ->
      let id = Id.tempid() in  
      let (stmts2, e1) = convert_exp_se rgnl e1 [] in 
      (stmts2 @ mk_cmd (Cst_new(id,e1)) e.pexp_loc @ stmts, E.id id)
  | Pexp_fld (e,c) ->
      let id = Id.tempid () in 
      let (stmts2, ce) = convert_exp_se rgnl e [] in 
      (stmts2 @ mk_cmd (Cst_fldlookup(rgnl, id, ce, c)) e.pexp_loc @ stmts, E.id id)

and convert_exp_list_se rgnl el stmts = 
  List.fold
    (fun ae (stmts,cel) -> 
      let (stmts, ce) = convert_exp_se rgnl ae stmts in
      (stmts,ce::cel))
    (List.rev el)
    (stmts,[])

let cprop_atom ca = cprop_pure (Pure.one ca)

let convert_infix op e1 e2 = match op with 
  | "<"  -> E.ltn e1 e2      
  | "<=" -> E.leq e1 e2
  | ">"  -> E.ltn e2 e1
  | ">=" -> E.leq e2 e1
  | "==" -> E.eq  e1 e2
  | "!=" -> E.neq e1 e2
  | _ -> assert false

let p_exp_to_cprop e =
  let rec go e = match e.pexp_desc with
    | Pexp_prefix ("!",e1) ->
	let (cp1,cp2) = go e1 in
        (cp2,cp1)
    | Pexp_infix ("&&",e1,e2) -> 
	let (cp11,cp12) = go e1 in
	let (cp21,cp22) = go e2 in
	(cprop_star cp11 cp21, cprop_or cp12 (cprop_star cp11 cp22))
    | Pexp_infix ("||",e1,e2) ->
	let (cp11,cp12) = go e1 in
	let (cp21,cp22) = go e2 in
	(cprop_or cp11 (cprop_star cp12 cp21), cprop_star cp12 cp22)
    | Pexp_infix ((("<"|"<="|">"|">="|"=="|"!=") as op),e1,e2) -> 
      let (e1,e2) = (convert_exp e1, convert_exp e2) in
      let ca = convert_infix op e1 e2 in
      (cprop_atom ca, cprop_atom (E.bnot ca))
    | _ -> 
      let e = exp_to_bool (convert_exp e) in
      (cprop_atom e, cprop_atom (E.bnot e))
  in go e 

let convert_assume_exp rgnl e = 
  let rec go e = match e.pexp_desc with
    | Pexp_prefix ("!",e1) ->
	let (stmts1,stmts2) = go e1 in
        (stmts2,stmts1)
    | Pexp_infix ("&&",e1,e2) -> 
      let (stmts11,stmts12) = go e1 in 
      let (stmts21,stmts22) = go e2 in 
      (stmts11 @ stmts21,
       mk_nondet stmts12 (stmts11 @ stmts22) e.pexp_loc IdSet.empty)
    | Pexp_infix ("||",e1,e2) ->
      let (stmts11,stmts12) = go e1 in 
      let (stmts21,stmts22) = go e2 in 
      (mk_nondet stmts11 (stmts12 @ stmts21) e.pexp_loc IdSet.empty,
       stmts12 @ stmts22)
    | Pexp_infix ((("<"|"<="|">"|">="|"=="|"!=") as op),e1,e2) -> 
      let (stmts,e1) = convert_exp_se rgnl e1 [] in 
      let (stmts,e2) = convert_exp_se rgnl e2 stmts in 
      let ca = convert_infix op e1 e2 in
      let cond1 = mk_assume (ca) e.pexp_loc in
      let cond2 = mk_assume (E.bnot ca) e.pexp_loc in
      (stmts @ cond1, stmts @ cond2)
    | _ ->
      let (stmts,ce) = convert_exp_se rgnl e [] in
      let ce = exp_to_bool ce in
      let cond1 = mk_assume (ce) e.pexp_loc in
      let cond2 = mk_assume (E.bnot ce) e.pexp_loc in
      (stmts @ cond1, stmts @ cond2)
  in go e

(* Argument list is simply a node name. *)
let read_node argl loc = match argl with
  | []      -> list_link_tag
  | [(snode,loc)] ->
      let _ = Indpreds.add_ip_use (snode,-1,loc) in
      component_of_string ("." ^ snode) 
  | _::_::_ -> raise (Conversion_error ("Syntax error: Bad arguments to predicate.", loc))

let parse_indpred what argl el loc = (match what with
  | "list" ->
      let snode = read_node argl loc in
      let (e,f) = match el with
				| [e] -> (convert_exp e, E.id (Id.gensym_str_ex "VAL"))
				| [e;f] -> (convert_exp e, convert_exp f)
				| _ -> raise (Conversion_error ("Syntax error: Bad arguments to `list' predicate.", loc)) 
			in
      	Csp_listsegi(tag_default,SINGLE(snode,Fld.emp), e, E.zero, f, E.zero, Cem_PE, Dset.emp)
  | "lseg" | "lsegi" ->
      let snode = read_node argl loc in
      let (e,f,g) = match el with
				| [e;f] -> (convert_exp e, convert_exp f, E.id (Id.gensym_str_ex "VAL"))
				| [e;f;g] -> (convert_exp e, convert_exp f, convert_exp g)
				| _ -> raise (Conversion_error ("Syntax error: Bad arguments to `lseg' predicate.", loc)) 
			in
      	Csp_listsegi(tag_default,SINGLE(snode,Fld.emp), e, f, g, E.zero, Cem_PE, 
		   		if what="lseg" then Dset.from_list [f] else Dset.emp)
  | "dlseg" ->
      let (t1,t2) = match argl with
				| []      -> (dl_Rlink_tag, dl_Llink_tag)
				| [(t1,_);(t2,_)] -> (component_of_string t1, component_of_string t2)
				| _ -> raise (Conversion_error ("Syntax error: Bad arguments to `dlseg' predicate.", loc)) 
			in
      let (e1,f1,e2,f2) = match el with
				| [e1;f1;e2;f2] -> (convert_exp e1, convert_exp f1, convert_exp e2, convert_exp f2)
				| _ -> raise (Conversion_error ("Syntax error: Bad arguments to `dlseg' predicate.", loc)) 
			in
      	Csp_listsegi(tag_default,DOUBLE(t1,t2), e1, f1, e2, f2, Cem_PE, Dset.from_list [f1; e2])
  | "xlseg" ->
      let t1 = match argl with
				| []       -> (dl_Llink_tag)
				| [(t1,_)] -> component_of_string t1
				| _::_::_ -> raise (Conversion_error ("Syntax error: Bad arguments to `xlseg' predicate.", loc)) 
			in
      let (e1,f1,e2,f2) = match el with
				| [e1;f1;e2;f2] -> (convert_exp e1, convert_exp f1, convert_exp e2, convert_exp f2)
				| _ -> raise (Conversion_error ("Syntax error: Bad arguments to `xlseg' predicate.", loc)) 
			in
      	Csp_listsegi(tag_default,XOR t1, e1, f1, e2, f2, Cem_PE, Dset.from_list [f1; e2])
  | _ ->
      begin match argl with [] -> () | _::_ ->
        raise (Conversion_error ("Syntax error: Bad arguments to predicate.", loc))
      end;
      let _ = Indpreds.add_ip_use (what,List.length el,loc) 
			in Csp_indpred (tag_default, what, List.map convert_exp el)
		)

let convert_prop p loc = 
  let rec go p = match p with
  | Aprop_exp e -> fst (p_exp_to_cprop e)
  | Aprop_node (s,e,cel) ->
      let f (c,e) = (c, convert_exp e) in
      cprop_spred (spat_one (Csp_node (tag_default,s,convert_exp e, Fld.from_list (List.map f cel))))
  | Aprop_ifthenelse (e,p1,p2) ->
      let (cond1,cond2) = p_exp_to_cprop e in
      let px = cprop_star cond1 (go p1) in
      let py = cprop_star cond2 (go p2) in
      cprop_or px py
  | Aprop_star (p1,p2) -> cprop_star (go p1) (go p2)
  | Aprop_barbar (p2,p3) -> cprop_or (go p2) (go p3)
  | Aprop_box (rid,p) -> cprop_box rid (normalize_cprop (go p))
  | Aprop_indpred (what,argl,el,loc) -> (
		cprop_spred (spat_one (parse_indpred what argl el loc))
		)
  in (
		normalize_cprop (go p)
  )
let prop_to_ip_body p loc =
  let join (pl1,cf1) (pl2,cf2) = 
    let pl = Pure.conj pl1 pl2 in
    if Pure.is_false pl then None else 
    cform_star cf1 cf2 >>= fun cf ->
    Some (pl,cf) in
  let joinl xl1 xl2 = List.concat (List.map (fun x -> List.map_partial (join x) xl2) xl1) in
  let rec go = function
  | Aprop_exp e -> 
      begin match (fst (p_exp_to_cprop e)) with 
	| [] -> []
	| [((pl,_),PNil)] -> [(Pure.ptrue,((pl,spat_empty),PNil))]
	| _ -> assert false
      end
  | (Aprop_node _ | Aprop_indpred _) as sp ->
      let cp = convert_prop sp loc in
      List.map (fun cf -> (Pure.ptrue,cf)) cp
  | Aprop_ifthenelse (e,p1,p2) ->
      let (cond1,cond2) = p_exp_to_cprop e in
      let p1 = match cond1 with
	| [] -> []
	| [((pl,_),PNil)] -> 
            List.map (fun(guard,cf)->(Pure.conj pl guard,cf)) (go p1)
	| _ -> assert false in
      let p2 = match cond2 with
	| [] -> []
	| [((pl,_),PNil)] -> 
            List.map (fun(guard,cf)->(Pure.conj pl guard,cf)) (go p2)
	| _ -> assert false in
      p1 @ p2
  | Aprop_star (p1,p2) -> joinl (go p1) (go p2)
  | Aprop_barbar (p2,p3) -> 
     raise (Conversion_error ("Syntax error: Disjunction (||) is not allowed in user-defined predicates.", loc))
  | Aprop_box (rid,p) -> 
     [(Pure.ptrue,(uform_empty, PCons (rid, convert_prop p loc, PNil)))]
  in
  go p
