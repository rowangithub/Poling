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
open Indpreds
open Convert

(* -------------------------------------------------------------------------- *)
(** {2 Error handling} *)
(* -------------------------------------------------------------------------- *)

exception Vcgen_error of string * Location.t

let error_handler do_f =
  let res = 
    try 
      do_f ()
    with 
      | Conversion_error (s, loc) ->
	  print_endline ("\n" ^ Location.sprint loc ^ "Syntax error: " ^ s);
	  invalid_arg ("Errors found in input.")
      | Vcgen_error (s, loc) ->
	  print_endline ("\n" ^ Location.sprint loc ^ s);
	  invalid_arg ("Errors found in input.")
  in
  res

let error (s,loc) = 
  raise (Vcgen_error (s, loc))

let warning (s,loc) =
  print_endline ("\n" ^ Location.sprint loc ^ "Warning: " ^ s)

let argnum_error (s1,s2,l1,l2,loc) = 
  error (s1 ^ " has " ^ string_of_int (List.length l2) ^ s2 ^ " arguments, but "
	 ^ string_of_int (List.length l1) ^ " are expected.", loc)

(** [empty_or_error x (s1,s2,loc)] checks that the set [x] is empty. *) 
let empty_or_error x (s1,s2,loc) = 
  if not (IdSet.is_empty x) 
  then error (s1 ^ Id.to_string (IdSet.choose x) ^ s2, loc)


(* -------------------------------------------------------------------------- *)
(** {2 Set operations} *)
(* -------------------------------------------------------------------------- *)

let (++) = IdSet.union
let (--) = IdSet.diff
let (+) s x = s ++ (IdSet.singleton x)
let (-) s x = IdSet.remove x s
let set_of_list l =
  List.fold_left (+) IdSet.empty l
let union_map f l =
   List.fold (fun x ss -> (f x) ++ ss) l IdSet.empty

(* -------------------------------------------------------------------------- *)
(** {2 Environment} *)
(* -------------------------------------------------------------------------- *)

type typ = 
  | Pty_null
  | Pty_int
  | Pty_bool
  | Pty_void
  | Pty_tid
  | Pty_set
  | Pty_list
  | Pty_item
  | Pty_class of string 

let string_of_ty = function
  | Pty_null -> "0"
  | Pty_int -> "int"
  | Pty_bool -> "bool"
  | Pty_void -> "void"
  | Pty_tid -> "thread_id"
  | Pty_set -> "set"
  | Pty_list -> "list"
  | Pty_item -> "@item(...)"
  | Pty_class s -> s

let ty_of_string = function
  | "int" -> Pty_int
  | "bool" -> Pty_bool
  | "void" -> Pty_void
  | "thread_id" -> Pty_tid
  | "set" -> Pty_set
  | "list" -> Pty_list
  | s -> Pty_class s

(* User-defined structures *)

type class_item =
  { cla_fields: (typ * Location.t) StringMap.t
	; cla_tdesc : Predicate.t option
  ; cla_loc: Location.t }

type function_item =
  { fn_resty: typ
  ; param: (Id.t * typ * Location.t) list * (Id.t * typ * Location.t) list
  ; locals: (Id.t * typ * Location.t) list
  ; bound : IdSet.t  (** locals + params *)
  ; mutable calls: CompSet.t StringMap.t  
      (** map from fid to minimum set of resources 
          always acquired before calling fid *)
  ; mutable in_parallel_with: StringSet.t
  ; mutable requires: CompSet.t
  ; mutable writes_heap: bool
  ; mutable modif: IdSet.t
  ; mutable vars: IdSet.t
  ; pre: cprop
	; purespec: (string * Predicate.t)
  ; body: p_statement list
  ; post: cprop
	; effspec: (string * Predicate.t)
  ; fn_loc: Location.t }

type action_item =
  { act_id: string
  ; act_param: (string * Location.t) list
  ; act_locals: IdSet.t
  ; act_bound: IdSet.t         (** locals + params *)
  ; act_ctx: cprop
  ; act_pre: cprop
  ; act_post: cprop
  ; act_code: p_statement list 
      (** code to be inserted after each corresponding do...as action block *)
  ; act_loc: Location.t }

type resource_item =
  { owned: IdSet.t
  ; rvars: IdSet.t (** Free variables of the resource invariant *)
  ; res_locals : (Id.t * typ * Location.t) list
  ; res_cons : p_statement list
  ; res_interf : p_statement list option
  ; rinv : cprop option  (** Resource invariant *)
  ; ractions: action_item StringMap.t (** Resource actions *)
  ; res_loc: Location.t
	; res_def: Predicate.t }

type env =
  { mutable comments: string list
  ; classes: (string,class_item) Hashtbl.t
  ; mutable variables: (typ * Location.t) IdMap.t
  ; functions: (string,function_item) Hashtbl.t
  ; mutable env_funcs: string list 
     (** in reverse order wrt the original program *)
  ; resources: (component,resource_item) Hashtbl.t
  ; mutable env_rsrcs: component list 
     (** in reverse order wrt the original program *)
  ; mutable enable : IdSet.t * IdSet.t -> CompSet.t
  }

let initial_env () =
  let classes = Hashtbl.create 16 in
  Hashtbl.add classes "any" {cla_fields=StringMap.empty; 
		cla_tdesc = None; cla_loc=Location.none};
  { comments  = []
  ; classes   = classes
  ; variables = IdMap.add Id.mytid (Pty_tid, Location.none) 
                  (IdMap.add Id.tid (Pty_tid, Location.none) 
                     IdMap.empty)
  ; functions = Hashtbl.create 16
  ; env_funcs = []
  ; resources = Hashtbl.create 4
  ; env_rsrcs = []
  ; enable = fun _ -> assert false}

let lookup_class env x = Hashtbl.find env.classes x 

let lookup_function env x = Hashtbl.find env.functions x

let lookup_resource env x = Hashtbl.find env.resources x

let lookup_action res x = StringMap.find x res.ractions

let env_add_fun env x fi =
  if Hashtbl.mem env.functions x then 
    error ("Function " ^ x ^ " is already defined.", fi.fn_loc)
  else begin
    Hashtbl.add env.functions x fi;
    env.env_funcs <- x :: env.env_funcs
  end

let env_add_res env x ri =
  if Hashtbl.mem env.resources x then 
    error ("Resource " ^ string_of_component x ^ " is already defined.", ri.res_loc)
  else begin
    let ri_vars = ri.owned ++ ri.rvars in
    empty_or_error (IdSet.filter (fun x -> not (IdMap.mem x env.variables)) ri_vars)
	("Undeclared variable ", " in resource declaration.", ri.res_loc);
    Hashtbl.iter
      (fun y r ->
        empty_or_error (IdSet.inter r.owned ri_vars) 
	  ("Variable ", " is already owned by resource " ^ string_of_component y ^ ".", ri.res_loc);
        empty_or_error (IdSet.inter r.rvars ri.owned)
	  ("Variable ", " is already used by resource " ^ string_of_component y ^ ".", ri.res_loc)
      ) env.resources;
    Hashtbl.add env.resources x ri;
    env.env_rsrcs <- x :: env.env_rsrcs
  end


(* -------------------------------------------------------------------------- *)
(** {2  Type checking} *)
(* -------------------------------------------------------------------------- *)

let ty_unify = function
 | (ty1,ty2) when ty1=ty2 -> Some ty1
 | (Pty_null, ((Pty_int | Pty_tid | Pty_class _) as ty)) -> Some ty
 | (((Pty_int | Pty_tid | Pty_class _) as ty), Pty_null) -> Some ty
 | (Pty_class "any", (Pty_class _ as ty)) -> Some ty
 | ((Pty_class _ as ty), Pty_class "any") -> Some ty
 | (Pty_item, ((Pty_set | Pty_list) as ty)) -> Some ty
 | (((Pty_set | Pty_list) as ty), Pty_item) -> Some ty
 | (ty1,ty2) -> None

let expect_type loc ty1 ty2 =
  match ty_unify (ty1,ty2) with
  | Some _ -> ()
  | None ->
      error ("Type error: expecting type `" ^ string_of_ty ty1
             ^ "', but type `" ^ string_of_ty ty2 ^ "' found.", loc)

let type_of_var loc env x = 
  try fst (IdMap.find (Id.create x) env.variables)
  with Not_found -> 
    error ("Variable " ^ x ^ " has not been declared, or is out of scope.", loc)

let lookup_class_from_type loc env ty = match ty with
  | Pty_class t -> 
     begin 
       try lookup_class env t
       with Not_found -> error("Reference to undeclared class " ^ t ^ ".", loc)
     end
  | _ -> error ("Type error: expecting a pointer type.", loc)

let rec type_of_pexp env e = match e.pexp_desc with
  | Pexp_ident x ->  type_of_var e.pexp_loc env x
  | Pexp_num i -> if i=0 then Pty_null else Pty_int
  | Pexp_bool _ -> Pty_bool
  | Pexp_prefix (s,e1) -> 
      begin match s with
	| ("+" | "-") ->
	    check_pexp env Pty_int e1; Pty_int
	| ("!") ->
	    check_pexp env Pty_bool e1; Pty_bool
	| _ -> error("Error: found unknown unary operator (" ^ s ^ ").", e.pexp_loc)
     end
  | Pexp_infix (s,e1,e2) ->
      begin match s with
	| "+" ->
	    let ty1 = type_of_pexp env e1 in
	    let ty2 = type_of_pexp env e2 in
	    begin match ty1, ty2 with 
              | (Pty_null | Pty_int), (Pty_int | Pty_class _ | Pty_null) -> ty2
              | Pty_class _, (Pty_int | Pty_null) -> ty1
              | _, _ -> error("Type Error: Wrong argument types for + operator.", e.pexp_loc)
            end
	| "-" ->
	    let ty1 = type_of_pexp env e1 in
	    let ty2 = type_of_pexp env e2 in
	    begin match ty1, ty2 with 
              | (Pty_null | Pty_int), (Pty_int | Pty_null) -> ty2
              | Pty_class _, (Pty_int | Pty_null) -> ty1
              | Pty_class x, Pty_class y when x = y -> ty1
              | _, _ -> error("Type Error: Wrong argument types for - operator.", e.pexp_loc)
            end
	| ("*" | "/" | "%" | "^") ->
	    check_pexp env Pty_int e1;
	    check_pexp env Pty_int e2;
	    Pty_int
	| ("==" | "!=") ->
	    let ty1 = type_of_pexp env e1 in
	    let ty2 = type_of_pexp env e2 in
	    begin match ty_unify (ty1,ty2) with 
	      | None -> error ("Type error: Incompatible types in equality.", e.pexp_loc)
	      | Some _ -> ()
	    end;
	    Pty_bool
	| ("<" | "<=" | ">" | ">=") ->
	    check_pexp env Pty_int e1;
	    check_pexp env Pty_int e2;
	    Pty_bool
	| ("&&" | "||") ->
	    check_pexp env Pty_bool e1;
	    check_pexp env Pty_bool e2;
	    Pty_bool
	| _ -> error("Error: found unknown binary operator (" ^ s ^ ").", e.pexp_loc)
      end
  | Pexp_cast (e1,ty) ->
      let _ = type_of_pexp env e1 in
      ty_of_string ty
  | Pexp_fld (e1,s) ->
      let ty = type_of_pexp env e1 in
      let ci = lookup_class_from_type e.pexp_loc env ty in
      begin try fst (StringMap.find (string_of_component s) ci.cla_fields)
      with Not_found ->
	error("Type error: expression has type " ^ string_of_ty ty 
		^ ", which does not have field " ^ string_of_component s ^ ".", e1.pexp_loc)
      end
  | Pexp_new (s,e) ->
      let ty = Pty_class s in
      ignore (lookup_class_from_type e.pexp_loc env ty); 
      check_pexp env Pty_int e;
      ty
  | Pexp_fun(s,el) ->
      let check_one ty1 =
	match el with 
	| [x] -> check_pexp env ty1 x
	| _ -> error("Error: Function "^s^" expects one argument.", e.pexp_loc) in
      let check_one_any () =
	match el with 
	| [x] -> ignore (type_of_pexp env x)
	| _ -> error("Error: Function "^s^" expects one argument.", e.pexp_loc) in
      let check_two ty1 ty2 =
	match el with 
	| [x;y] ->
	    check_pexp env ty1 x;
	    check_pexp env ty2 y
	| _ -> error("Error: Function "^s^" expects two arguments.", e.pexp_loc) in
      begin match s with
	| "@item" -> check_one_any (); Pty_item
	| "@list" -> List.iter (check_pexp env Pty_list) el; Pty_list
	| "@set"  -> List.iter (check_pexp env Pty_set ) el; Pty_set
	| "@zero" -> List.iter (type_of_pexp env >> ignore) el; Pty_null
	| "@hd" -> check_one Pty_list; Pty_int
	| "@tl" -> check_one Pty_list; Pty_list
	| "@sorted" -> check_one Pty_list; Pty_bool
	| "@set_of_list" -> check_one Pty_list; Pty_set
	| "@sublist"    -> check_two Pty_list Pty_list; Pty_bool
	| "@list_minus" -> check_two Pty_list Pty_list; Pty_list
	| "@minus"      -> check_two Pty_set  Pty_set; Pty_set
	| "@subset"     -> check_two Pty_set  Pty_set; Pty_bool
	| "@can_return" -> check_one_any (); Pty_bool
	| _ -> error("Error: found unknown pure function (" ^ s ^ ").", e.pexp_loc)
      end
  | Pexp_fcall (fid,(vl,el)) ->
      let fi = 
	try lookup_function env fid
        with Not_found -> error ("Error: Function " ^ fid ^ " has not been defined.", e.pexp_loc) in
      check_pexp_list ("Function call", " reference", e.pexp_loc) env (fst fi.param) (List.map (fun (v,l) -> {pexp_desc=Pexp_ident v; pexp_loc=l}) vl);
      check_pexp_list ("Function call", " value", e.pexp_loc) env (snd fi.param) el;
      fi.fn_resty
 
and check_pexp env ty e =
  let ty1 = type_of_pexp env e in
  expect_type e.pexp_loc ty ty1

and check_pexp_list (s1,s2,loc) env tyl el =
  if List.length tyl = List.length el then
    List.iter2 (fun (_,ty,_) e -> check_pexp env ty e) tyl el
  else
    argnum_error(s1,s2,tyl,el,loc)

(** Check an action annotation. *)
let check_action0 env rid actid loc =
  let ri =
    try lookup_resource env rid with Not_found -> 
    error ("Error: The resource "^string_of_component rid^" has not been declared.", loc) in
  if actid <> "" then begin
    try ignore (lookup_action ri actid) with Not_found ->
    error ("Error: The definition of resource "^string_of_component rid^" does not have the action "^actid^".", loc)
  end

(** Check an action annotation. *)
let check_action env rid actid argl loc =
  let ri =
    try lookup_resource env rid with Not_found -> 
    error ("Error: The resource "^string_of_component rid^" has not been declared.", loc) in
  if actid <> "" then begin
    let ai = 
      try lookup_action ri actid with Not_found ->
      error ("Error: The definition of resource "^string_of_component rid^" does not have the action "^actid^".", loc) in
    if List.length ai.act_param <> List.length argl then
      argnum_error ("Action annotation","",ai.act_param,argl,loc)
  end


(* Make function call code *)
let mk_fcall_stm loc (reso,f,args) = 
  let e = {pexp_desc = Pexp_fcall(f,args); pexp_loc = loc} in
  match reso with
    | None -> {pstm_desc = Pstm_exp(e); pstm_loc = loc}
    | Some x -> {pstm_desc= Pstm_assign(x,Some e); pstm_loc = loc}

(** Check variables in the proposition [p] are defined. *)
let tycheck_cprop env loc s p = 
  let g v =
    if not (IdMap.mem v env.variables) then
      error ("Error: The " ^ s ^ " contains variable " ^ Id.to_string v
      	^ " is undeclared or out of scope.", loc) in
  IdSet.iter g (fv_norm_cprop p)

(** Simple type checking *)
let tycheck_cmd env fn_resty c =
  let rec go_stmt in_loop s = match s.pstm_desc with
    | Pstm_comment _ -> ()
    | Pstm_exp e -> 
	begin match type_of_pexp env e with
	| Pty_void -> ()
	| ty -> warning("The program ignores value of type `" ^ string_of_ty ty ^ "'.", s.pstm_loc)
	end
    | Pstm_assign(v,None) -> ignore (type_of_var s.pstm_loc env v)
    | Pstm_assign(v,Some e) -> check_pexp env (type_of_var s.pstm_loc env v) e
    | Pstm_fldassign l ->
	List.iter 
	  (fun (e1,c,e2) -> check_pexp env 
	     (type_of_pexp env {pexp_desc=Pexp_fld(e1,c); pexp_loc=s.pstm_loc}) e2)
	  l
    | Pstm_dispose (e1,e2) ->
        ignore (lookup_class_from_type e1.pexp_loc env (type_of_pexp env e1));
        check_pexp env Pty_int e2
    | Pstm_block sl -> List.iter (go_stmt in_loop) sl
    | Pstm_assume e -> check_pexp env Pty_bool e
    | Pstm_if (eo,s1,s2) ->
	(match eo with None -> () | Some e -> check_pexp env Pty_bool e); 
        go_stmt in_loop s1;
	go_stmt in_loop s2
    | Pstm_while (po,eo,s1) ->
	(match po with None -> () | Some p -> tycheck_cprop env s.pstm_loc "loop invariant" (convert_prop p s.pstm_loc));
	(match eo with None -> () | Some e -> check_pexp env Pty_bool e);
        go_stmt true s1
    | Pstm_withres (rid,e,s,actid,el) ->
	check_pexp env Pty_bool e;
	check_action env rid actid el s.pstm_loc;
	List.iter (type_of_pexp env >> ignore) el;
	go_stmt in_loop s
    | Pstm_interfere (rid,actid) ->
	check_action0 env rid actid s.pstm_loc
    | Pstm_action (s,rid,actid,el) ->
	check_action env rid actid el s.pstm_loc;
	List.iter (type_of_pexp env >> ignore) el;
	go_stmt in_loop s
    | Pstm_parblock par_calls ->
	List.iter (mk_fcall_stm s.pstm_loc >> go_stmt false) par_calls
    | Pstm_return eo ->
	begin match eo with 
	| None -> 
	    if fn_resty <> Pty_void then 
	      error ("Error: The return type of this function is " ^ string_of_ty fn_resty, s.pstm_loc)
	| Some e -> check_pexp env fn_resty e 
	end
    | Pstm_break ->     if not in_loop then error ("Syntax error: `break' must be inside a loop.", s.pstm_loc) 
    | Pstm_continue ->  if not in_loop then error ("Syntax error: `continue' must be inside a loop.", s.pstm_loc) 
  in
  List.iter (go_stmt false) c


let tycheck_res env ri =
  let gvars = env.variables in
  let add_var r (v,ty,loc) =
    if IdMap.mem v r then error ("Variable " ^ Id.to_string v ^ " has already been defined and is in scope.", loc)
    else IdMap.add v (ty,loc) r in
  let ff x res = List.fold_left add_var res x in
  (* add locals *)
  env.variables <- ff ri.res_locals env.variables; 
  tycheck_cmd env Pty_void ri.res_cons;
  (* remove locals + params *)
  env.variables <- gvars;
  begin match ri.res_interf with 
  | None -> () 
  | Some c -> tycheck_cmd env Pty_void c
  end

let tycheck_fun env fi =
  let gvars = env.variables in
  let add_var r (v,ty,loc) =
    if IdMap.mem v r then error ("Variable " ^ Id.to_string v ^ " has already been defined and is in scope.", loc)
    else IdMap.add v (ty,loc) r in
  let ff x res = List.fold_left add_var res x in
  (* add params *)
  env.variables <- ff (snd fi.param) (ff (fst fi.param) gvars);
  tycheck_cprop env fi.fn_loc "precondition" fi.pre;
  (* add Result *) 
  if fi.fn_resty <> Pty_void then
    env.variables <- 
      add_var env.variables (Id.create "Result",fi.fn_resty,Location.none);
  tycheck_cprop env fi.fn_loc "postcondition" fi.post;
  (* add locals *)
  env.variables <- ff fi.locals env.variables; 
  tycheck_cmd env fi.fn_resty fi.body;
  (* remove locals + params *)
  env.variables <- gvars

(* -------------------------------------------------------------------------- *)
(** {2 Translation to intermediate form} *)
(* -------------------------------------------------------------------------- *)

(* translate an invariant to a proposition *)
let inv_to_cprop po loc = match po with
  | None -> cprop_empty
  | Some p -> convert_prop p loc

type mod_var_req_modh =
  { md: IdSet.t   (** Variables modifies *)
  ; vr: IdSet.t   (** Variables accessed *)
  ; rq: CompSet.t (** Requires resources *)
  ; mh: bool      (** Modifies heap? *) }

let mvr_empty =
  { md = IdSet.empty; vr = IdSet.empty;
    rq = CompSet.empty; mh = false }

let (++.) mvr1 mvr2 =
  { md = mvr1.md ++ mvr2.md;
    vr = mvr1.vr ++ mvr2.vr;
    rq = CompSet.union mvr1.rq mvr2.rq;
    mh = mvr1.mh || mvr2.mh }

let mvr_union_map f l =
   List.fold_left (fun mvr x -> mvr ++. f x) mvr_empty l

let mvr_exp env e = 
  let rec go e = match e.pexp_desc with
    | Pexp_new _
    | Pexp_bool _
    | Pexp_num _ -> mvr_empty
    | Pexp_ident x ->
	let x = Id.create x in
	if Id.is_existential x then mvr_empty
	else {mvr_empty with vr = IdSet.singleton x}
    | Pexp_cast (e1,_)
    | Pexp_prefix (_,e1)
    | Pexp_fld (e1,_) -> go e1
    | Pexp_infix (_,e1,e2) -> go e1 ++. go e2
    | Pexp_fun (i,el) -> mvr_union_map go el
    | Pexp_fcall (fid,(vl,el)) ->
	let fi = lookup_function env fid in
	let md = List.fold (fun (v,_) -> IdSet.add (Id.create v)) vl IdSet.empty in
	{ mvr_empty with md = md; vr = md }
	++. mvr_union_map go el
	++. {md = fi.modif; vr = fi.vars; rq = fi.requires; mh = fi.writes_heap} in
  let mvr = go e in
  { mvr with rq = env.enable(mvr.md, mvr.vr) }

(** (modified, vars, required) for a sequence of statements *)
let mvr_body env stl =
  let f_e e = mvr_exp env e in
  let f_oe e = match e with None -> mvr_empty | Some e -> mvr_exp env e in
  let f_p p = {mvr_empty with 
               vr = fv_norm_cprop (inv_to_cprop p Location.none)} in
  let rec f st = match st.pstm_desc with
    | Pstm_exp e -> mvr_exp env e
    | Pstm_assign (i,oe) ->
	let id = IdSet.singleton (Id.create i) in
	f_oe oe ++. {mvr_empty with md=id; vr=id}
    | Pstm_fldassign l ->
	List.fold_left 
	  (fun res (e1,_,e2) -> res ++. mvr_exp env e1 ++. mvr_exp env e2)
	  {mvr_empty with mh=true} l
    | Pstm_dispose (e1,e2) -> {(mvr_exp env e1 ++. mvr_exp env e2) with mh=true}
    | Pstm_block stl -> mvr_union_map f stl
    | Pstm_assume e -> f_e e
    | Pstm_if (a,st1,st2) -> f_oe a ++. f st1 ++. f st2
    | Pstm_while (inv,a,st) -> f_oe a ++. f_p inv ++. f st
    | Pstm_withres (rid,a,st,aid,argl) ->
        let ri = lookup_resource env rid in
        let mvr = f st ++. f_e a in
	(* calculate rq properly *)
	let mvr = { mvr with rq = env.enable(mvr.md, mvr.vr) } in
	let md = mvr.md -- ri.owned in
        {md = md; vr = md ++ (mvr.vr -- ri.rvars); 
	 rq = CompSet.remove rid mvr.rq; mh=mvr.mh}
    | Pstm_action (st,rid,aid,argl) ->
        f st
    | Pstm_parblock par_calls ->
	mvr_union_map f (List.map (mk_fcall_stm st.pstm_loc) par_calls)
    | Pstm_return eo -> f_oe eo
    | (Pstm_comment _ | Pstm_interfere _ | Pstm_break | Pstm_continue) ->
        mvr_empty
  in 
  let mvr = mvr_union_map f stl in
  { mvr with rq = env.enable(mvr.md, mvr.vr) }

let (+++) sm (i,s) =
  try let s' = StringMap.find i sm
      in StringMap.add i (CompSet.inter s s') sm
  with Not_found -> StringMap.add i s sm

let (++++) sm1 sm2 =
  StringMap.fold (fun i acq sm -> sm +++ (i,acq)) sm1 sm2

(* initial call graph: only functions called directly *)
let initial_call_graph env _ fi  =
  let check_fcall fid (vl,el) loc =
    let fi = 
      try lookup_function env fid
      with Not_found ->
        error ("Function " ^ fid ^ " has not been declared.", loc) in
    if List.length vl <> List.length (fst fi.param) then
      argnum_error ("Function call", " reference", fst fi.param, vl, loc);
    if List.length el <> List.length (snd fi.param) then
      argnum_error ("Function call", " value", snd fi.param, el, loc) in
  let check_withres rid loc =
    try ignore (lookup_resource env rid)
    with Not_found -> 
     error ("Resource " ^ string_of_component rid ^ " has not been defined.", 
            loc) in
  let add_fcall fid acquired = fi.calls <- fi.calls +++ (fid,acquired) in
  let rec f_e acquired e = match e.pexp_desc with
    | Pexp_new _
    | Pexp_num _ 
    | Pexp_bool _ 
    | Pexp_ident _ -> ()
    | Pexp_cast (e1,_)
    | Pexp_prefix (_,e1)
    | Pexp_fld (e1,_) -> f_e acquired e1
    | Pexp_infix (_,e1,e2) -> f_e acquired e1; f_e acquired e2
    | Pexp_fun (_,el) ->  List.iter (f_e acquired) el
    | Pexp_fcall (i,(vl,el)) ->
	check_fcall i (vl,el) e.pexp_loc;
	add_fcall i acquired;
        begin match List.filter (fun (x,_) -> IdMap.mem (Id.create x) env.variables) vl with
	  | [] -> ()
	  | (x,loc)::_ -> error ("Global variable " ^ x ^ " cannot be passed by reference.", loc)
	end;
	List.iter (f_e acquired) el in
  let rec check_pure e = match e.pexp_desc with
    | Pexp_new _
    | Pexp_fld _ 
    | Pexp_fcall _ -> error ("Arguments of a parallel call must be pure.",e.pexp_loc)
    | Pexp_num _ 
    | Pexp_bool _ 
    | Pexp_ident _ -> ()
    | Pexp_cast (e1,_)
    | Pexp_prefix (_,e1) -> check_pure e1;
    | Pexp_infix (_,e1,e2) -> check_pure e1; check_pure e2
    | Pexp_fun (_,el) ->  List.iter check_pure el in
  let f_eo acquired eo = match eo with 
    | None -> ()
    | Some e -> f_e acquired e in
  let rec f acquired st = match st.pstm_desc with
    | Pstm_if (a,st1,st2) -> f_eo acquired a; f acquired st1; f acquired st2
    | Pstm_while (_,a,st) -> f_eo acquired a; f acquired st
    | Pstm_block stl -> List.iter (f acquired) stl
    | Pstm_withres (rid,_,st,_,_) ->
        check_withres rid st.pstm_loc;
	f (CompSet.add rid acquired) st
    | Pstm_action (st,_,_,_) -> f acquired st
    | Pstm_parblock par_calls ->
	List.iter (fun (reso,i,args) ->
	  check_fcall i args st.pstm_loc;
	  add_fcall i acquired;
	  List.iter check_pure (snd args)) par_calls
    | Pstm_comment _
    | Pstm_interfere _
    | Pstm_break
    | Pstm_continue
    | Pstm_assign (_,None)
    | Pstm_return None -> ()
    | Pstm_assume e
    | Pstm_exp e
    | Pstm_return (Some e)
    | Pstm_assign (_,Some e)  -> f_e acquired e 
    | Pstm_dispose (e1,e2) -> f_e acquired e1; f_e acquired e2 
    | Pstm_fldassign l ->
        List.iter (fun (e1,_,e2) -> f_e acquired e1; f_e acquired e2) l
  in List.iter (f CompSet.empty) fi.body

(* compute the entire call graph of fi assuming _.calls in stop are complete *)
let call_graph_fid env fi stop =
  let stopr = ref stop in
  let rec f acquired fi =
    StringMap.fold
    (fun fid' acquired' sm ->
       let fi' = lookup_function env fid' in
       let acq = CompSet.union acquired acquired' in
       let deep_calls =
         if StringSet.mem fid' !stopr
         then StringMap.map (CompSet.union acq) fi'.calls
         else begin
           stopr := StringSet.add fid' !stopr;
           f (CompSet.union acquired acquired') fi'
         end in
       sm ++++ (deep_calls +++ (fid',acq)))
    fi.calls StringMap.empty in
  f CompSet.empty fi

(* entire call graph of all the functions *)
let calc_call_graph env =
  let fil = env.functions in
  let _ = Hashtbl.iter (initial_call_graph env) fil in
  let stopr = ref StringSet.empty in
  let f x fi =
    fi.calls <- call_graph_fid env fi !stopr;
    stopr := StringSet.add x !stopr in
  Hashtbl.iter f fil

(* create a function  enable (mS aS) returning the resources required to modify
   mS and access aS *)
let mk_enable_fun env =
  let m = ref IdMap.empty in
  let find id =
    try IdMap.find id !m
    with Not_found -> (CompSet.empty, CompSet.empty) in
  let add_mods rid id =
    let (mods,vars) = find id in
     m := IdMap.add id (CompSet.add rid mods,vars) !m  in
  let add_vars rid id =
    let (mods,vars) = find id in
    m := IdMap.add id (mods,CompSet.add rid vars) !m in
  let f x ri =
    IdSet.iter (add_mods x) ri.rvars;
    IdSet.iter (add_vars x) ri.owned in
  Hashtbl.iter f env.resources;
  let enable (mS,aS) =
    IdSet.fold (fun id -> CompSet.union (fst (find id))) mS
      (IdSet.fold (fun id -> CompSet.union (snd (find id))) aS CompSet.empty)
  in enable

(* calculates the modified and vars and required set for each function *)
let calc_mvr env =
  let enable = mk_enable_fun env in
  env.enable <- enable; 
  let shallow_mod _ fi =
    let mvr = mvr_body env fi.body in
    let fv_spec = (fv_norm_cprop fi.pre ++ fv_norm_cprop fi.post) in
    fi.modif <- mvr.md -- fi.bound;
    fi.vars <- (mvr.vr ++ fv_spec) -- fi.bound;
    fi.requires <- CompSet.union mvr.rq 
                     (enable (IdSet.empty, fv_spec -- fi.bound));
    fi.writes_heap <- mvr.mh;
  in Hashtbl.iter shallow_mod env.functions;
  let deep_mod _ fi =
    let call_set fid' fi' =
      StringMap.fold (fun fid _ s -> StringSet.add fid s) fi'.calls 
        (StringSet.singleton fid') in
    let in_par_with loc = function
      | Pstm_parblock par_calls ->
          let add_call_set_to_function cs f = 
            let fi = lookup_function env f in 
            fi.in_parallel_with <- StringSet.union fi.in_parallel_with cs in
	  let rec go cs1 csl2 = match csl2 with 
	    | [] -> ()
	    | cs::csl3 -> 
                StringSet.iter (add_call_set_to_function cs) cs1;
                List.iter (StringSet.iter (add_call_set_to_function cs)) csl3;
		go (StringSet.union cs1 cs) csl3 in
	  go StringSet.empty (List.map (fun (_,f,_) -> call_set f (lookup_function env f)) par_calls)
      | _ -> ()
    in Parsetree.iter in_par_with fi.body;
    let owned_set acq =
      CompSet.fold (fun rid s -> (lookup_resource env rid).owned ++ s) acq IdSet.empty in
    let modif =
      StringMap.fold
      (fun fid acq modif -> modif ++ ((lookup_function env fid).modif -- owned_set acq))
      fi.calls fi.modif
    and vars =
      StringMap.fold
      (fun fid acq vars -> vars ++ ((lookup_function env fid).vars -- owned_set acq))
      fi.calls fi.vars
    and requires =
      StringMap.fold
      (fun fid acq req -> CompSet.union req (CompSet.diff (lookup_function env fid).requires acq))
      fi.calls fi.requires
    and writes_heap =
      StringMap.fold
      (fun fid acq writes_heap -> writes_heap || (lookup_function env fid).writes_heap)
      fi.calls fi.writes_heap
    in fi.requires <- requires;
       fi.modif <- modif;
       fi.vars <- vars;
       fi.writes_heap <- writes_heap in
    Hashtbl.iter deep_mod env.functions

(** Convert a p_action to an action_item *)
let process_action env (s,params,r,p,q,code,loc) acts = 
  if StringMap.mem s acts then
    error ("Action " ^ s ^ " is already defined.", loc);
  let r = convert_prop r loc in
  let p = convert_prop p loc in
  let q = convert_prop q loc in
  let fv = fv_norm_cprop r ++ fv_norm_cprop p ++ fv_norm_cprop q in
  let exfv = prop_exfv r (prop_exfv p (prop_exfv q IdSet.empty)) in
  let bound = set_of_list (List.map (fst >> Id.create) params) ++ exfv in
  empty_or_error 
    (IdSet.filter (fun x -> not (IdMap.mem x env.variables)) (fv -- bound))
    ("Variable ", " must either be global or bound by the action.", loc);
  tycheck_cmd env (Pty_void) code;
  StringMap.add s
    { act_id=s; act_param=params; act_locals=exfv; act_bound=bound; 
      act_ctx=r; act_pre=p; act_post=q; act_code=code; act_loc=loc}
    acts

let add_poss_link_field x =
  let x = Misc.component_of_string x in
  if List.exists (fun y -> x==y) (!Misc.possible_link_fields) then ()
  else Misc.possible_link_fields := x :: !Misc.possible_link_fields

let rec process_declarations iteml env =
  (* First pass -- class definitions and global variables *)
  let go1 = function
    | Pdec_comment s -> env.comments <- s::env.comments;
    | Pdec_class (sid,tdesc,fields,loc) ->
	let fld = List.fold_left (fun res (x,ty,loc) ->
	  if StringMap.mem x res then error ("Error: Duplicate definition of field " ^ x ^ " in class " ^ sid ^ ".", loc);
	  if ty=sid then add_poss_link_field x;
	  StringMap.add x (ty_of_string ty,loc) res) StringMap.empty fields in
	let tdesc = match tdesc with 
		| Some tdesc -> (Some (Qualdecl.transl_patpred_single tdesc) )
		| _ -> (None) in
	Hashtbl.add env.classes sid {cla_fields = fld; cla_tdesc = tdesc; cla_loc = loc}
    | Pdec_var (x,ty,loc) ->
	let id = Id.create x in
	if IdMap.mem id env.variables then 
	  error ("Global variable " ^ x ^ " is already defined.", loc);
	env.variables <- IdMap.add id (ty_of_string ty,loc) env.variables
    | Pdec_fun _ | Pdec_resource _ | Pdec_indpred _ -> () in
  (* Second pass -- predicates, functions, resources *)
  let go2 = function
    | (Pdec_class _ | Pdec_var _ | Pdec_comment _) -> ()
    | Pdec_fun (fid,resty,param,(pre,post,purespec,effspec),(locals,body),loc) ->
        let pre = inv_to_cprop pre loc in
	let post = inv_to_cprop post loc in
	let f = List.map (fun (x,y,loc) -> (Id.create x,ty_of_string y,loc)) in
	let locals = f locals in
	let param = (f (fst param), f (snd param)) in
        let bound = 
          (List.map (fun (x,_,_) -> x) >> set_of_list) (locals @ fst param @ snd param) in
	env_add_fun env fid
	    {fn_resty=ty_of_string resty; param=param; locals=locals; bound=bound;
	     calls=StringMap.empty; in_parallel_with=StringSet.empty; writes_heap=false;
	     requires=CompSet.empty; modif=IdSet.empty; vars=IdSet.empty;
	     pre=pre; 
			 purespec= (match purespec with 
				| Some (r, purespec) -> (r,Qualdecl.transl_patpred_single purespec) 
				| _ -> ("", Predicate.True)); 
			 body=body; post=post; 
			 effspec= (match effspec with
				| Some (r,effspec) -> (r,Qualdecl.transl_patpred_single effspec) 
				| _ -> ("", Predicate.True)); 
			 fn_loc=loc}
    | Pdec_resource (rid,owned,inv,(locals,body),interf,actions,def,loc) ->
	let rec modvars r st = match st.pstm_desc with
	  | (Pstm_interfere _ | Pstm_assume _ | Pstm_exp _ | Pstm_fldassign _ | Pstm_dispose _
	    | Pstm_break | Pstm_continue | Pstm_return _ | Pstm_comment _) -> r
	  | Pstm_assign (i,_) -> IdSet.add (Id.create i) r
	  | Pstm_block stl -> List.fold_left modvars r stl
	  | Pstm_if (_,st1,st2) -> modvars (modvars r st1) st2
	  | Pstm_while (_,_,st) -> modvars r st
	  | Pstm_withres _ | Pstm_action _ | Pstm_parblock _ -> r (* TODO *) in 
        let owned = set_of_list (List.map (fst >> Id.create) owned) in
        let (rinv,rvars) = match inv with
	  | None ->
	      let locals = set_of_list (List.map (fun (x,_,_) -> Id.create x) locals) in
	      (None, IdSet.diff (List.fold_left modvars IdSet.empty body) locals)
	  | Some inv ->
	      let inv = convert_prop inv loc in
	      (Some inv, fv_norm_cprop inv) in
        let acts = List.fold (process_action env) actions StringMap.empty in 
	let locals = List.map (fun (x,y,loc) -> (Id.create x,ty_of_string y,loc)) locals in
	env_add_res env rid
          {owned=owned; rvars=rvars; rinv=rinv; ractions=acts;
	   res_locals = locals; res_cons = body; res_interf=interf; res_loc=loc; 
			res_def = Qualdecl.transl_patpred_single def}
    | Pdec_indpred (pid,param,body,loc) ->
	let param = List.map (fst >> Id.create) param in
	let body = prop_to_ip_body body loc in
	let node = List.length param = 3 && (match body with
	  | [(x,((_,sl),PNil))] when Pure.is_true x ->
             begin match spat_fold_spred (fun x r -> x::r) sl [] with
	       | [Csp_node(_,_,e,_)] -> e == E.id (List.hd param)
	       | _ -> false
	     end
          | _ -> false) in
	begin try
	  add_ip_decl
            {ip_id=pid;ip_args=param;ip_body=body;ip_node=node;ip_loc=loc}
	with Indpred_error (s,loc) -> error (s,loc) end
  in 
  List.iter go1 iteml;
  List.iter go2 iteml;
  (* Type checking *)
  let check_ty s (ty,loc) = match ty with
    | Pty_class t ->
	begin 
	  try ignore (lookup_class env t)
	  with Not_found -> 
            error("The type of " ^ s ^ " refers to the undeclared class " 
                  ^ t ^ ".", loc)
	end
    | _ -> ()
  in
  Hashtbl.iter (fun _ ci -> StringMap.iter (fun x -> check_ty ("field " ^ x)) ci.cla_fields) env.classes;
  IdMap.iter (fun x -> check_ty ("global variable " ^ Id.to_string x))
    env.variables;
  List.iter (lookup_resource env >> tycheck_res env) (List.rev env.env_rsrcs);
  List.iter (lookup_function env >> tycheck_fun env) (List.rev env.env_funcs)

open Format

let pp_component pp c = 
  Format.pp_print_string pp (string_of_component c)

let rec pp_seq pp f = function
  | [] -> ()
  | [x] -> pp f x
  | x::l -> pp f x; Format.pp_print_char f ','; pp_seq pp f l

let pp_call_item pp (fid,acq) =
  begin match CompSet.elements acq with
  | [] -> ()
  | l -> 
      Format.pp_print_char pp '{';
      pp_seq pp_component pp l;
      Format.pp_print_char pp '}'
  end;
  Format.pp_print_string pp fid

let pp_set x pp f s = match s with
  | [] -> ()
  | l ->
      Format.pp_print_string f x;
      pp_seq pp f l

let print_env pp env =
  let f fid fi =
    Format.pp_print_string pp "FUNCTION ";
    Format.pp_print_string pp fid;
    pp_set " CALLS" pp_call_item pp (StringMap.fold (fun fid acq l -> (fid,acq)::l) fi.calls []);
    pp_set " IN_PARALLEL_WITH" Format.pp_print_string pp (StringSet.elements fi.in_parallel_with);
    pp_set " REQUIRES" pp_component pp (CompSet.elements fi.requires);
    pp_set " MODIFIES" pp_ident pp (IdSet.elements fi.modif);
    pp_set " READS" pp_ident pp (IdSet.elements fi.vars) in
  Hashtbl.iter f env.functions

(* star resource invariants *)
let desugar_rsrc_initzers iteml env =
  let rsrc_invs =
    List.fold_right
      (fun item invs -> match item with
	 | Pdec_resource(rid,prots,Some inv,([],[]),_,actions,_,loc) -> (
	     let can_inv = convert_prop inv loc in
	     cprop_star can_inv invs)
	 | _ -> invs)
      iteml
      cprop_empty
  (* if absent, extend iteml with an init function consisting of the
     resource initializers *)
  in (rsrc_invs,
      if (List.exists (function Pdec_fun("init",_,_,_,_,_) -> true | _ -> false) iteml) 
	|| not (List.exists (function Pdec_resource _ -> true | _ -> false) iteml)
      then iteml
      else (Pdec_fun("init", "void",
	 	     ([],[]),
	 	     (Some a_prop_empty, Some a_prop_empty, None, None),
	 	     ([],[]),
	 	     Location.none)
	    :: iteml))

let compose_init_and_main rsrc_invs env =
  let init_post =
    try 
      let init_fun = lookup_function env "init" in
      Hashtbl.replace env.functions "init" {init_fun with post = (cprop_star init_fun.post rsrc_invs)};
      init_fun.post
    with Not_found -> cprop_empty in
  try
    let main_fun = lookup_function env "main" in
    env_add_fun env "compose_init_main" 
      {fn_resty=Pty_void;
       pre= init_post;
       body= [];
       post= main_fun.pre;
       param= [],[];
       locals= [];
       bound= IdSet.empty;
       calls= StringMap.empty;
       in_parallel_with= StringSet.empty;
       requires= CompSet.empty;
       writes_heap = false;
       modif= IdSet.empty;
       vars= IdSet.empty;
       fn_loc= Location.none;
			 purespec = ("", Predicate.True);
			 effspec = ("", Predicate.True)}
  with Not_found ->
    () (*pp "// No main() found.@."*)

let check_variable_conditions env =
  let check_main_req_empty () =
    try (* check that main requires no resources *)
      let main_fun = lookup_function env "main" in
      if not (CompSet.is_empty main_fun.requires) then 
	error ("Function main requires resource " ^ string_of_component (CompSet.choose main_fun.requires)
		^ " in order to execute.", main_fun.fn_loc)
    with Not_found -> () in
  let check_init_sequential () =
    try (* check that init is sequential *)
      let init_fun = lookup_function env "init" in
      Parsetree.iter
	(fun loc -> function
	   | Pstm_withres _ | Pstm_action _ | Pstm_parblock _ ->
	       error ("The body of init must be sequential.", loc)
	   | _ -> ()) init_fun.body;
      if not (StringMap.is_empty init_fun.calls) then
	error ("Function init cannot call other functions.", init_fun.fn_loc)
    with Not_found -> () in
  let rec check_par_fcalls loc = function
  | Pstm_parblock par_calls ->
      let get_data (reso,fid,args) =
	let fi = lookup_function env fid in
	let mvr = mvr_body env [mk_fcall_stm loc (reso,fid,args)] in
	let fv = fv_norm_cprop fi.pre ++ fv_norm_cprop fi.post in
	(fid,mvr,fv) in
      let check (fid,mvr,fv) (fid',mvr',fv') =
	 empty_or_error (IdSet.inter mvr.md fv')
	   ("Function " ^ fid ^ " modifies ",
	    " which appears in the spec of " ^ fid' ^ ".", loc);
         empty_or_error (IdSet.inter mvr.md mvr'.vr)
	   ("RACE: Function " ^ fid ^ " modifies variable ", 
	    " and function " ^ fid' ^ " accesses it.", loc) in
      let rec go xl yl = match yl with
	| [] -> ()
	| y::yl -> 
	    List.iter (check y) xl;
	    List.iter (check y) yl;
	    go (y::xl) yl in
      go [] (List.map get_data par_calls)
  | _ -> ()
  in 
  check_main_req_empty ();
  check_init_sequential ();
  Hashtbl.iter (fun _ fi -> Parsetree.iter check_par_fcalls fi.body) env.functions

let create_env iteml =
  let env = initial_env () in
  let rsrc_invs, iteml = desugar_rsrc_initzers iteml env in
  process_declarations iteml env;
  compose_init_and_main rsrc_invs env;
  calc_call_graph env;
  calc_mvr env;
  (* if !Config.verbose1 then print_env !Config.formatter env; *)
  check_variable_conditions env;
  env

let conv_stm env in_parallel body =
  let rec f rgnl (ins_no,ins_br,ins_co,ins_re)
    {pstm_desc = d; pstm_loc = loc} = match d with
    | Pstm_exp (e) ->
	let stmts =
	  begin match e.pexp_desc with
	    | Pexp_fcall(s,(idl,el)) -> 
		let idl = List.map (fst >> Id.create) idl in
		let (stmts2, cel) = convert_exp_list_se rgnl el [] in
		stmts2 @ mk_cmd (Cst_pfcall[(None,s,idl,cel)]) e.pexp_loc
	    | _ -> fst (convert_exp_se rgnl e [])
	  end in
	stmts @ ins_no
    | Pstm_assign (i, peo) ->
	begin match peo with 
	| None ->
	    mk_cmd (Cst_kill (IdSet.add (Id.create i) IdSet.empty)) loc @ ins_no
	| Some {pexp_desc = Pexp_fld (e,c); pexp_loc = l} ->
	    let (stmts,ce) = convert_exp_se rgnl e [] in
	    stmts @ mk_cmd (Cst_fldlookup (rgnl, Id.create i, ce, c)) loc @ ins_no
	| Some {pexp_desc = Pexp_new (_,pe); pexp_loc = _} -> 
	    let (stmts,ce) = convert_exp_se rgnl pe [] in
	    stmts @ mk_cmd (Cst_new (Id.create i, ce)) loc @ ins_no
	| Some pe -> 
	    let (stmts,ce) = convert_exp_se rgnl pe [] in
	    stmts @ mk_cmd (Cst_assign (Id.create i, ce)) loc @ ins_no
	end
    | Pstm_fldassign l ->
	let (rev_stmts,rev_l) =
	  List.fold_left 
	    (fun (res,l) (e1,t,e2) ->
	       let (stmts1,ce1) = convert_exp_se rgnl e1 [] in
	       let (stmts2,ce2) = convert_exp_se rgnl e2 [] in
	       (List.rev_append stmts2 (List.rev_append stmts1 res), 
		(ce1,t,ce2)::l))
	    ([],[]) l in
	List.rev_append 
	  rev_stmts 
	  (mk_cmd (Cst_fldassign (rgnl, List.rev rev_l,ref[])) loc @ ins_no)
    | Pstm_dispose (e1,e2) ->
	let (stmts,e1) = convert_exp_se rgnl e1 [] in
	let (stmts,e2) = convert_exp_se rgnl e2 stmts in
	stmts @ mk_cmd (Cst_dispose (e1,e2)) loc @ ins_no
    | Pstm_block sl ->
	List.flatten (List.map (f rgnl ([],ins_br,ins_co,ins_re)) sl) @ ins_no
    | Pstm_if (e, s1, s2) ->
	let (stmts1, stmts2) = match e with 
	  | None -> ([],[]) 
	  | Some e -> convert_assume_exp rgnl e in
	let c1 = stmts1 @ f rgnl (ins_no,ins_br,ins_co,ins_re) s1 in
	let c2 = stmts2 @ f rgnl (ins_no,ins_br,ins_co,ins_re) s2 in
        mk_nondet c1 c2 loc IdSet.empty
    | Pstm_assume (e) ->
	fst (convert_assume_exp rgnl e) @ ins_no
    | Pstm_while (invo, eo, s) ->
        let _ = match invo, eo with 
          | Some _, Some e when not (exp_is_pure e) ->
              error ("While loop has a non-pure guard.", loc)
          | _ -> () in
        let (s1,s2) = match eo with
          | None -> ([],[])
          | Some e -> convert_assume_exp rgnl e in
	let s0 = mk_nondet s1 (s2 @ mk_cmd (Cst_goto Cgo_break) loc) 
                   loc IdSet.empty in
	let invo = invo >>= fun inv -> Some (convert_prop inv loc) in
	mk_loop (s0 @ f rgnl ([],[],[],ins_re) s) invo loc IdSet.empty @ ins_no
    | Pstm_return eo ->
        let eo1 = match eo with None -> Some {pexp_desc=(Pexp_num 0); pexp_loc=loc} | _ -> eo in
	f rgnl ([],ins_br,ins_co,ins_re) 
	  {pstm_desc = Pstm_assign("Result", eo1); pstm_loc=loc}
	@ ins_re 
	@ mk_cmd (Cst_goto Cgo_return) loc
    | Pstm_break       -> ins_br @ mk_cmd (Cst_goto Cgo_break) loc
    | Pstm_continue    -> ins_co @ mk_cmd (Cst_goto Cgo_continue) loc
    | Pstm_interfere (rid, actid) -> 
	mk_cmd (Cst_interfere (rid, actid)) loc @ ins_no
    | Pstm_withres (rid, e, s,actid,argl) ->
	let mk_ins' exit_code = 
	  (exit_code @ ins_no, exit_code @ ins_br, 
	   exit_code @ ins_co, exit_code @ ins_re) in
	let (stmts,_) = convert_assume_exp (rid::rgnl) e in
	let ri = lookup_resource env rid in
	let modif_body = (mvr_body env [s]).md in
	let exit_code = match ri.res_interf with
	  | None -> mk_cmd (Cst_stabilize rid) loc
	  | Some sl -> List.flatten (List.map (f (rid::rgnl) ([],ins_br,ins_co,ins_re)) sl) in
        if actid="" then (* no annotation *) 
          match ri.rinv with
	  | Some inv when StringMap.is_empty ri.ractions -> (* a traditional region *)
	      let exit_code =
		mk_cmd (Cst_action_end (rid,fv_norm_cprop inv)) loc @ exit_code in
	      stmts 
	      @ mk_cmd (Cst_action_begin(rid,cprop_empty,inv,inv,modif_body)) loc
	      @ f (rid::rgnl) (mk_ins' exit_code) s
	  | _ -> (* a read-only region *)
	      stmts 
	      @ f (rid::rgnl) (mk_ins' exit_code) s 
	else 
	  let ai = try lookup_action ri actid 
	    with Not_found -> error ("Action " ^ actid ^ " of resource " ^ string_of_component rid ^ " is not defined.", loc) in
	  let el = List.map convert_exp argl in
	  let xel = try PList.combine (List.map (fst >> Id.create) ai.act_param) el 
            with Invalid_argument _ -> argnum_error ("Action annotation","",ai.act_param,el,loc) in
	  let sub = mk_subst (PCons (Id.mytid,E.tid, xel)) in
	  let act_ctx = map_cprop sub ai.act_ctx in
	  let act_pre = map_cprop sub ai.act_pre in
	  let act_post =  map_cprop sub ai.act_post in
	  let exit_code =
	    mk_cmd (Cst_action_end (rid,fv_norm_cprop act_post)) loc 
	    @ List.fold_right (fun s res -> f (rid::rgnl) ([],ins_br,ins_co,ins_re) s @ res) ai.act_code 
		exit_code in
	  stmts 
	  @ mk_cmd (Cst_action_begin(rid,act_ctx,act_pre,act_post,modif_body)) loc
	  @ f (rid::rgnl) (mk_ins' exit_code) s
    | Pstm_action (s,rid,actid,argl) ->
	let modif_body = (mvr_body env [s]).md in
	let ri = lookup_resource env rid in
	let ai = try lookup_action ri actid 
	  with Not_found -> error ("Action " ^ actid ^ " of resource " ^ string_of_component rid ^ " is not defined.", loc) in
	let el = List.map convert_exp argl in
	let xel = try PList.combine (List.map (fst >> Id.create) ai.act_param) el 
          with Invalid_argument _ -> argnum_error ("Action annotation","",ai.act_param,el,loc) in
	let sub = mk_subst (PCons (Id.mytid, E.tid, xel)) in
	let act_ctx = map_cprop sub ai.act_ctx in
	let act_pre = map_cprop sub ai.act_pre in
	let act_post =  map_cprop sub ai.act_post in
	let exit_code =
	  mk_cmd (Cst_action_end (rid,fv_norm_cprop act_post)) loc
	  @ List.fold_right (fun s res -> f rgnl ([],ins_br,ins_co,ins_re) s @ res) ai.act_code [] in
	let ins' =
	  (exit_code @ ins_no, exit_code @ ins_br, 
	   exit_code @ ins_co, exit_code @ ins_re) in
	mk_cmd (Cst_action_begin(rid,act_ctx,act_pre,act_post,modif_body)) loc
	@ f rgnl ins' s
    | Pstm_parblock par_calls ->
	let go (reso,fid,(vl,el)) =
	  let id = match reso with Some r -> Some (Id.create r) | None -> None in
	  let vl = List.map (fst >> Id.create) vl in
	  let el = try List.map convert_exp el
	    with Undef_non_pure_expression -> error ("Parallel function call has a non-pure argument.", loc) in
	  (id,fid,vl,el) in
        mk_cmd (Cst_pfcall (List.map go par_calls)) loc
	@ ins_no
    | Pstm_comment s -> mk_cmd (Cst_comment s) loc
  in
  List.flatten (List.map (f [] ([],[],[],[])) body)

let conv_fun env res_lv fid =
  let fi = lookup_function env fid in
  let exfv = prop_exfv fi.pre IdSet.empty in
  let sub = mk_subst (IdSet.fold (fun x r -> PCons(x, E.id (Id.gensym_norm x), r)) exfv PNil) in
  let pre = map_cprop sub fi.pre in
  let pre = and_cprop_pure pre (Pure.conj_one (E.neq E.zero E.tid) Pure.ptrue) in
  let post = map_cprop sub fi.post in
  let c = conv_stm env fi.in_parallel_with 
          (fi.body 
	   @ [{pstm_desc = Pstm_assign("Result",Some {pexp_desc=Pexp_num 0; pexp_loc=fi.fn_loc}); pstm_loc=fi.fn_loc}]) in
  let c = clarify_cmd c in
  (*let c = unfold_loops c in*) (* TESTING ONLY!*) 
  let lv_post = (prop_fv post res_lv) in
  mark_live_vars lv_post c;
  let c = insert_kill_dead_vars c lv_post in
  if Str.string_match (Str.regexp "ABS_") fid 0 then begin
    (* Do additional checks for specification functions *)
    let (effl, _purel) = Commands.linear_parse_spec c in
    match effl with
    | [] | [_] -> ()
    | _::_::_ -> raise (Vcgen_error ("Linearizability specifications must have at most one effectful branch.",fi.fn_loc))
  end;
  (fid,(pre,c,[],post,res_lv,fi.fn_loc))

let conv_res env rid =
  let ri = lookup_resource env rid in
  match ri.rinv with
    | None ->
	let c = conv_stm env StringSet.empty ri.res_cons in
  	mark_live_vars ri.rvars c;
	let c = insert_kill_dead_vars c ri.rvars in
	(rid, Cri_code (ri.rvars,c,ri.res_loc))
    | Some inv -> (rid, Cri_inv (inv,ri.res_loc))

let make_fun_htable env =
  let ht = Hashtbl.create 32 in
  let go fid fi = 
    let returntb = Hashtbl.create 3 in
		let _ = 
		if Str.string_match (Str.regexp "ABS_") fid 0 then ()
		else Parsetree.iter (fun loc pdesc -> match pdesc with
			| Pstm_return eo -> 
				let returnpred = (match eo with
					| None -> Predicate.Not Predicate.True
					| Some eo -> (match eo.pexp_desc with
						| Pexp_ident value -> 
								Predicate.Atom (Predicate.Var (Id.result), 
									Predicate.Eq, Predicate.Var (Id.create value))
						| Pexp_num n -> 
								Predicate.Atom (Predicate.Var (Id.result), 
									Predicate.Eq, Predicate.PInt n)
						| Pexp_bool b ->
								Predicate.Atom (Predicate.Var (Id.result), 
									Predicate.Eq, if b then (Predicate.PInt 1) else (Predicate.PInt 0))
						| Pexp_fld (pe, com) -> (
								match pe.pexp_desc with
										| Pexp_ident value -> 
											Predicate.Atom (Predicate.Var (Id.result),
											Predicate.Eq, Predicate.FunApp (string_of_field_component com, 
									 		[Predicate.Var (Id.create value)]
											))
										| _ -> (** FIX ME !! *) 
											Predicate.Atom (Predicate.Var (Id.result),
											Predicate.Eq, Predicate.FunApp (string_of_field_component com, 
									 		[Predicate.Var (Id.create "RPTR")]
											))
										)
						| _ -> Predicate.True
						)
					) in
				(*let _ = Misc.pp "At return site %s, insert pred %a@." 
										(Location.lineno_to_string loc) Predicate.pprint returnpred in*)
				Hashtbl.replace returntb loc returnpred
			| _ -> ()
			) fi.body in
		{fun_param = (List.map (fun(x,_,_)->x) (fst fi.param),
                  List.map (fun(x,_,_)->x) (snd fi.param));
     fun_modif = fi.modif;
     fun_pre = fi.pre;
     fun_post = fi.post;
     fun_loc = fi.fn_loc;
		 fun_purespec = fi.purespec;
		 fun_effspec = fi.effspec; 
		 fun_returns = returntb;
		 fun_lbs = 
			List.map (fun (x,y,_)-> (x,string_of_ty y)) 
			(fst fi.param @ snd fi.param @ fi.locals)} in
  Hashtbl.iter (fun x fi -> Hashtbl.add ht x (go x fi)) env.functions;
  ht

let make_res_htable env = 
  let mk_rely aid ai res =
    let f (name,_) r =
      let id = Id.create name in PCons (id, E.id (Id.gensym_garb id), r) in
    let sub =
      List.fold f ai.act_param PNil
      |> IdSet.fold (fun id r -> PCons (id, E.id (Id.gensym_garb id), r))
           ai.act_locals
      |> mk_subst in
    new_acts aid 
      (map_cprop sub ai.act_ctx) 
      (map_cprop sub ai.act_pre)
      (map_cprop sub ai.act_post)
    @ res
  in
  let ht = Hashtbl.create 32 in
  Hashtbl.iter (fun rid ri -> 
    let rely = StringMap.fold mk_rely ri.ractions [] in
    Hashtbl.add ht rid rely) env.resources;
  ht
	
let make_res_def_htable env = 
	let ht = Hashtbl.create 32 in
	Hashtbl.iter (fun rid ri ->
		Hashtbl.add ht rid ri.res_def
		) env.resources; 
	ht	

let convert iteml =
  Indpreds.init_ip_env ();
  error_handler (fun () ->
    let env = create_env iteml in
    let entl1 = List.rev_map (conv_res env) env.env_rsrcs in
    let res_lv = Hashtbl.fold (fun _ x r -> x.rvars ++ r)
		 env.resources IdSet.empty in
    let entl2 = List.rev_map (conv_fun env res_lv) env.env_funcs in
    let  _ = try check_ip_uses () with Indpred_error (s,loc) -> error (s,loc) in
    let globals = 
      IdMap.fold (fun x _ r -> IdSet.add x r) env.variables IdSet.empty in
    let fun_ht = make_fun_htable env in
    let res_ht = make_res_htable env in
    let fields =
      Hashtbl.fold (fun _ ci -> StringMap.fold 
                      (fun x _ r -> StringSet.add x r) ci.cla_fields)
        env.classes StringSet.empty in
    let comments = List.rev env.comments in
		let res_def_ht = make_res_def_htable env in
		let tdesc = (Hashtbl.fold (fun sid ci res -> match ci.cla_tdesc with
			| Some tdsec -> (match res with
				| Some _ -> (Misc.pp "Duplicated thread descriptors defined@."; assert false)
			 	| None -> (Misc.pp "%s is thread descriptor with %a@." sid Predicate.pprint tdsec; Some (sid, tdsec))
				)
			| None -> res
			) env.classes None) in
    (comments, fields, globals, fun_ht, res_ht, res_def_ht, entl1, entl2, tdesc))
