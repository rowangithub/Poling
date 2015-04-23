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
open Format


(* -------------------------------------------------------------------------- *)
(** {2 Arguments} *)
(* -------------------------------------------------------------------------- *)

(** Enable arithmetic program generation if [>0]. *)
let gen_arith = ref 0

let enabled () = !gen_arith > 0

let args = 
  [("-gen_arith", Arg.Set_int gen_arith, "<n> Generate arithmetic programs (experimental)")]



(* -------------------------------------------------------------------------- *)
(** {2 Helper functions} *)
(* -------------------------------------------------------------------------- *)

let tempids = ref (Array.init 16 (fun _ -> Id.tempid ()))

let new_tempid n =
  let k = Array.length tempids.contents in
  if n >= k then begin
    tempids :=
      Array.init (n+1) 
	(fun m -> 
	   if m < k then 
	     Array.get tempids.contents m
	   else Id.tempid ())
  end;
  Array.get tempids.contents n

let no_junk_exp e = E.forall_fv Id.is_no_junk_var e

(* -------------------------------------------------------------------------- *)
(** {2 Graphs} *)
(* -------------------------------------------------------------------------- *)

type ga_node =
    { ga_id: int;
      mutable ga_form: cform;
      mutable ga_refs: int;
      mutable ga_prog: ga_prog
    }

and ga_prog =
  | Ga_skip   of ga_node
  | Ga_nondet of ga_prog list
  | Ga_assn   of Id.t * exp option * ga_prog
  | Ga_assume  of exp * ga_prog
  | Ga_comment of string * ga_prog
  | Ga_return

let rec ga_exp = function x -> x
(*
  | ((Enum _ | Eident _ ) as x) -> x 
  | Eeq(x,y) -> E.eq (ga_exp x) (ga_exp y)
  | Efun1 (Sfn_item, _) -> E.one
  | Efun (sfn, el) ->
      let el = List.map ga_exp el in
      else if sfn == sfn_set then E.grp "+" 0 (List.map (fun x -> (1,x)) el)
      else E.fun sfn el
  | Egrp(s,n,nel) -> E.grp s n (List.map (fun (n,e)->(n,ga_exp e)) nel)
*)

let mk_return = Ga_nondet []

let mk_assn x eo r = match eo with
  | None -> Ga_assn(x,None,r)
  | Some e -> 
      if e == E.id x then r else Ga_assn(x,Some (ga_exp e),r)

let rec eq_prog x y = match x,y with
  | Ga_skip n, Ga_skip m -> n==m
  | Ga_nondet xl, Ga_nondet yl -> 
      List.length xl = List.length yl 
	&& List.for_all2 eq_prog xl yl
  | Ga_assn (i,None,x), Ga_assn(k,None,y) ->
      i==k && eq_prog x y
  | Ga_assn (i,Some e,x), Ga_assn(k,Some f,y) ->
      i==k && equal_exp e f && eq_prog x y
  | Ga_assume (e,x), Ga_assume (f,y) ->
      equal_exp e f && eq_prog x y
  | Ga_comment (s,x), Ga_comment (t,y) ->
      s=t && eq_prog x y
  | Ga_return, Ga_return -> true
  | _ -> false


(** A parallel assigment: (x1,...,xn) = (e1,...,en)   *)
let mk_ParAssign ieol r =
  let ieol =
    let ieol = List.filter (fun (s,_) -> Id.is_no_junk_var s) ieol in
    List.map 
      (function
	 | (i,Some e) when no_junk_exp e -> (i,Some e)
	 | (i,_) -> (i,None))
      ieol in
  let ieol = (* Remove assigments x = x *)
    List.filter
      (function 
	 | (id,Some e) -> E.id id != e
	 | _ -> true)
      ieol in
  (* Special case for single assignments *)
  match ieol with [(i,eo)] -> mk_assn i eo r | _ ->
  let (_,r1,r2) = 
    List.fold_left 
      (fun (n,r1,r2) (i,o) -> match o with 
	 | None -> (n,r1,mk_assn i o r2)
	 | Some _ -> 
	     let t = new_tempid n in
	     (n+1,(t,o)::r1,mk_assn i (Some (E.id t)) r2))
      (0,[],r) ieol
  in
  List.fold_left (fun r (i,o) -> mk_assn i o r) r2 r1

let mk_assume p r =
  match ga_exp (Pure.to_exp p) with 
    | Enum 0 -> Ga_assume(E.zero,r)
    | Enum _ -> r
    | Efun(Sfn_AND,el) ->
       let el = List.filter no_junk_exp el in
       List.fold_left (fun r e -> Ga_assume(e,r)) r el
    | e -> 
       if no_junk_exp e then Ga_assume(e,r) else r

let mk_nondet xl =
  let rec go r = function
    | [] -> r
    | Ga_nondet xl0 :: xl -> go r (xl0 @ xl)
    | x :: xl -> 
			if List.exists (eq_prog x) r then go r xl
			else go (x::r) xl
  in
  	match go [] xl with
    	| [x] -> x
    	| xl -> Ga_nondet xl

(** Used to create fresh nodes *)
let new_node_counter = ref 0

(** Create an new node *)
let new_node cf = 
  incr new_node_counter;
  { ga_id = !new_node_counter;
    ga_form = cf;
    ga_refs = 0;
    ga_prog = Ga_nondet []
  }

(** Put the program [prog] at node [n] *)
let put_prog n prog =
  if !gen_arith > 0 then
    n.ga_prog <- prog

let add_prog n prog =
  put_prog n (mk_nondet [prog; n.ga_prog])

let put_edge_skip n1 n2 = 
  put_prog n1 (Ga_skip n2)

let put_edge_implication n1 sub p n2 = 
  let el = 
    match Pure.to_exp p with 
    | Efun(Sfn_AND,el) -> el 
    | e -> [e] in
  let ieol = 
    List.fold_left
      (fun res e ->
	 match e with
	 | Eeq (e1,e2) when existential_id e1 -> (Id.of_exp e1, Some (sub e2))::res
	 | _ -> res) [] el in
  add_prog n1 (mk_ParAssign ieol (Ga_skip n2))


(* -------------------------------------------------------------------------- *)
(** {2 Graph simplification} *)
(* -------------------------------------------------------------------------- *)
(** Terminator cannot handle big programs; so try to compress the
    program as much as possible.
    Algorithm: 
    1. Remove all nodes that are simple returns, gotos
    2. Inline and remove all nodes that are reachable from only
    one place.
*)


let gdo x f = match x with Ga_return | Ga_nondet [] -> x | _ -> f x


(** Remove return/goto/assert(0) nodes *)
let g_clear_counts ht n =
  let rec go_node n =
    n.ga_refs <- 0;
    if not (Hashtbl.mem ht n.ga_id) then begin
      Hashtbl.add ht n.ga_id ();
      go_prog n.ga_prog
    end
  and go_prog = function
    | Ga_skip n -> go_node n
    | Ga_nondet xl -> List.iter go_prog xl
    | Ga_assn (i,e,x) -> go_prog x
    | Ga_assume (e,x) -> go_prog x
    | Ga_comment(s,x) -> go_prog x
    | Ga_return -> () in
  go_node n


(** Remove return/goto/assert(0) nodes *)
let g_simplify1 ht n =
  let ret_simple1 n =
    match n.ga_prog with
      | Ga_nondet [] | Ga_return | Ga_skip _ -> n.ga_prog
      | _ -> Ga_skip n in
  let ret_simple2 n =
    match n.ga_prog with
      | Ga_nondet [] | Ga_return -> n.ga_prog
      | Ga_skip m -> n.ga_refs <- n.ga_refs - 1; m.ga_refs <- m.ga_refs + 1; n.ga_prog
      | _ -> Ga_skip n in
  let rec go_node n =
    n.ga_refs <- n.ga_refs + 1;
    if Hashtbl.mem ht n.ga_id then
      ret_simple1 n
    else begin
      Hashtbl.add ht n.ga_id ();
      let p = go_prog n.ga_prog in
      n.ga_prog <- p;
      ret_simple2 n
    end
  and go_prog = function
    | Ga_skip n -> go_node n
    | Ga_nondet xl -> mk_nondet (List.map go_prog xl)
    | Ga_assn (i,e,x) -> go_do x (fun x -> Ga_assn (i,e,x))
    | Ga_assume (e,x) -> go_do x (fun x -> Ga_assume (e,x))
    | Ga_comment(s,x) -> go_do x (fun x -> Ga_comment(s,x))
    | Ga_return -> Ga_return
  and go_do x f = gdo (go_prog x) f in
  ignore (go_node n)

(** Inline nodes reachable by only one point *)
let g_simplify2 ht n =
  let rec go_node n =
    if n.ga_refs = 1 then 
      let p = go_prog n.ga_prog in
      n.ga_prog <- p;
      p
    else begin 
      if not (Hashtbl.mem ht n.ga_id) then begin
	Hashtbl.add ht n.ga_id ();
	n.ga_prog <- go_prog n.ga_prog
      end;
      Ga_skip n
    end
  and go_prog = function
    | Ga_skip n -> go_node n
    | Ga_nondet xl -> mk_nondet (List.map go_prog xl)
    | Ga_assn (i,e,x) -> go_do x (fun x -> Ga_assn (i,e,x))
    | Ga_assume (e,x) -> go_do x (fun x -> Ga_assume (e,x))
    | Ga_comment(s,x) -> go_do x (fun x -> Ga_comment(s,x))
    | Ga_return -> Ga_return
  and go_do x f = gdo (go_prog x) f in
  ignore (go_node n)


(** Remove self loops for which we don't want to prove termination *)
let g_simplify3 ht n =
  let rec go_node n =
    if Hashtbl.mem ht n.ga_id then ()
    else begin
      Hashtbl.add ht n.ga_id ();
      go_top_prog n n.ga_prog
    end
  and go_top_prog n = function
    | Ga_nondet xl -> 
	let xl = List.filter 
	  (function Ga_skip x | Ga_assume (_,Ga_skip x) -> x!=n | _ -> true) xl in
	n.ga_prog <- mk_nondet xl;
	List.iter go_prog xl
    | x -> go_assn_prog n x
  and go_assn_prog n = function
    | Ga_skip x when x==n -> n.ga_prog <- mk_nondet []
    | Ga_assume (_,x)
    | Ga_assn (_,_,x) -> go_assn_prog n x 
    | x -> go_prog x
  and go_prog = function
    | Ga_skip n -> go_node n
    | Ga_nondet xl -> List.iter go_prog xl
    | Ga_assn (_,_,x)
    | Ga_assume (_,x)
    | Ga_comment(_,x) -> go_prog x
    | Ga_return -> () in
  go_node n


(** Simplify the graph *)
let graph_simplify n = 
  let ht = Hashtbl.create 32 in
  for i = 1 to !gen_arith - 1 do
    g_simplify1 ht n;
    Hashtbl.clear ht;
    g_simplify2 ht n;
    Hashtbl.clear ht;
    g_simplify3 ht n;
    Hashtbl.clear ht;
    g_clear_counts ht n;
    Hashtbl.clear ht;
  done


(** Return the set of variables appearing in statements 
    reachable from [n]. *)
let get_graph_vars n = 
  let ht = Hashtbl.create 32 in
  let rec go_node r n =
    n.ga_refs <- n.ga_refs + 1;
    if Hashtbl.mem ht n.ga_id then r
    else begin
      Hashtbl.add ht n.ga_id ();
      go_prog r n.ga_prog
    end
  and go_prog r = function
    | Ga_skip n -> go_node r n
    | Ga_nondet xl -> List.fold_left go_prog r xl
    | Ga_assn (i,None,x) -> go_prog (IdSet.add i r) x 
    | Ga_assn (i,Some e,x) -> go_prog (E.fv e (IdSet.add i r)) x 
    | Ga_assume (e,x) -> go_prog (E.fv e r) x 
    | Ga_comment(_,x) -> go_prog r x
    | Ga_return -> r in
  go_node IdSet.empty n


(* -------------------------------------------------------------------------- *)
(** {2 Extended assertions} *)
(* -------------------------------------------------------------------------- *)

type eform = ga_node
type eprop = eform list

let eprop_false = []

let cform_of_eform n = n.ga_form

let eprop_of_cprop cp = List.map new_node cp

let eprop_of_cprop_at_start_node cp =
  let n = new_node ((Pure.ptrue,[]),PNil) in
  let ep = eprop_of_cprop cp in
  put_prog n (mk_nondet (List.map (fun n -> Ga_skip n) ep));
  (n,ep)

let pp_eprop f ep =
  pp_cprop f (List.map (fun n -> n.ga_form) ep)


let compare_node x y = compare_cform x.ga_form y.ga_form


(** Remove syntactically identical disjuncts (and add edges to the
    generated arithmetic program where necessary). *)
let remove_eform_duplicates_from_sorted efl =
  let rec remdup r = function
    | [] -> r
    | [x] -> x::r
    | n::((m::xl) as yl) ->
	if compare_cform n.ga_form m.ga_form = 0 then begin
	  put_edge_skip n m;
	  remdup r yl
	end else
	  remdup (n::r) yl in
  remdup [] efl

(** Optimization: push case splits inside.
    Used when not generating arithmetic programs. *)
let aggr_remove_eform_duplicates_from_sorted efl =
  let rec merge xs ys = match xs, ys with
    | PNil, ys -> ys
    | xs, PNil -> xs
    | PCons(s,x,xs0), PCons(s',y,ys0) ->
	let n = compare_component s s' in
	if n = 0 then PCons (s, remove_cform_duplicates(x@y), merge xs0 ys0)
	else if n < 0 then PCons (s, x, merge xs0 ys)
	else PCons (s',y, merge xs ys0) in
  let rec f = function
    | xn::yn::rest ->
	let (x,xsh) = xn.ga_form in
	let (y,ysh) = yn.ga_form in
	if compare_uform x y = 0 then 
	  f (new_node (y, merge xsh ysh) :: rest)
	else xn::(f(yn::rest))
    | xs -> xs in
  f efl

let remove_eform_duplicates_from_sorted l =
  if !gen_arith = 0 then 
    aggr_remove_eform_duplicates_from_sorted l 
  else
    remove_eform_duplicates_from_sorted l 

let remove_eform_duplicates l =
  remove_eform_duplicates_from_sorted (List.sort compare_node l)

let (@@@) n cp = cprop_star [n.ga_form] cp 

let eprop_star cp ep =
  let go_one n =
    let res1 = List.map new_node (n @@@ cp) in
    put_prog n (mk_nondet (List.map (fun x -> Ga_skip x) res1));
    res1 in
  List.reduce_append go_one ep

let eprop_star_assume cp ep = 
  let prog_imp n m =
    let p = Pure.simplify (fst (fst n.ga_form)) (fst (fst m.ga_form)) in
    mk_assume p (Ga_skip m) in
  let go_one n =
    let res1 = List.map new_node (n @@@ cp) in
    put_prog n (mk_nondet (List.map (prog_imp n) res1));
    res1 in
  List.reduce_append go_one ep

let eprop_or ep1 ep2 =
  remove_eform_duplicates (List.rev_append ep1 ep2)

let map_eprop f_e ep =
  let go_one n =
    let res1 = List.map new_node (map_cform f_e n.ga_form) in 
    put_prog n (mk_nondet (List.map (fun x -> Ga_skip x) res1));
    res1 in
  remove_eform_duplicates(*!*) (List.reduce_append go_one ep)

let naive_map_eprop f_e ep =
  List.iter (fun n -> n.ga_form <- naive_map_cform f_e n.ga_form) ep;
  ep

(** Append a return statement *)
let ext_append_return ep =
  List.iter (fun n -> put_prog n mk_return) ep

(** Append a comment *)
let ext_append_comment sfn ep =
  if !gen_arith = 0 then ep else 
  List.map
    (fun n ->
       let m = new_node n.ga_form in
       add_prog n (Ga_comment (sfn (),Ga_skip m));
       m) ep

(** Append an assignment statement *)
let ext_append_assign s ep =
  if !gen_arith = 0 then ep else 
  List.map
    (fun n ->
       let m = new_node n.ga_form in
       add_prog n (mk_ParAssign s (Ga_skip m));
       m) ep

(** Do a case split *)
let ext_append_case_split ep =
  List.fold_left 
    (fun (r1,r2) n ->
       let m1 = new_node n.ga_form in
       let m2 = new_node n.ga_form in
       put_prog n (mk_nondet [Ga_skip m1; Ga_skip m2]);
       (m1::r1, m2::r2))
    ([],[]) ep


let ext_transform fn ep =
  let transf n res =
    let cf = n.ga_form 
		in
    	match (fn cf) with
      | [cf] ->
	  			n.ga_form <- cf; n :: res
      | cfl ->
	  			let nl = List.map new_node cfl 
					in
	  				put_prog n (mk_nondet (List.map (fun x -> Ga_skip x) nl));
	  				nl @ res 
	in
  	remove_eform_duplicates(*!*) (List.reduce transf ep)

let ext_opt_transform1 fn n =
  match fn n.ga_form with
    | None -> None
    | Some [cf] ->
	n.ga_form <- cf;
	Some [n]
    | Some cfl ->
	let nl = List.map new_node cfl in
	put_prog n (mk_nondet (List.map (fun x -> Ga_skip x) nl));
	Some nl

(* -------------------------------------------------------------------------- *)
(** {2 Abstraction interface} *)
(* -------------------------------------------------------------------------- *)

(** Abstract domain corresponding to a disjunction of [uform]s for
    calculating fix-points. *)
type udom = uform list * uform list

let udom_of_uform_list (ufl: uform list) = ([], ufl)
let uform_list_of_udom (ud : udom) = snd ud


(** Interface provided by the abstraction module:
    - [uform_abs] is the analogue of [prop_abs] for formulas with no boxes. See below.
      The boolean argument tells whether the abstraction should be aggressive
      (disregard sentinel values).
    - [uform_join] is the analogue of [prop_join] for formulas with no boxes. See below.
    - [prop_abs cp] returns a [cp'] belonging to a smaller domain such that [cp |- cp']
    - [prop_join cp1a cp1b cp2] assumes that [cp1a <==> cp1b] and returns 
    [(cpa,cpb,cp2')] such that [cpa <==> cpb] 
    and [cp1a |- cpa] and [cp2' |- cpa]
    and [(cp1b \/ cp2) ==> cpb] 
    and [cpb ==> (cp1b \/ cp2')]
*)
type abstraction =
  {
     uform_abs : bool -> uform list -> uform list;
     uform_join : udom -> uform list -> udom * uform list;
     prop_abs : eprop -> eprop;
     prop_join : eprop -> eprop -> eprop -> (eprop * eprop * eprop);
  }


(* -------------------------------------------------------------------------- *)
(** {2 Pretty printing} *)
(* -------------------------------------------------------------------------- *)

let pp_graph f n = 
  let ht = Hashtbl.create 32 in
  let rec pp_node f n = 
    if Hashtbl.mem ht n.ga_id then
      fprintf f "goto L%d;" n.ga_id
    else begin
      Hashtbl.add ht n.ga_id ();
      if !gen_arith mod 2 = 1 then 
	fprintf f "@[/* %a */@]@ " pp_cform n.ga_form;
      if n.ga_refs > 1 then 
	fprintf f "@[<v>L%d: %a@]" n.ga_id pp_prog n.ga_prog
      else
	fprintf f "@[<v>%a@]" pp_prog n.ga_prog
    end
  and pp_prog f = function
    | Ga_skip n -> pp_node f n
    | Ga_assn (i,None,x) ->
	fprintf f "%s = nondet();@ " (Id.to_string i);
	pp_prog f x
    | Ga_assn (i,Some e,x) ->
	fprintf f "%s = %a;@ " (Id.to_string i) pp_exp e;
	pp_prog f x
    | Ga_assume (e,x) ->
	fprintf f "assm(%a);@ " pp_exp e;
	pp_prog f x
    | Ga_comment (s,x) ->
	fprintf f "%s@ " s;
	pp_prog f x
    | Ga_return -> fprintf f "return;"
    | Ga_nondet [] -> fprintf f "assm(0);"
    | Ga_nondet [x] -> fprintf f "{@   @[<v>%a@]@ }" pp_prog x
    | Ga_nondet (x::(_::_ as l)) ->
	fprintf f "if(nondet()) {@   @[<v>%a@]@ } else " pp_prog x;
	pp_prog f (Ga_nondet l)
  in
  pp_node f n

let pp_function f (name,n) =
  graph_simplify n;
  let vars = IdSet.elements (get_graph_vars n) in
  fprintf f "@[<v 2> void %s(void) {@ " name;
  List.iter (fun x -> fprintf f "int %s;@ " (Id.to_string x)) vars;
  List.iter (fun x -> fprintf f "%s = nondet();@ " (Id.to_string x)) vars;
  pp_graph f n;
  fprintf f "@]@;}@."
