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
open Pure
open Assertions

exception Indpred_error of string * Location.t

type ip_decl =
    {ip_id: string;
     ip_args: Id.t list;
     ip_body: (Pure.t * cform) list;
     ip_node: bool; (** can it be a list node *)
     ip_loc: Location.t}

let body_to_cprop body =
  (*mk_cprop*) (List.map (fun(pl1,((pl2,sl),scpl)) -> ((Pure.conj pl1 pl2,sl),scpl)) body)

let ex_fv_ip_body body = prop_exfv (body_to_cprop body) IdSet.empty

let node_component = component_of_string "Node"

(**** pretty printing ****)
open Format

let pp_string f s = fprintf f "%s" s

let rec pp_listsep pp s1 s2 f = function
  | [] -> fprintf f "%s" s2
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a%s %a" pp x s1 (pp_listsep pp s1 s2) l

let pp_idlist = pp_listsep pp_string "" ","

let pp_ip_decl f = function
  | {ip_id=p; ip_args=ia; ip_body=body} ->
      fprintf f "%s(%a) = %a" p pp_idlist (List.map Id.to_string ia) 
      pp_cprop (body_to_cprop body)

(**** environment of inductive definitions ****)
let (ip_env : (string, ip_decl) Hashtbl.t) = Hashtbl.create 16
let ip_uses = ref ([] : (string * int * Location.t) list)

let init_ip_env () =
  Hashtbl.clear ip_env;
  ip_uses := []

let pp_ip_environment f () =
  Hashtbl.iter (fun _ ip -> fprintf f "%a@." pp_ip_decl ip) ip_env

let add_ip_decl ip =
  let fv_body = fv_norm_cprop (body_to_cprop ip.ip_body) in
  let eargs = List.map E.id ip.ip_args in
  let fv_args = List.fold E.fv eargs IdSet.empty in
  let () =
    let x = IdSet.diff fv_body fv_args in
    if not (IdSet.is_empty x) then 
      raise (Indpred_error ("Variable " ^ Id.to_string (IdSet.choose x) ^ 
                            " is free in the definition of predicate " ^ ip.ip_id ^ ".", ip.ip_loc)) in
  let () = 
    if Hashtbl.mem ip_env ip.ip_id then
      raise (Indpred_error ("Predicate " ^ ip.ip_id ^ " is already defined.",ip.ip_loc)) in
  Hashtbl.add ip_env ip.ip_id ip

let add_ip_use x = ip_uses := x :: !ip_uses

let lookup_ip id = Hashtbl.find ip_env id

let check_ip_uses () =
  let f (id,n,loc) =
    if n=(-1) && String.get id 0 = '.' then () else try
      let decl = lookup_ip id in
      if n=(-1) then 
	if decl.ip_node then () else raise (Indpred_error ("Predicate " ^ id ^ " is not a valid list node.",loc))
      else
	let argn = List.length (decl.ip_args) in 
	if argn <> n then 
	  raise (Indpred_error ("Predicate " ^ id ^ " expects "
		   ^ string_of_int argn ^ " arguments, but "
		   ^ string_of_int n ^ " are provided.",loc))
    with Not_found -> raise (Indpred_error ("Undefined predicate " ^ id ^ ".",loc))
  in 
  List.iter f !ip_uses;
  ip_uses := [] (* Assist GC *)

let instance_ip (id,el) =
  let ip = lookup_ip id in
  let iil = PList.combine ip.ip_args el in
  let sub = mk_subst iil in
  map_ip_body sub (ip.ip_body)

let instance_ip_lhs (id,el) =
  let body = instance_ip (id,el) in
  let sub = existentials_rename_sub (ex_fv_ip_body body) in
  map_ip_body sub body

let instance_ip_rhs (id,el) =
  let body = instance_ip (id,el) in
  let ex_fv_args = List.fold E.exfv el IdSet.empty in
  let ex_fv_body = IdSet.diff (ex_fv_ip_body body) ex_fv_args in
  let sub = mk_gensym_garb_subst_idset ex_fv_body in
  map_ip_body sub body

let ip_body_to_node_data = function
  | [(x,((pl,sl),PNil))] ->
      assert (Pure.is_true x);
      begin match spat_fold_spred (fun x r -> x::r) sl [] with
				| [Csp_node(_,s,_,cel)] -> (s,cel,pl)
				| _ -> assert false
      end
  | _ -> assert false

(** Unroll a node declaration in the lhs *) 
let unroll_node_lhs snode e1 =
  let e2 = E.gensym_str "split" in
  let e3 = E.gensym_str "valsplit" in
  let e4 = E.item e3 in
  let (s,cel,pl) = 
    if component_is_field snode then
      let t1 = snode in
      (node_component, Fld.two t1 e2 Misc.list_data_tag e3, Pure.ptrue) 
    else
      ip_body_to_node_data (instance_ip_lhs (string_of_component snode,[e1;e2;e3])) in
  (e2,e4,s,cel,pl)

(** Unroll a node declaration in the rhs *)
let unroll_node_rhs snode e1 =
  let e2 = E.gensym_str_ex "split" in
  let e3 = E.gensym_str_ex "valsplit" in
  let e4 = E.item e3 in
  let (s,cel,pl) = 
    if component_is_field snode then
      let t1 = snode in
      (node_component, Fld.two t1 e2 Misc.list_data_tag e3, Pure.ptrue) 
    else
      ip_body_to_node_data (instance_ip_rhs (string_of_component snode,[e1;e2;e3])) in
  (e2,e4,s,cel,pl)


let print_ip_env f =
  if Hashtbl.length ip_env <> 0 then
    fprintf f "INDUCTIVE PREDICATES:@.%a@." pp_ip_environment ()
