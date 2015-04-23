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
(** Symbolic heaps *)
open Misc
open Exp
open Format

let allow_leaks = ref true

let args =
  [("-allow_leaks", Arg.Set allow_leaks, " Allow memory leaks");
   ("-no_leaks", Arg.Clear allow_leaks, " Do not allow memory leaks")]


(* -------------------------------------------------------------------------- *)
(** {2 Data structures} *)
(* -------------------------------------------------------------------------- *)

type link_kind = 
  | SINGLE of component * Fld.t
  | DOUBLE of component * component 
  | XOR of component

type can_isemp = Cem_PE | Cem_NE

(** Tags for spatial predicates.

    Logically, tags are a bitvector representation of the subset of a
    set X permission model (cf., Parkinson's thesis).  Therefore, they
    should always be non-zero.

    Note, however, that tags are not used to encode permissions in the
    assertion language; they are used only as a way of doing the
    [Wande] computations.

    Therefore, for normal spatial predicates, the tag should always be
    [1]. Tags [2]-[7] are used internally by the [Wande] computation as
    follows:

    {v
    tag 1 :  minued, not matched 
    tag 2 :  subtrahend, to be kept
    tag 3 :  difference, to be kept
    tag 6 :  subtrahend, to be removed
    tag 7 :  difference, to be removed
    v}

    The assertion represented as [1 * 2 * 3 * 6 * 7] is interpreted as
    saying: [(2 * 3 * 6 * 7 -*E 1 * 3 * 7) * 2 * 3].

    For further information, see also the appendix of the paper "RGSep action
    inference" (Vafeiadis, VMCAI 2010), where the implementation of
    MAY-SUBTRACT is described.

*)
type tag = int

type can_spred =
  | Csp_listsegi of tag * link_kind * exp * exp * exp * exp
      * can_isemp * Dset.t
  | Csp_arr  of     tag * exp * exp * exp * Fld.t * can_isemp * Dset.t
  | Csp_node of     tag * component * exp * Fld.t
  | Csp_indpred of  tag * string * exp list

(** Spatial part: star-conjuction of can_spred's *)
type can_spatial = can_spred list

type uform = Pure.t * can_spatial              (** Canonical form without boxes *)
type cform = uform * (component, cprop) plist (** Canonical form *)

and cprop = cform list

(** Type of RGSep actions used for interference calculations *)
type act = { 
  a_name : string;
  a_exvars : IdSet.t;
  a_pure : Pure.t; 
  a_pre : can_spatial (** context & precondition *);
  a_post : cprop }

exception No_frame_found
exception Junk

type prover =
   { find_ptsto : Misc.component -> exp -> can_spatial -> 
                  Fld.t * can_spatial;
     expose_ptsto : cprop -> exp -> cprop;
     nf_cprop : can_spatial -> cprop -> cprop;
     nf_cform : cform -> cprop;
     entails_cprop : cprop -> cprop -> Pure.t list;
     find_frame_cprop : can_spatial -> cprop -> cprop -> cprop;
     adv_entails_atom : cprop -> exp -> bool;
   }

(* -------------------------------------------------------------------------- *)
(** {2 Helper functions} *)
(* -------------------------------------------------------------------------- *)

(** Only allow comparisons between integers to catch uses of builtin
    equality.  Use Pervasives.(=) on base types only *)
let (=) (x:int) (y:int) = x=y

(** [get_first f l] assumes [List.exists f l].
    [get_first f (xs @ [y] @ zs) = (y, xs @ zs)] where [f y] and 
    [forall (not << f) xs].
 *)
let get_first f =
  let rec go acc l = match l with
    | x :: l -> if f x then (x, List.rev_append acc l) else go (x :: acc) l
    | [] -> assert(false) (* Should never happen *)
  in
  go []

(* -------------------------------------------------------------------------- *)
(** {2 Equality and comparison functions} *)
(* -------------------------------------------------------------------------- *)

let compare_lkind k1 k2 = if k1 == k2 then 0 else match k1,k2 with
  | SINGLE(s1,cel), SINGLE(s1',cel') ->
      let n = compare_component s1 s1' in if n<>0 then n else
      Fld.compare cel cel'
  | SINGLE _, _ -> -1
  | _, SINGLE _ -> 1
  | DOUBLE(s1,s2), DOUBLE(s1',s2') ->
      let n = compare_component s1 s1' in if n<>0 then n else
      compare_component s2 s2'
  | DOUBLE _, _ -> -1
  | _, DOUBLE _ -> 1
  | XOR(s1), XOR(s1') -> compare_component s1 s1'

let compare_can_spred sp1 sp2 = if sp1 == sp2 then 0 else match sp1,sp2 with
  | Csp_listsegi (tag,k,e1,e2,e3,e4,ie,ds), 
    Csp_listsegi(tag',k',e1',e2',e3',e4',ie',ds') ->
      let n = tag - tag' in if n<>0 then n else
      let n = compare_lkind k k' in if n<>0 then n else
      let n = compare_exp e1 e1' in if n<>0 then n else
      let n = compare_exp e2 e2' in if n<>0 then n else
      let n = compare_exp e3 e3' in if n<>0 then n else
      let n = compare_exp e4 e4' in if n<>0 then n else
      let n = Obj.magic ie - Obj.magic ie' in if n<>0 then n else
      Dset.compare ds ds'
  | Csp_listsegi _, _ -> -1
  | _, Csp_listsegi _ -> 1
  | Csp_arr (tag,e1,e2,e3,fld,ie,ds), 
    Csp_arr(tag',e1',e2',e3',fld',ie',ds') ->
      let n = tag - tag' in if n<>0 then n else
      let n = compare_exp e1 e1' in if n<>0 then n else
      let n = compare_exp e2 e2' in if n<>0 then n else
      let n = compare_exp e3 e3' in if n<>0 then n else
      let n = Fld.compare fld fld' in if n<>0 then n else
      let n = Obj.magic ie - Obj.magic ie' in if n<>0 then n else
      Dset.compare ds ds'
  | Csp_arr _, _ -> -1
  | _, Csp_arr _ -> 1
  | Csp_node (tag1,s1,e1,cel1), Csp_node (tag2,s2,e2,cel2) ->
      let n = tag1 - tag2 in if n<>0 then n else
      let n = compare_component s1 s2 in if n<>0 then n else
      let n = compare_exp e1 e2 in if n<>0 then n else 
      Fld.compare cel1 cel2
  | Csp_node _, _ -> -1
  | _, Csp_node _ -> 1
  | Csp_indpred (tag1,s1,el1), Csp_indpred (tag2,s2,el2) ->
      let n = tag1 - tag2 in if n<>0 then n else
      let n = String.compare s1 s2 in if n<>0 then n else
      compare_exp_list el1 el2

let abs_compare_can_spred sp1 sp2 = if sp1 == sp2 then 0 else match sp1,sp2 with
  | Csp_listsegi (tag,k,e1,e2,e3,e4,ie,ds),
    Csp_listsegi(tag',k',e1',e2',e3',e4',ie',ds') ->
      let n = tag - tag' in if n<>0 then n else
      let n = compare_lkind k k' in if n<>0 then n else
      let n = abs_compare_exp e1 e1' in if n<>0 then n else
      let n = abs_compare_exp e2 e2' in if n<>0 then n else
      let n = abs_compare_exp e3 e3' in if n<>0 then n else
      let n = abs_compare_exp e4 e4' in if n<>0 then n else
      let n = Obj.magic ie - Obj.magic ie' in if n<>0 then n else
      Dset.abs_compare ds ds'
  | Csp_listsegi _, _ -> -1
  | _, Csp_listsegi _ -> 1
  | Csp_arr (tag,e1,e2,e3,fld,ie,ds), 
    Csp_arr(tag',e1',e2',e3',fld',ie',ds') ->
      let n = tag - tag' in if n<>0 then n else
      let n = abs_compare_exp e1 e1' in if n<>0 then n else
      let n = abs_compare_exp e2 e2' in if n<>0 then n else
      let n = abs_compare_exp e3 e3' in if n<>0 then n else
      let n = Fld.compare fld fld' in if n<>0 then n else
      let n = Obj.magic ie - Obj.magic ie' in if n<>0 then n else
      Dset.abs_compare ds ds'
  | Csp_arr _, _ -> -1
  | _, Csp_arr _ -> 1
  | Csp_node (tag1,s1,e1,cel1), Csp_node (tag2,s2,e2,cel2) ->
      let n = tag1 - tag2 in if n<>0 then n else
      let n = compare_component s1 s2 in if n<>0 then n else
      let n = abs_compare_exp e1 e2 in if n<>0 then n else 
      Fld.compare cel1 cel2
  | Csp_node _, _ -> -1
  | _, Csp_node _ -> 1
  | Csp_indpred (tag1,s1,el1), Csp_indpred (tag2,s2,el2) ->
      let n = tag1 - tag2 in if n<>0 then n else
      let n = String.compare s1 s2 in if n<>0 then n else
      compare_exp_list el1 el2

let rec compare_can_spatial sl1 sl2 = match sl1,sl2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | sp1::sl1', sp2::sl2' ->
      let n = compare_can_spred sp1 sp2 in if n<>0 then n else
      compare_can_spatial sl1' sl2'

let compare_uform (pl1,sl1) (pl2,sl2) =
  let n = Pure.compare pl1 pl2
  in if n<>0 then n
    else compare_can_spatial sl1 sl2

let rec compare_component_cprop (s1,p1) (s2,p2) =
  let n = compare_component s1 s2 in if n<>0 then n else
  compare_cprop p1 p2

and compare_component_cprop_list spl1 spl2 = 
  if spl1 == spl2 then 0 else match spl1 with
    | PNil -> -1
    | PCons (k1, v1, l1) -> begin match spl2 with
	| PNil -> 1
	| PCons (k2, v2, l2) ->
	    let n = compare_component k1 k2 in if n<>0 then n else
	    let n = compare_cprop v1 v2 in if n<>0 then n else
	    compare_component_cprop_list l1 l2
      end

and compare_cform ((cu1,spl1): cform) ((cu2,spl2): cform) =
  let n = compare_uform cu1 cu2 in if n<>0 then n else
  compare_component_cprop_list spl1 spl2

and compare_cprop cp1 cp2 =
  let rec f cfl1 cfl2 = match cfl1,cfl2 with
    | [],[] -> 0
    | [],_ -> -1
    | _,[] -> 1
    | cf1::cfl1', cf2::cfl2' ->
	let n = compare_cform cf1 cf2
	in if n<>0 then n
	  else f cfl1' cfl2'
  in f cp1 cp2

let mem_component_cprop y l =
  List.exists (fun x -> compare_component_cprop x y = 0) l


(* -------------------------------------------------------------------------- *)
(** {2 Spatial predicates} *)
(* -------------------------------------------------------------------------- *)

let tag_default = 1

let spred_bad =
  Csp_node (tag_default, component_of_string "**internal**", E.zero, Fld.emp)

let spred_node tag nid e fld = 
  if e == E.zero then spred_bad
  else Csp_node (tag, nid, e, fld)

(** [get_tag sp] returns the tag associated with [sp] *)
let get_tag sp = match sp with
  | Csp_node (tag, _, _, _)
  | Csp_listsegi (tag, _, _, _, _, _, _, _)
  | Csp_arr (tag, _, _, _, _, _, _)
  | Csp_indpred (tag, _, _) -> tag

(** [set_tag tag sp] returns an updated version of [sp] with its tag
    set to [tag]. *)
let set_tag tag sp = match sp with
  | Csp_node (tag', nid, e, fld) -> 
      if tag' == tag then sp else Csp_node (tag, nid, e, fld)
  | Csp_listsegi (tag', kind, e1, e2, e3, e4, ie, ds) ->
      if tag' == tag then sp else 
      Csp_listsegi (tag, kind, e1, e2, e3, e4, ie, ds)
  | Csp_arr (tag', e1, e2, e3, fld, ie, ds) -> 
      if tag' == tag then sp else Csp_arr (tag, e1, e2, e3, fld, ie, ds)
  | Csp_indpred (tag', i, el) ->
      if tag' == tag then sp else Csp_indpred (tag, i, el)

let spat_empty = []
let spat_one sp = [sp]
let spat_star_one sp sl = sp::sl
let spat_star sl1 sl2 = sl1@sl2

let spred_fold f sp acc = match sp with
  | Csp_listsegi (_,_,e1,e2,e3,e4,_,ds) ->
      Dset.fold f ds (f e4 (f e3 (f e2 (f e1 acc))))
  | Csp_arr (_,e1,e2,e3,_,_,ds) ->
      Dset.fold f ds (f e3 (f e2 (f e1 acc)))
  | Csp_node (_,_,e,fld) -> Fld.fold_val f fld (f e acc)
  | Csp_indpred (_,_,el) -> List.fold f el acc

let spat_fold f = List.fold (spred_fold f)
let spat_fold_spred = List.fold 

let spat_remove sl x = List.filter (fun y -> compare_can_spred y x <> 0) sl
let spat_get x sl = 
  let rec gosp r l = match l with
   | [] -> None
   | sp::l -> match sp with
      | Csp_node (_,_,e,_) 
      | Csp_listsegi (_,SINGLE _,e,_,_,_,_,_) ->
				if equal_exp x e then Some (sp, List.rev_append r l) else gosp (sp::r) l
      | Csp_listsegi (_,(DOUBLE _ | XOR _),e,_,f,_,_,_) ->
				if equal_exp x e || equal_exp x f then 
          Some (sp, List.rev_append r l) 
        else gosp (sp::r) l
      | Csp_arr (_,e1,e2,_,_,_,_) ->
				if equal_exp x e1 (* TODO!!!!!! *) then 
          Some (sp, List.rev_append r l) 
        else gosp (sp::r) l
      | Csp_indpred _ -> gosp (sp::r) l in
  gosp [] sl

(* -------------------------------------------------------------------------- *)
(** {2 Pretty printing} *)
(* -------------------------------------------------------------------------- *)

let rec pp_seq pp f = function
  | [] -> ()
  | [x] -> pp f x
  | x::l -> pp f x; pp_print_char f ','; pp_seq pp f l

let pp_disjoint_set f ds = match Dset.to_list ds with
  | [] -> ()
  | el -> fprintf f ",{%a}" (pp_seq pp_exp) el

let pp_isemp f ie = match ie with
  | Cem_PE -> () 
  | Cem_NE -> pp_print_string f "NE"

let pp_tag f tag = 
  if tag <> tag_default then begin 
    pp_print_char f '<';
    pp_print_int f tag;
    pp_print_char f '>'
  end

let pp_spred f = function
  | Csp_listsegi (tag,SINGLE(snode,cel),e1,f1,e2,_,ie,ds) ->
      let (what,ds) =
        if Dset.mem f1 ds then ("lseg",Dset.remove f1 ds) else ("lsegi",ds) in
      pp_tag f tag;
      pp_print_string f what;
      pp_isemp f ie;
      if cel != Fld.emp then begin
	pp_print_char f '[';
	pp_fld f cel;
	pp_print_char f ']'
      end;
      pp_print_char f '(';
      (if snode == Misc.list_link_tag then () else 
         pp_print_string f (string_of_component snode^";"));
      pp_seq pp_exp f [e1;f1;e2];
      pp_disjoint_set f ds;
      pp_print_char f ')'
  | Csp_listsegi (tag,DOUBLE(t1,t2),e1,f1,e2,f2,ie,el) ->
      pp_tag f tag;
      fprintf f "dlsegi%a(%s,%s;%a,%a,%a,%a%a)" pp_isemp ie
	(string_of_component t1) (string_of_component t2)
	pp_exp e1 pp_exp f1 pp_exp e2 pp_exp f2 pp_disjoint_set el
  | Csp_listsegi (tag,XOR t1,e1,f1,e2,f2,ie,el) ->
      pp_tag f tag;
      fprintf f "xlsegi%a(%s%a,%a,%a,%a%a)" pp_isemp ie
	(if t1 == Misc.dl_Llink_tag then "" else (string_of_component t1)^";")
	pp_exp e1 pp_exp f1 pp_exp e2 pp_exp f2 pp_disjoint_set el
  | Csp_node (tag,s, e1, cel) ->
      pp_tag f tag;
      if cel == Fld.emp then 
	fprintf f "@[%a|->_@]" pp_exp e1
      else
	fprintf f "@[%a|->%a@]" pp_exp e1 pp_fld cel
  | Csp_arr (tag,e1,e2,e3,cel,ie,ds) ->
      pp_tag f tag;
      pp_print_string f "arr";
      pp_isemp f ie;
      if cel != Fld.emp then begin
	pp_print_char f '[';
	pp_fld f cel;
	pp_print_char f ']'
      end;
      pp_print_char f '(';
      pp_seq pp_exp f [e1;e2;e3];
      pp_disjoint_set f ds;
      pp_print_char f ')'
  | Csp_indpred (tag,id,el) ->
      pp_tag f tag;
      fprintf f "%s(%a)" id (pp_seq pp_exp) el
 
let rec pp_starsep pp f = function
  | x::l ->
      pp f x;
      (match l with [] -> () | _ ->
	 Format.pp_print_space f ();
	 Format.pp_print_string f "* ";
	 pp_starsep pp f l)
  | [] -> Format.pp_print_string f "emp"

let rec pp_orsep pp f = function
  | x::l ->
      pp f x;
      (match l with [] -> () | _ ->
	 Format.pp_print_space f ();
	 Format.pp_print_string f "|| ";
	 pp_orsep pp f l)
  | [] -> Format.pp_print_string f "false"

let pp_uform f (pl,sl) = 
  Format.pp_open_box f 0;
  if Pure.is_true pl then
      pp_starsep pp_spred f sl
  else begin
    Pure.pp f pl;
    (match sl with [] -> () | _ ->
       Format.pp_print_space f ();
       Format.pp_print_string f "* ";
         pp_starsep pp_spred f sl)
  end;
  Format.pp_close_box f ()

let rec pp_cform f (uf,scpl) =
  match scpl with
    | PNil -> pp_uform f uf
    | PCons _ -> fprintf f "@[<hv>%a@ * %a@]" pp_uform uf pp_boxes scpl

and pp_cprop f (cp : cprop) =
  Format.pp_open_hvbox f 0;
  pp_orsep pp_cform f cp;
  Format.pp_close_box f ()

and pp_boxes f = function
  | PCons (s, cp, l) ->
      Format.pp_print_string f (string_of_component s);
      Format.pp_open_hvbox f 0;
      Format.pp_print_string f ":[";
      pp_orsep pp_cform f cp;
      Format.pp_print_char f ']';
      Format.pp_close_box f ();
      begin match l with
	| PNil -> ()
	| PCons _ ->
	    Format.pp_print_space f ();
	    Format.pp_print_string f "* ";
	    pp_boxes f l
      end
  | PNil -> ()

(** Pretty print an action *)
let pp_act pp act =
  Format.fprintf pp "@[%a@ |  %a@ ~~> %a@]"
    pp_uform (act.a_pure, List.filter (fun x -> get_tag x = 6) act.a_pre)
    (pp_starsep pp_spred) (List.filter (fun x -> get_tag x = 2) act.a_pre)
    pp_cprop act.a_post

(* -------------------------------------------------------------------------- *)
(** {2 Implementation} *)
(* -------------------------------------------------------------------------- *)

(** default values *)
let uform_empty : uform = (Pure.ptrue,spat_empty)
let uform_false : uform = (Pure.pfalse,spat_empty)
let cform_false = (uform_false,PNil)
let cprop_pure p = [((p,spat_empty),PNil)]
let cprop_spred sl = [((Pure.ptrue,sl),PNil)]
let cprop_uform uf = [(uf,PNil)]
let cprop_cform cf = [cf]
let cprop_empty = cprop_pure (Pure.ptrue)
let cprop_false = []

let cprop_box s p : cprop = [(uform_empty, PCons(s, p, PNil))]

let mk_array tag e1 e2 ev fld ds (p,sl) =
  match E.sub e2 e1 with
  | Enum 0 -> (Pure.conj_one (E.eq ev E.empty_list) p, sl)
  | Enum 1 ->
     let ev' = E.gensym_str_ex "VAL" in
     let fld = Fld.set list_data_tag ev' fld in
     let sp = spred_node tag node_component e1 fld in
     if sp == spred_bad then uform_false else
     (Pure.conj_one (E.eq ev (E.item ev')) p, sp :: sl)
  | Enum n when n < 0 -> uform_false
  | _ -> (p, Csp_arr(tag,e1,e2,ev,fld,Cem_PE,ds) :: sl)

let remove_uform_duplicates l =
  let l2 = List.stable_sort compare_uform l in
  let rec f = function
    | x::y::xs -> if compare_uform x y = 0 then f(y::xs) else x::(f(y::xs))
    | xs -> xs
  in f l2

let remove_cform_duplicates l =
  let l2 = List.stable_sort compare_cform l in
  let rec f = function
    | x::y::xs -> if compare_cform x y = 0 then f(y::xs) else x::(f(y::xs))
    | xs -> xs
  in f l2

let rec aggr_remove_cform_duplicates (l: cprop) =
  let l2 = List.stable_sort compare_cform l in
  let rec merge xs ys = match xs, ys with
    | PNil, ys -> ys
    | xs, PNil -> xs
    | PCons (s,x,xs0), PCons (s',y,ys0) ->
			let n = compare_component s s' in
			if n = 0 then PCons (s, remove_cform_duplicates (x @ y), 
                             merge xs0 ys0)
			else if n < 0 then PCons (s, x, merge xs0 ys)
			else PCons (s', y, merge xs ys0) in
  let rec f = function
    | (x,xsh)::(y,ysh)::xs ->
			if compare_uform x y = 0 then f ((y, merge xsh ysh)::xs)
			else (x,xsh)::(f((y,ysh)::xs))
    | xs -> xs in
  f l2

let ( @& ) = Pure.conj_one
let ( @&& ) = Pure.conj

let spred_fv   sp acc = spred_fold E.fv   sp acc
let spred_exfv sp acc = spred_fold E.exfv sp acc
let spred_fhd  sp acc = spred_fold E.fhd  sp acc

let (++) = IdSet.union

let spred_fv_fromTID sp acc = match sp with
  | Csp_node (_,_,e,fld) ->
      let go_fld c e (res,fv) = 
				let idset = E.fv e IdSet.empty 
				in
					(IdSet.mem Id.tid idset && res,
	 				if is_lock_field c then fv else idset ++ fv) 
			in
      let (res,fv) = Fld.fold go_fld fld (false, E.fv e acc) 
			in
      	if res then fv else acc
  | Csp_listsegi _
  | Csp_arr _
  | Csp_indpred _ -> acc

let uform_fv (p,sl) acc =
  List.fold spred_fv sl (Pure.fv p acc)

let uform_fhd (p,sl) acc =
  List.fold spred_fhd sl (Pure.fhd p acc)

let uform_fv_fromTID (p,sl) acc =
  List.fold spred_fv_fromTID sl acc

let rec form_fv (uf,scpl) acc =
  PList.fold_val prop_fv scpl (uform_fv uf acc)

and prop_fv (cp: cprop) acc =
  List.fold form_fv cp acc

let rec form_fhd (uf,scpl) acc =
  PList.fold_val prop_fhd scpl (uform_fhd uf acc)

and prop_fhd (cp: cprop) acc =
  List.fold form_fhd cp acc

let rec form_fv_fromTID (uf,scpl) acc =
  PList.fold_val prop_fv_fromTID scpl (uform_fv_fromTID uf acc)

and prop_fv_fromTID (cp: cprop) acc =
  List.fold form_fv_fromTID cp acc


(** Existential free variables only *)
let abs_fv_uform (p,sl) = 
  let rec go_exp e fv = match e with
    | Enum _ -> fv
    | Eident _ ->
        let i = Id.of_exp e in
        if Id.is_existential i && not (List.memq i fv) then i::fv else fv
    | Eeq (e,f) -> go_exp f (go_exp e fv)
    | Efun1 (_,e) -> go_exp e fv
    | Efun2 (_,e,f) -> go_exp f (go_exp e fv)
    | Efun (_,el) -> List.fold go_exp el fv
    | Egrp(_,_,nel) ->  ie_fold_exp go_exp nel fv in
  let go_spred sp fv = match sp with
    | Csp_listsegi (_,_,ce1,ce2,ce3,ce4,_,el) ->
        go_exp ce1 (
        go_exp ce2 (
        go_exp ce3 (
        go_exp ce4 (List.fold go_exp (Dset.to_list el) fv))))
    | Csp_arr (_,ce1,ce2,ce3,_,_,el) ->
        go_exp ce1 (
        go_exp ce2 (
        go_exp ce3 (List.fold go_exp (Dset.to_list el) fv)))
    | Csp_node (_,_,e,fld) ->
        Fld.fold_val go_exp fld (go_exp e fv)
    | Csp_indpred (_,i,el) -> List.fold go_exp el fv in
  let fv = List.fold go_spred sl [] in
  let fv = go_exp (Pure.to_exp p) fv in
  List.rev fv


let map_spred f_e sp = match sp with
  | Csp_listsegi (tag,k,e1,e2,e3,e4,ie,ds) ->
      let e1' = f_e e1 in
      let e2' = f_e e2 in
      let e3' = f_e e3 in
      let e4' = f_e e4 in
      if ie == Cem_NE && (e1' == E.zero || equal_exp e1' e2') then spred_bad
      else 
				let ds' = Dset.map f_e ds in
				if e1' == e1 && e2' == e2 && e3' == e3 && e4' == e4 && ds' == ds then sp
				else Csp_listsegi (tag, k, e1', e2', e3', e4', ie, ds')
  | Csp_arr (tag,e1,e2,e3,fld,ie,ds) ->
      let e1' = f_e e1 in
      let e2' = f_e e2 in
      let e3' = f_e e3 in
      if ie == Cem_NE && (equal_exp e1' e2') then spred_bad
      else 
				let ds' = Dset.map f_e ds in
        let fld' = Fld.map f_e fld in
				if e1' == e1 && e2' == e2 && e3' == e3 && fld' == fld && ds' == ds then sp
				else Csp_arr (tag, e1', e2', e3', fld', ie, ds')
  | Csp_node (tag,nid,e,fld) ->
      let e' = f_e e in
      let fld' = Fld.map f_e fld in
      if e' == e && fld' == fld then sp 
      else spred_node tag nid e' fld'
  | Csp_indpred (tag,id,el) -> Csp_indpred (tag,id, List.map f_e el)

let map_spred_opt f_e sp =  match sp with
  | Csp_listsegi (tag,k,e1,e2,e3,e4,ie,ds) -> 
      let e1' = f_e e1 in
      let e2' = f_e e2 in
      let e3' = f_e e3 in
      let e4' = f_e e4 in
      (e1'!=e1 || e2'!=e2 || e3'!=e3 || e4'!=e4,
       if ie == Cem_NE && (e1' == E.zero || equal_exp e1' e2') then spred_bad
       else
	 			let ds' = Dset.map f_e ds in
	 			if e1' == e1 && e2' == e2 && e3' == e3 && e4' == e4
            && ds' == ds then sp
	 			else Csp_listsegi (tag, k, e1', e2', e3', e4', ie, ds'))
  | Csp_arr (tag,e1,e2,e3,fld,ie,ds) ->
      let e1' = f_e e1 in
      let e2' = f_e e2 in
      let e3' = f_e e3 in
      (e1'!=e1 || e2'!=e2 || e3'!=e3,
       if ie == Cem_NE && (equal_exp e1' e2') then spred_bad
       else 
         let ds' = Dset.map f_e ds in
         let fld' = Fld.map f_e fld in
         if e1' == e1 && e2' == e2 && e3' == e3 
           && fld' == fld && ds' == ds then sp
         else Csp_arr (tag, e1', e2', e3', fld', ie, ds'))
  | Csp_node (tag, nid, e, fld) ->
      let e' = f_e e in
      let fld' = Fld.map f_e fld in
      (e' != e,
       if e' == e && fld' == fld then sp
       else spred_node tag nid e' fld')
  | Csp_indpred (tag,id,el) -> (true, Csp_indpred (tag, id, List.map f_e el))

let map_spat f_e =
  if f_e == identity then identity else
  map_sub (map_spred f_e)

let map_spat_opt f_e =
  if f_e == identity then (fun x y -> List.rev_append y x) 
	else
  	let rec go acc sl = match sl with
    	| sp::sl ->
				let sp = map_spred f_e sp in
				if sp == spred_bad then [sp]
				else go (sp::acc) sl
    	| [] -> acc
  	in go

let map_spat_opt2 f_e =
  if f_e == identity then (fun sl -> ([], sl)) 
	else
	  let rec go sl1 sl2 sl = match sl with
	    | sp::sl ->
				let (changed,sp) = map_spred_opt f_e sp in
				if sp == spred_bad then ([sp],[])
				else if changed then go (sp::sl1) sl2 sl
				else go sl1 (sp::sl2) sl
	    | [] -> (sl1, sl2)
	  in go [] []

(** [None = identity substitution] *)
let fhd_to_sub fhd =
  match List.filter Id.is_existential (IdSet.elements fhd) with
    | [] -> None
    | fhd ->
	let f x =
	  let id1 = E.id (Id.gensym_garb x) in
	  let id2 = E.id (Id.gensym_garb x) in
	  let exp = E.list [E.item id1; id2] in
	  (x, (id1,exp)) in
	let fhd = List.map f fhd in
	let sub =
	  mk_fun_subst 
	    (fun e -> match e with 
	       | Efun1 (Sfn_hd,(Eident _ as e')) -> 
		   begin try fst (List.assq (Id.of_exp e') fhd)
                         with Not_found -> e end
	       | _ -> e) in
	Some sub


let rec def_alloc tag x sl = match sl with
  | Csp_node (tag',_,y,_) :: sl ->
      if equal_exp x y then tag' land tag <> 0 else def_alloc tag x sl
  | Csp_listsegi (tag',SINGLE _,y,_,_,_,Cem_NE,_) :: sl ->
      if equal_exp x y then tag' land tag <> 0 else def_alloc tag x sl
  | Csp_listsegi (tag',(DOUBLE _ | XOR _),y,_,z,_,Cem_NE,_) :: sl ->
      if equal_exp x y || equal_exp x z then tag' land tag <> 0
      else def_alloc tag x sl
  | _ :: sl -> def_alloc tag x sl
  | [] -> false

let rec maybe_alloc x sl = match sl with
  | Csp_node (_,_,y,_) :: sl -> equal_exp x y || maybe_alloc x sl
  | Csp_listsegi (_,SINGLE _,y,_,_,_,_,_) :: sl ->
      equal_exp x y || maybe_alloc x sl
  | Csp_listsegi(_,(DOUBLE _ | XOR _),y,_,z,_,_,_) :: sl ->
      equal_exp x y || equal_exp x z || maybe_alloc x sl
  | _ :: sl -> maybe_alloc x sl
  | [] -> false


(** Assuming that [(Pure.ptrue,sl)] is already in normal form,
    [do_update_pure p_new slu sl res = normalize (p_new, slu @ sl) @ res]. *)
(* called as do_update_pure p sl [] [] *)		
let rec do_update_pure p_new slu sl q = 
  if Pure.is_false p_new then q
  else
		let sub = Pure.to_sub p_new in
    let (sl1, sl2) = map_spat_opt2 sub sl in
		let slu = map_spat_opt sub sl1 slu in
		(* (p_new, sl2) is already normalized. Focusing on slu. *)
		add_nodes p_new slu sl2 q


(** Assuming that [(p,sl)] is already in normal form and [sp] starts at address
    [x], [add_node sp x p slu sl res = normalize (p, sp::slu@sl) @ res]. *)
and add_node sp x p slu sl q =
    let is_interesting x sp = match sp with
      | Csp_node(_,_,y,_) -> equal_exp x y
      | Csp_listsegi(_,SINGLE _,y,_,_,_,_,_) -> equal_exp x y
      | Csp_listsegi(_,(DOUBLE _ | XOR _),y,_,z,_,_,_) ->
          equal_exp x y || equal_exp x z
      | _ -> false 
		in
  		if List.exists (is_interesting x) sl then 
				begin
    			let (sp',sl) = get_first (is_interesting x) sl 
					in
    				match sp, sp' with
      				| Csp_node (tag,nid,_,fld), Csp_node (tag',nid',_,fld') ->
	  						if tag land tag' = 0 && nid == nid' then (* Compatible *)
	  								let (eq,fld) = Fld.components_equal fld fld' 
										in
	  									do_update_pure (eq @& p) slu (Csp_node (tag lor tag', nid, x, fld) :: sl) q
								else q 
    					| (Csp_node (tag,nid,_,fld) as sp0), 
       					Csp_listsegi (tag',(SINGLE(snode,fld') as kind),_,e2,e3,_,ie,ds)
    					| Csp_listsegi (tag',(SINGLE(snode,fld') as kind),_,e2,e3,_,ie,ds),
     						(Csp_node (tag,nid,_,fld) as sp0) ->
								let q = (* Case: lseg is non-empty *)
	  							if tag land tag' = 0 then (* Consisent => unroll lseg *)
	    							let t = if component_is_field snode then snode else assert false (* TODO *) in
	    							let (e_next,fld) = Fld.get_extend t fld in
	    							let (e_val,fld) = Fld.get_extend list_data_tag fld in
	    							let (eq,fld) = Fld.components_equal fld fld' in
	    							let e_val_rest = E.gensym_str_ex "VAL" in
	    							let eq2 = E.eq (E.list [E.item e_val; e_val_rest]) e3 in
	    							do_update_pure (eq @& eq2 @& p)
	      							(Csp_listsegi (tag',kind,e_next,e2,e_val_rest,E.zero,Cem_PE,ds) :: slu)
	      							(Csp_node (tag lor tag', nid, x, fld) :: sl)
	      							q
	  							else q 
								in
								let q = match ie with
	  							| Cem_PE -> do_update_pure (E.eq x e2 @& E.eq E.empty_list e3 @& p) slu (sp0 :: sl) q
	  							| Cem_NE -> q 
								in q
    					| Csp_listsegi (tag, SINGLE(snode,fld),_,e2,e3,_,ie,ds), 
      					Csp_listsegi (tag', SINGLE(snode',fld'),_,e2',e3',_,ie',ds') ->
								if tag land tag' = 0 then (* Compatible *)
	  							let _ = if snode == snode' then () else (Misc.pp "@.snode is %a and snode' is %a@." pp_spred sp 
									pp_spred sp'; assert false) in
	  							let (eq, fldU) = Fld.components_equal fld fld' in
	  							let tagU = tag lor tag' in
	  							let dsU = Dset.union ds ds' in
	  							let e_val = E.gensym_str_ex "VAL" in
	  							let p = eq @& p in
	  							let (ie1, ie1') = match ie, ie' with 
            				| Cem_PE, Cem_NE -> (Cem_NE, Cem_PE)
            				| _ -> (Cem_PE, Cem_NE) 
									in
									  do_update_pure (E.eq e3' (E.list [e3; e_val]) @& p)
									    (Csp_listsegi (tag', SINGLE(snode',fld'),e2,e2',e_val,E.zero,ie1,ds') :: slu)
									    (Csp_listsegi (tagU, SINGLE(snode,fldU),x,e2,e3,E.zero,ie,dsU) :: sl)
									    (do_update_pure (E.eq e3 (E.list [e3'; e_val]) @& p)
									       (Csp_listsegi (tag, SINGLE(snode,fld),e2',e2,e_val,E.zero,ie1',ds) :: slu)
									       (Csp_listsegi (tagU, SINGLE(snode,fldU),x,e2',e3',E.zero,ie',dsU) :: sl)
									       q)
								else (* One lseg must be empty *)
	  							let q = match ie with
	    							| Cem_PE -> 
												do_update_pure (E.eq x e2 @& E.eq E.empty_list e3 @& p) slu (sp' :: sl) q
	    							| Cem_NE -> q 
									in
	  								let q = match ie' with
	    								| Cem_PE -> 
												do_update_pure (E.eq x e2' @& E.eq E.empty_list e3' @& p) slu (sp :: sl) q
	    								| Cem_NE -> q 
										in q
    					| _ -> assert false (* Not implemented *) 
  			end 
			else add_nodes p slu (sp :: sl) q

(** Assuming that [(p,sl)] is already in normal form,
    [add_nodes p slu sl res = normalize (p, slu @ sl) @ res]. *)
and add_nodes p slu sl q = match slu with
  | sp :: slu -> 
		begin match sp with
  		| Csp_node (_,_,x,_) -> 
	  		begin match x with 
	    		| Enum 0 -> q
	    		| _ -> add_node sp x p slu sl q
	  		end
      | Csp_listsegi(tag,(SINGLE _ as kind),x,y,v,_,ie,ds) ->
			  if (match x with Enum 0 -> true | _ -> 
					Dset.mem x ds
					|| equal_exp x y && (maybe_alloc y sl || maybe_alloc y slu)
					|| equal_exp v E.empty_list) then 
					begin
	   				match ie with
	      			| Cem_NE -> q
	      			| Cem_PE -> do_update_pure 
                            (E.eq x y @& E.eq v E.empty_list @& p) slu sl q
	  			end 
				else
	    		let sp = 
	      		if (match ie with Cem_NE -> false | Cem_PE -> true)
							&& Pure.is_false (E.eq x y @& E.eq v E.empty_list @& p) then
							Csp_listsegi (tag,kind,x,y,v,E.zero,Cem_NE,ds)
	      		else sp 
					in
	    			add_node sp x p slu sl q
      | Csp_arr(tag,x,y,v,fld,ie,ds) ->
	  		if (match x with Enum 0 -> true | _ -> 
					Dset.mem x ds || equal_exp x y || equal_exp v E.empty_list) then 
					begin
	    			match ie with
	      			| Cem_NE -> q
	      			| Cem_PE -> do_update_pure 
                            (E.eq x y @& E.eq v E.empty_list @& p) slu sl q
	  			end 
				else
	    		let sp = 
	      		if (match ie with Cem_NE -> false | Cem_PE -> true)
							&& Pure.is_false (E.eq x y @& E.eq v E.empty_list @& p) then
							Csp_arr (tag,x,y,v,fld,Cem_NE,ds)
	      		else sp 
					in
	    			add_node sp x p slu sl q
      | _ -> assert false
    end
  | [] -> (p, sl) :: q
 
let normalize_uform (p,sl) =
  do_update_pure p sl [] []

let map_uform f_e (p,sl) =
  let p' = Pure.map f_e p in
  let sl' = map_spat f_e sl in
  if Pure.identical_eq p' p && sl' == sl then [(p', sl')]
  else
    normalize_uform (p', sl')

(* Very simplistic *)
let normalize_cform ((uf,scpl) : cform) =
  if PList.exists (fun _ cp -> cp == []) scpl then
    cprop_false
  else
    List.map (fun uf -> (uf,scpl)) (normalize_uform uf)

let normalize_cprop cp =
  List.fold_append normalize_cform cp []

let rec map_cform_app f_e (uf,scpl) res = match map_uform f_e uf with
  | [] -> res
  | ufl ->
      let scpl' = PList.map_val (map_cprop f_e) scpl in
      List.fold_cons (fun uf -> (uf,scpl')) ufl res

and map_cprop f_e cp =
  List.reduce (map_cform_app f_e) cp

let map_cform f_e cf = map_cform_app f_e cf []

let naive_map_uform sub (p,sl) =
  (Pure.map sub p, map_spat sub sl)

let rec naive_map_cform f_e (uf,scpl) =
  (naive_map_uform f_e uf, PList.map_val (naive_map_cprop f_e) scpl)

and naive_map_cprop f_e (cp: cprop) =
  List.fold (fun cf q -> naive_map_cform f_e cf :: q) cp []

(** Replace annoying [hd(_temp)] with a fresh [_temp']. *)
let uform_kill_hd_vars uf =
  match fhd_to_sub (uform_fhd uf IdSet.empty) with
    | None -> uf 
    | Some sub -> naive_map_uform sub uf

(** Replace annoying [hd(_temp)] with a fresh [_temp']. *)
let form_kill_hd_vars (cf : cform) =
  let cf = 
    match fhd_to_sub (form_fhd cf IdSet.empty) with
      | None -> cf 
      | Some sub -> naive_map_cform sub cf
  in
  cf

(** Replace annoying [hd(_temp)] with a fresh [_temp']. *)
let prop_kill_hd_vars cp =
  match fhd_to_sub (prop_fhd cp IdSet.empty) with
    | None -> cp
    | Some sub -> naive_map_cprop sub cp

let normalize_uform x = normalize_uform (uform_kill_hd_vars x)
let normalize_cform x = 
  prop_kill_hd_vars (normalize_cform (form_kill_hd_vars x))
let normalize_cprop x =
  prop_kill_hd_vars (normalize_cprop (prop_kill_hd_vars x))
let map_cform f_e cf = prop_kill_hd_vars (map_cform f_e cf)
let map_cprop f_e cp = prop_kill_hd_vars (map_cprop f_e cp)

let map_ip_body f_e body =
  let f res (p,cf) = 
    let pl = Pure.normalize (Pure.map f_e p) in
    match pl with [] -> res (* Optimisation *) | _ ->
    let cfl = map_cform f_e cf in
    List.fold_left (fun acc p -> List.fold_left (fun acc cf -> (p,cf)::acc) acc cfl) res pl in
  List.fold_left f [] body


(** @deprecated unify [e1] and [e2] instantiating existential variables in [e2]. *)
let unify_exp inst e1 e2 = 
  let rec go (inst,pl) e1 e2 = match (e1,e2) with
    | e1, Eident _ ->
      (try 
	let e3 = List.assq (Id.of_exp e2) inst in
	go (inst,pl) e1 e3
      with Not_found -> 
	if existential_id e2 then
	  let i2 = Id.of_exp e2 in
	  let sub = mk_single_subst i2 e1 in
	  let inst = List.map (fun (t,e) -> (t,sub e)) inst in
	  Some ((i2,e1)::inst, pl)
	else if equal_exp e1 e2 then Some (inst,pl)
	else None)
    | Enum n1, Enum n2 -> if n1 = n2 then Some (inst,pl) else None
    | e1, e2 -> if equal_exp e1 e2 then Some (inst,pl) else None
  and go_list res el1 el2 = match (el1,el2) with
    | [], [] -> Some res
    | [],_::_ -> None 
    | _::_,[] -> None
    | e1::el1,e2::el2 ->
	begin match go res e1 e2 with 
	  | None -> None
	  | Some res -> go_list res el1 el2
	end
  in
  go (inst,Pure.ptrue) e1 e2 

let ie_leq = function 
    (Cem_PE, _) -> true 
  | (Cem_NE, Cem_PE) -> false
  | (Cem_NE, Cem_NE) -> true

let can_spred_leq csp1 csp2 = match (csp1,csp2) with
  | (Csp_listsegi(tag,SINGLE(s1,cel),e1,f1,e2,f2,ie,el),
     Csp_listsegi(tag',SINGLE(s1',cel'),e1',f1',e2',f2',ie',el')) ->
      if tag == tag' && s1==s1' && equal_exp e1 e1' && ie_leq (ie, ie')
        && Fld.fold (fun t e r -> r && Fld.mem t e cel) cel' true
        && Dset.subset el' el then
	if equal_exp f1 f1' then E.eq e2 e2'
        else if equal_exp e2 e2' then E.eq f1 f1'
	else E.zero
      else E.zero
  | (Csp_listsegi(tag,k1,e1,f1,e2,f2,ie,el),
     Csp_listsegi(tag',k1',e1',f1',e2',f2',ie',el')) ->
      if tag == tag' && compare_lkind k1 k1' = 0 && equal_exp e1 e1'
        && equal_exp f1 f1' && equal_exp e2 e2' && equal_exp f2 f2'
        && ie_leq (ie, ie') && Dset.subset el' el 
	then E.one
	else E.zero
  | (csp1,csp2) -> 
	if compare_can_spred csp1 csp2 = 0 then E.one else E.zero

let scpl_filter p1 x =
  PList.map_val
    (List.filter 
       (fun ((p,_),_) -> 
	  let p' = Pure.conj p1 p in
	  let pl' = Pure.normalize_aggr p' in
	  pl' != [])) x

let normalize_cform_aggr ((p,sl),scpl) =
  let gonorm p res = 
    let scpl = scpl_filter p scpl in
    if PList.exists (fun _ v -> v == []) scpl then res
    else ((p,sl),scpl) :: res in
  List.reduce gonorm (Pure.normalize_aggr p)

(* Removes inconsistencies *)
let cform_star_inner ((pl1,sl1),scpl1) ((pl2,sl2),scpl2) res = 
  assert (PList.for_all (fun x _ -> not (PList.mem_assq x scpl2)) scpl1);
  let p = Pure.conj pl1 pl2 in
  let scpl2 = scpl_filter p scpl2 in
  let scpl1 = scpl_filter p scpl1 in
  normalize_cform ((p, List.rev_append sl1 sl2), 
                      PList.rev_append scpl1 scpl2) @ res

(* Removes inconsistencies *)
let cprop_star cp1 cp2 =
  List.fold (fun cf1 -> List.fold (cform_star_inner cf1) cp2) cp1 []

(* TODO *)
let cform_star ((pl1,sl1),scpl1) ((pl2,sl2),scpl2) = 
  assert (PList.for_all (fun x _ -> not (PList.mem_assq x scpl2)) scpl1);
  Some ((Pure.conj pl1 pl2, List.rev_append sl1 sl2), 
        PList.rev_append scpl1 scpl2)

let and_cprop_pure cp p = cprop_star (cprop_pure p) cp

let cprop_or cp1 cp2 =
  aggr_remove_cform_duplicates (List.rev_append cp1 cp2)

let rec is_pure cp =
  List.for_all (function ((_,[]),_)->true | _ -> false) cp

let is_cprop_empty = is_pure


(** Flatten the preconditon proposition *)
let flatten_condition cp = 
	let rec flatten_condition_rec (cp : cprop) : uform list list = 
		let rec extend (ufs : uform list list) splist : (uform list list) = match splist with
			| PNil -> ufs
			| PCons (rid, cp', splist') ->
				let ufsl = flatten_condition_rec cp' in
				let ufsl = List.tflap2 (ufs, ufsl) (fun c d -> c @ d) in
				extend ufsl splist' in
		List.flatten (List.map (fun (uf, scpl) -> 
				extend [[uf]] scpl
			) cp) in
	let result = flatten_condition_rec cp in
	List.map (fun ufs ->
		cprop_cform (List.fold_left (fun res uf -> 
		match cform_star (uf, PNil) res with
			| None -> assert false 
			| Some ufres -> ufres
			) (uform_empty, PNil) ufs)
		) result

(* -------------------------------------------------------------------------- *)
(** {2 Existential variables } *)
(* -------------------------------------------------------------------------- *)

let rec form_exfv ((p,sl),scpl) acc =
  PList.fold_val prop_exfv scpl
    (spat_fold E.exfv sl (Pure.exfv p acc))

and prop_exfv (cp: cprop) acc =
  List.fold form_exfv cp acc

let fv_norm_cprop cp =
  let fv = prop_fv cp IdSet.empty in
  IdSet.filter (fun x -> not (Id.is_existential x)) fv

(** Important variables not to be treated as garbage. *)
let spred_exfv_keep sp acc = 
  let go_fld c e res = 
    if is_value_field c || is_lock_field c then E.exfv e res
    else res in
  match sp with
  | Csp_node (_,_,e,fld) -> Fld.fold go_fld fld (E.exfv e acc)
  | Csp_listsegi (_,_,e1,e2,e3,e4,_,ds) ->
      E.exfv e1 (E.exfv e2 (E.exfv e3 (E.exfv e4 acc)))
  | Csp_arr (_,e1,e2,e3,_,_,ds) ->
      E.exfv e1 (E.exfv e2 (E.exfv e3 acc))
  | Csp_indpred _ -> spred_fold E.exfv sp acc

(** Important variables not to be treated as garbage *)
let rec form_exfv_keep ((_,sl),scpl) acc = 
  PList.fold_val prop_exfv_keep scpl
    (List.fold spred_exfv_keep sl acc)

and prop_exfv_keep cp = List.fold form_exfv_keep cp

let form_fv_more_keep (((_,sl),scpl): cform) = 
  IdSet.inter (List.fold spred_fv sl IdSet.empty)
              (PList.fold_val prop_fv scpl IdSet.empty)

let uform_fv_killable ((p,sl) : uform) =
  IdSet.diff
    (Pure.exfv p IdSet.empty) 
    (spat_fold E.exfv sl IdSet.empty) 

let form_fv_killable (cf : cform) =
  let s = form_exfv cf IdSet.empty in
  let s = IdSet.diff s (form_exfv_keep cf (form_fv_more_keep cf)) in
  s

let fv_common f l = match l with
  | [] -> IdSet.empty
  | x :: l -> List.fold (fun x -> IdSet.inter (f x)) l (f x)

let prop_fv_killable = fv_common form_fv_killable
let uform_list_fv_killable = fv_common uform_fv_killable

let uform_kill_vars kill ((p,sl) as uf) =
  let myfilter e = IdSet.is_empty (IdSet.inter (E.exfv e IdSet.empty) kill) in
  let myfilter_snd _ e = myfilter e in
  let kill_fn sp = match sp with
    | Csp_node (tag,s,e,fld) ->
			let fld' = Fld.filter myfilter_snd fld in 
			if fld' == fld then sp 
			else
        Csp_node (tag,s,e,fld')
    | Csp_listsegi (tag,k,e1,f1,e2,f2,ie,ds) ->
			let ds' = Dset.filter myfilter ds in
			if ds' == ds then sp 
			else
				Csp_listsegi (tag,k,e1,f1,e2,f2,ie,ds')
    | _ -> sp 
	in
  	let p' = Pure.kill_vars kill p in
  	let sl' = map_sub kill_fn sl in
  	if p' == p && sl' == sl then uf else (p', sl')

let rec form_kill_vars kill ((uf,scpl) as cf) =
  let uf' = uform_kill_vars kill uf in
  let scpl' = PList.map_val (prop_kill_vars kill) scpl in
  if uf' == uf && scpl' == scpl then cf else (uf', scpl')

and prop_kill_vars kill (cp : cprop) =
  map_sub (form_kill_vars kill) cp

let rec form_kill_can_return (((p,sl),scpl) as cf) =
  let p' = Pure.kill_can_return p in
  let scpl' = PList.map_val prop_kill_can_return scpl in
  if p' == p && scpl' == scpl then cf else ((p', sl), scpl')

and prop_kill_can_return (cp : cprop) =
  map_sub form_kill_can_return cp

let kill_garbage_vars cp =
  prop_kill_vars (fv_common form_fv_killable cp) cp

let kill_garbage_vars_ufl ufl = 
  map_sub (uform_kill_vars (fv_common uform_fv_killable ufl)) ufl

let aggr_kill_garbage_vars cp =
  map_sub (fun cf -> form_kill_vars (form_fv_killable cf) cf) cp

(** Return all free variables of [cp] not directly reachable from the set [s] *)
let fv_killable_vars2 s cp =
  let sr = ref s in
  let go_spred = function
    | Csp_node (_,_,ce, fld) ->
      if E.forall_fv (fun x -> IdSet.mem x !sr) ce then  
        sr := Fld.fold_val E.fv fld (!sr)
    | _ -> () in
  let go_cprop cp = List.iter (fun((_,sl),_) -> List.iter go_spred sl) cp in
  let rec fix () =
     let s = !sr in
     go_cprop cp; 
     if IdSet.equal !sr s then () else fix () in
  fix ();
  IdSet.diff (prop_fv cp IdSet.empty) !sr

let kill_dead_vars lv cp =
  let killfv = (fv_killable_vars2 lv cp) in
  if IdSet.is_empty killfv then cp
  else
    map_cprop (existentials_rename_sub killfv) cp


(* -------------------------------------------------------------------------- *)
(** {2 Actions } *)
(* -------------------------------------------------------------------------- *)

let spred_no_s s sp = match sp with
  | Csp_listsegi (_,_,e1,e2,e3,e4,_,ds) ->
      exp_no_s s e1 && exp_no_s s e2 && exp_no_s s e3
      && exp_no_s s e4 && Dset.no_s s ds
  | Csp_arr (_,e1,e2,e3,fld,_,ds) ->
      exp_no_s s e1 && exp_no_s s e2 && exp_no_s s e3
      && Fld.no_s s fld && Dset.no_s s ds
  | Csp_node (_,_,e,fld) -> exp_no_s s e && Fld.no_s s fld
  | Csp_indpred (_,_,el) -> List.for_all (exp_no_s s) el

let rec form_no_s s ((p,sl),scpl) =
  Pure.no_s s p 
  && List.for_all (spred_no_s s) sl
  && PList.for_all (fun _ cp -> prop_no_s s cp) scpl

and prop_no_s s = List.for_all (form_no_s s)

let act_id_string = "?a"
let act_ids = idpool_new Id.gensym_str_ex act_id_string

(** Create a new set of actions: [new_acts name ctx pre post] *)
let new_acts name ctx pre post =
  let mk s (((p1,c),_) as cf_ctx) (((p2,p),_) as cf_p) q =
    let exfv = form_exfv cf_ctx (form_exfv cf_p (prop_exfv q IdSet.empty)) in
    let sub = mk_subst (idpool_combine act_ids (IdSet.elements exfv)) in
    { a_name = s;
      a_exvars = map_idset sub exfv;
      a_pure = Pure.map sub (Pure.conj p1 p2);
      a_pre  = map_spat sub (List.map (set_tag 2) c @ List.map (set_tag 6) p);
      a_post = map_cprop sub q }
  in
  let (ctx,pre,post) = 
    let otid = E.gensym_str_ex "otherTID" in
    let sub = mk_subst (PCons (Id.mytid, E.tid, PCons (Id.tid, otid, PNil))) in
    let pl = E.neq otid E.zero @& E.neq otid E.tid @& Pure.ptrue in
    (map_cprop sub ctx,
     and_cprop_pure (map_cprop sub pre) pl,
     map_cprop sub post)
  in
  let n = List.length ctx * List.length pre in
  if n = 1 then
    [mk name (List.hd ctx) (List.hd pre) post]
  else
    snd 
      (List.fold
	 (fun c ->
	    List.fold
	      (fun p (n,r) ->
		 (n+1,mk (name^"#"^string_of_int n) c p post :: r))
	      pre)
	 ctx
	 (1,[]))


(** Return the name of an action *)
let act_name act = act.a_name

(* -------------------------------------------------------------------------- *)
(** {2 May Subtraction Implementation } *)
(* -------------------------------------------------------------------------- *)

let normalize_append uf ufl = 
  List.rev_append (normalize_uform uf) ufl


(** [(s minus x|->nid(fld)_tag) * p * sl] *)
let rec rem_ptsto_spred tag nid x fld p (s,sl) acc =
  let mk_listseg (tag,k,e1,f1,e2,f2,ds) (p,sl) = 
    if equal_exp e1 f1 && Dset.mem f1 ds then
      (E.eq e2 E.empty_list @& p, sl)
    else (p, Csp_listsegi(tag,k,e1,f1,e2,f2,Cem_PE,ds) :: sl) 
	in
  match s with 
  | Csp_node (tag',nid',e,fld') ->
      assert (tag' == 1);
      if nid' != nid then acc
      else
				let (eq, fld) = Fld.components_equal fld fld' 
				in
					normalize_append
	  				(E.eq e x @& eq @& p, 
	   					Csp_node (tag lor 1, nid, e, fld) :: sl)
	  			acc
  | Csp_listsegi (tag',SINGLE(snode,flds),e1,e2,e3,_,_,ds) ->
      assert (tag' == 1);
      let t = if component_is_field snode then snode
              else assert false (* TODO *) in
      let (e,fld) = Fld.get_extend t fld in
      let e3a = E.gensym_str_ex "VAL" in
      let e3b = E.gensym_str_ex "VAL" in
      let (e3c,fld) = Fld.get_extend Misc.list_data_tag fld in
      let (eq,fld) = Fld.components_equal fld flds in
      let p = 
				List.fold (fun y res -> E.neq x y @& res) 
					(Dset.to_list ds)
	  			(E.eq e3 (E.list [e3a; E.item e3c; e3b]) @& eq @& p) 
			in
      if Pure.is_false p then acc (* Optimisation *) else
			normalize_append
	  		(mk_listseg (1,SINGLE(snode,flds),e1,x,e3a,E.zero,ds)
	     		(mk_listseg (1,SINGLE(snode,flds),e,e2,e3b,E.zero,ds)
						(p, Csp_node (tag lor 1, nid, x, fld) :: sl)))
	  		acc
  | Csp_listsegi (_,_,_,_,_,_,_,_) -> assert false
  | Csp_arr (tag',e1,e2,e3,flds,_,ds) ->
      assert (tag' == 1);
      let e3a = E.gensym_str_ex "VAL" in
      let e3b = E.gensym_str_ex "VAL" in
      let (e3c,fld) = Fld.get_extend Misc.list_data_tag fld in
      let (eq,fld) = Fld.components_equal fld flds in
      let p = 
				List.fold (fun y res -> E.neq x y @& res) 
					(Dset.to_list ds)
	  			(E.eq e3 (E.list [e3a; E.item e3c; e3b]) @& eq @& p) 
			in
      if Pure.is_false p then acc (* Optimisation *) else
			normalize_append
	  		(mk_array 1 e1 x e3a flds ds
	     		(mk_array 1 (E.add x E.one) e2 e3b flds ds
						(p, Csp_node (tag lor 1, nid, x, fld) :: sl)))
	  	acc
  | Csp_indpred _ -> assert false (* TODO *)

(** [sl1 minus e|->nid(fld)_tag] *)
let rec rem_ptsto tag nid e fld (p,sl1) =
  let rec get_splittings sl1 sl2 acc = match sl2 with 
    | [] -> acc
    | sp :: sl3 ->
			let acc = 
	  		if get_tag sp == 1 then
	    		(sp, List.rev_append sl1 sl3) :: acc
	  		else acc 
			in
				get_splittings (sp :: sl1) sl3 acc in
  let res = (* remove x|->_ from each atomic spatial predicate *)
    List.fold (rem_ptsto_spred tag nid e fld p)
      (get_splittings [] sl1 []) [] 
	in
  if !allow_leaks then 
    (* might also remove x|->_ from the implicit ``* true'' *)
    normalize_append 
      (p, Csp_node (tag lor 1, nid, e, fld) :: sl1)
      res
  else 
    res

(** [interfere_once prover act cp] calculate the effect of applying
    interference [act] to [cp]. *)
let interfere_once prover act cp =
  let rec loop (p,sl) acc = 
    if List.for_all (fun x -> get_tag x land 1 = 1) sl then
      (p, List.fold (fun x r -> if get_tag x <= 3 then set_tag 1 x :: r else r) sl [])
      :: acc
    else
      let (sp,sl) = get_first (fun x -> get_tag x land 1 = 0) sl in
      match sp with
				| Csp_node (tag,nid,e,fld) ->
	    		List.fold loop (rem_ptsto tag nid e fld (p,sl)) acc
				| Csp_listsegi (2,_,_,_,_,_,_,_) ->
	    		pp "WARN Ignore LSEG: %a@." pp_uform (p,sp::sl);
	    		loop (p,sl) acc
				|  _ -> assert false
  in
  (* 1. Rename existential variables in [act] as they might appear in [cp] *)
  let (act_pure, act_pre, act_post) =
    if prop_no_s act_id_string cp then
      (act.a_pure, act.a_pre, act.a_post)
    else
      let sub = existentials_rename_sub act.a_exvars in
      (Pure.map sub act.a_pure,
       map_spat sub act.a_pre,
       map_cprop sub act.a_post) 
	in
  (* 2. Perform subtraction elimination. *)
  cprop_star act_post
    (List.reduce (fun ((p,sl),scpl) acc ->
			let ufl = normalize_uform (Pure.conj act_pure p, spat_star act_pre sl) in
			let ufl = List.reduce loop ufl in
			List.fold (fun uf acc -> (uf,scpl)::acc) ufl acc) cp)


