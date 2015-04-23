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

(* -------------------------------------------------------------------------- *)
(** {2 Data types} *)
(* -------------------------------------------------------------------------- *)

type sfn1 = 
  | Sfn_NOT
  | Sfn_item
  | Sfn_sorted
  | Sfn_hd
  | Sfn_tl
  | Sfn_set_of_list
  | Sfn_can_return

type sfn2 =
  | Sfn_list_lt
  | Sfn_subset
  | Sfn_set_minus

type sfn =
  | Sfn_list
  | Sfn_set
  | Sfn_AND
  | Sfn_OR
  | Sfn_XOR
  | Sfn_undef

type sfn_grp =
  | Sfn_plus
  | Sfn_pos

(** parameters for identifiers, in priority order *)
type id_kind = EXIST_RENAMED | EXIST_ORIG | NORMAL_RENAMED | NORMAL_ORIG

type id_internal1 = id_kind
type id_internal2 = int
type id_internal3 = string

(** NB: Expressions are kept in a canonical form.
    Do not create them directly: use the constructors instead.
*)
type exp =
  | Enum of int
  | Eident of id_internal1 * id_internal2 * id_internal3
  | Eeq of exp * exp
  | Efun1 of sfn1 * exp
  | Efun2 of sfn2 * exp * exp
  | Efun of sfn * exp list
  | Egrp of sfn_grp * int * ie_list (** Abelian group *)

and ie_list =
  | IEnil
  | IEcons of exp * int * ie_list

(* -------------------------------------------------------------------------- *)
(** {2 Built-in functions} *)
(* -------------------------------------------------------------------------- *)

let string_of_sfn1 = function
  | Sfn_NOT -> "!"
  | Sfn_item -> "@item"
  | Sfn_sorted -> "@sorted"
  | Sfn_hd -> "@hd"
  | Sfn_tl -> "@tl"
  | Sfn_set_of_list -> "@set_of_list"
  | Sfn_can_return -> "@can_return"

let string_of_sfn2 = function
  | Sfn_list_lt -> "@lt"
  | Sfn_subset -> "@subset"
  | Sfn_set_minus -> "@minus"

let string_of_sfn = function
  | Sfn_list ->  "@list"
  | Sfn_set ->   "@set"
  | Sfn_AND ->   "@and"
  | Sfn_OR  ->   "@or"
  | Sfn_XOR  ->  "@xor"
  | Sfn_undef -> "@undef"

let string_of_sfn_grp = function
  | Sfn_plus ->  "@plus"
  | Sfn_pos ->   "@pos"

(* -------------------------------------------------------------------------- *)
(** {2 Equality and comparison } *)
(* -------------------------------------------------------------------------- *)

let rec equal_exp e1 e2 =
  e1==e2 || begin match e1 with
    | Enum n1 -> (match e2 with Enum n2 -> n1 = n2 | _ -> false)
    | Eident _ -> false
    | Eeq (e1,f1) ->
	(match e2 with Eeq (e2,f2) ->
	   equal_exp e1 e2 && equal_exp f1 f2
	   | _ -> false)
    | Efun1 (s1,e1) ->
	(match e2 with Efun1 (s2,e2) -> s1==s2 && equal_exp e1 e2
	   | _ -> false)
    | Efun2 (s1,e1,f1) ->
	(match e2 with Efun2 (s2,e2,f2) -> 
             s1==s2 && equal_exp e1 e2 && equal_exp f1 f2
	   | _ -> false)
    | Efun (s1,el1) ->
	(match e2 with Efun (s2,el2) -> 
           s1==s2 && equal_exp_list el1 el2
	   | _ -> false)
    | Egrp (s1,n1,nel1) ->
	(match e2 with Egrp (s2,n2,nel2) ->
	   Pervasives.(=) s1 s2 && n1=n2 && equal_ie_list nel1 nel2
	   | _ -> false)
  end

and equal_exp_list el1 el2 = match el1,el2 with
  | [],[] -> true
  | [],_ -> false
  | _,[] -> false
  | e1::el1',e2::el2' -> equal_exp e1 e2 && equal_exp_list el1' el2'

and equal_ie_list el1 el2 = match el1,el2 with
  | IEnil,IEnil -> true
  | IEnil,_ -> false
  | _,IEnil -> false
  | IEcons(e1,i1,el1'),IEcons (e2,i2,el2') ->
      i1==i2 && equal_exp e1 e2 && equal_ie_list el1' el2'

let compare_int (i1: int) (i2: int) =
  Pervasives.compare i1 i2 

let compare_small_int x y =
  Obj.magic x - (Obj.magic y : int)

let rec compare_exp e1 e2 =
  if e1==e2 then 0 else
  let n = compare_small_int (Obj.tag (Obj.repr e1)) (Obj.tag (Obj.repr e2)) in 
  if n <> 0 then n else match e1,e2 with
    | Enum n1, Enum n2 -> compare_int n1 n2
    | Eident (kind1,id1,_), Eident (kind2,id2,_) ->
	let n = compare_small_int kind1 kind2 in if n<>0 then n else
	id2 - id1
    | Eeq (e1,f1), Eeq (e2,f2) ->
	let n = compare_exp e1 e2 in if n<>0 then n else
	compare_exp f1 f2
    | Efun1 (s1,e1), Efun1 (s2,e2) ->
	let n = compare_small_int s1 s2 in if n<>0 then n else
	compare_exp e1 e2
    | Efun2 (s1,e1,f1), Efun2 (s2,e2,f2) ->
	let n = compare_small_int s1 s2 in if n<>0 then n else
	let n = compare_exp e1 e2 in if n<>0 then n else
	compare_exp f1 f2
    | Efun (s1,el1), Efun (s2,el2) ->
	let n = compare_small_int s1 s2 in if n<>0 then n else
	compare_exp_list el1 el2
    | Egrp (s1,n1,nel1), Egrp (s2,n2,nel2) ->
	let n = compare_small_int s1 s2 in if n<>0 then n else
	let n = compare_int n1 n2 in if n<>0 then n else
	compare_ie_list nel1 nel2
    | _ -> assert false

and compare_exp_list el1 el2 = match el1,el2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | e1::el1',e2::el2' ->
      let n = compare_exp e1 e2 in if n<>0 then n else
      compare_exp_list el1' el2'

and compare_ie_list nel1 nel2 = match nel1,nel2 with
  | IEnil,IEnil -> 0
  | IEnil,_ -> -1
  | _,IEnil -> 1
  | IEcons(e1,n1,el1'),IEcons(e2,n2,el2') ->
      let n = compare_exp e1 e2 in if n<>0 then n else
      let n = compare_int n1 n2 in if n<>0 then n else
      compare_ie_list el1' el2'


let rec abs_compare_exp e1 e2 =
  if e1==e2 then 0 else
  let n = compare_small_int (Obj.tag (Obj.repr e1)) (Obj.tag (Obj.repr e2)) in 
  if n <> 0 then n else match e1,e2 with
    | Enum n1, Enum n2 -> compare_int n1 n2
    | Eident (kind1, id1, _), Eident (kind2, id2, _) ->
	let n = compare_small_int kind1 kind2 in if n<>0 then n else
	if kind1==EXIST_RENAMED || kind1==EXIST_ORIG then 0 else
	id2 - id1
    | Eeq (e1,f1), Eeq (e2,f2) ->
	let n = abs_compare_exp e1 e2 in if n<>0 then n else
	abs_compare_exp f1 f2
    | Efun1 (s1,e1), Efun1 (s2,e2) ->
	let n = compare_small_int s1 s2 in if n<>0 then n else
	abs_compare_exp e1 e2
    | Efun2 (s1,e1,f1), Efun2 (s2,e2,f2) ->
	let n = compare_small_int s1 s2 in if n<>0 then n else
	let n = abs_compare_exp e1 e2 in if n<>0 then n else
	abs_compare_exp f1 f2
    | Efun (s1,el1), Efun (s2,el2) ->
	let n = compare_small_int s1 s2 in if n<>0 then n else
	abs_compare_exp_list el1 el2
    | Egrp (s1,n1,nel1), Egrp (s2,n2,nel2) ->
	let n = compare_small_int s1 s2 in if n<>0 then n else
	let n = compare_int n1 n2 in if n<>0 then n else
	abs_compare_ie_list nel1 nel2
    | _ -> assert false

and abs_compare_exp_list el1 el2 = match el1,el2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | e1::el1',e2::el2' ->
      let n = abs_compare_exp e1 e2 in if n<>0 then n else
      abs_compare_exp_list el1' el2'

and abs_compare_ie_list nel1 nel2 = match nel1,nel2 with
  | IEnil,IEnil -> 0
  | IEnil,_ -> -1
  | _,IEnil -> 1
  | IEcons(e1,n1,el1'),IEcons(e2,n2,el2') ->
      let n = abs_compare_exp e1 e2 in if n<>0 then n else
      let n = compare_int n1 n2 in if n<>0 then n else
      abs_compare_ie_list el1' el2'


(* -------------------------------------------------------------------------- *)
(** {2 Identifiers } *)
(* -------------------------------------------------------------------------- *)

module Id = struct

  (** Always of the form [Eident ...] *)
  type t = exp

  let of_exp e =
    assert (match e with Eident _ -> true | _ -> false);
    e
  
  let unique_id_count = ref 0
  let create_ident_ht = Hashtbl.create 251
  
  let get_unique_id () =
    let _ = incr unique_id_count in
    !unique_id_count
  
  let get_id_kind (x: t) = (Obj.obj (Obj.field (Obj.repr x) 0) : id_kind)
  let get_id_uid  (x: t) = (Obj.obj (Obj.field (Obj.repr x) 1) : int)
  let get_id_name (x: t) = (Obj.obj (Obj.field (Obj.repr x) 2) : string)
  
  (* generate fresh identifiers *)
  let gensym_str s =
    assert (String.length s <> 0);
    let count = get_unique_id () in
    Eident (NORMAL_RENAMED, count, s)
  
  let gensym_str_ex s =
    assert (String.length s <> 0);
    let count = get_unique_id () in
    Eident (EXIST_RENAMED, count, s)
  
  let gensym_norm id = gensym_str (get_id_name id)
  let gensym_garb id = gensym_str_ex (get_id_name id)
  let tempid () = gensym_str "temporary"
  
  let existential_name s =
    assert (String.length s <> 0);
    String.length s <> 0 && String.get s 0 = '_'
  
  let un_EX s =
    try String.sub s 1 (String.length s - 1)
    with Not_found -> assert false
  
  let is_ex_kind = function
    | EXIST_ORIG | EXIST_RENAMED -> true
    | NORMAL_ORIG | NORMAL_RENAMED -> false
  
  let create s =
    assert (String.length s <> 0);
    try
       Hashtbl.find create_ident_ht s
    with Not_found ->
      let unique_id = get_unique_id () in
      let res =
        if existential_name s
        then Eident (EXIST_ORIG, unique_id, un_EX s)
        else Eident (NORMAL_ORIG, unique_id, s) in
      Hashtbl.add create_ident_ht s res;
      res
  
  let tid    = create "TID"
  let mytid  = create "myTID"
  let result = create "Result"
  let junk   = create "JUNK"
  
  let string_of_id_internal kind uid name = match kind with
    | EXIST_ORIG     -> "_" ^ name
    | EXIST_RENAMED  -> "_" ^ name ^ "_" ^ string_of_int uid
    | NORMAL_ORIG    -> name
    | NORMAL_RENAMED -> name ^ "_" ^ string_of_int uid
  
  let to_string = function
    | Eident (kind, uid, name) -> string_of_id_internal kind uid name
    | _ -> assert false
 
  let is_existential id = 
    is_ex_kind (get_id_kind id)
		
	let to_unex_string id = 
		if (is_existential id) then un_EX (to_string id)
		else to_string id
  
  let is_no_junk_var i = 
    match (get_id_name i) with
    | "" -> true
    | "split" | "VAL" | "valsplit" -> not (is_existential i)
    | s -> String.get s 0 != '.'

  let compare i1 i2 =
    let n = compare_small_int (get_id_kind i1) (get_id_kind i2) in
    if n<>0 then n else
    get_id_uid i2 - get_id_uid i1
end

module IdSet = Set.Make(Id)
module IdMap = Map.Make(Id)

(* -------------------------------------------------------------------------- *)
(** {2 Expression misc operations} *)
(* -------------------------------------------------------------------------- *)

let rec ie_fold f l acc = match l with
  | IEnil -> acc
  | IEcons(e,n,l) -> ie_fold f l (f e n acc)

let rec ie_fold_exp f l acc = match l with
  | IEnil -> acc
  | IEcons(e,_n,l) -> ie_fold_exp f l (f e acc)

let rec ie_forall_exp f l = match l with
  | IEnil -> true
  | IEcons(e,_n,l) -> f e && ie_forall_exp f l 

let rec exp_fold f e acc = match e with
  | Enum _ 
  | Eident _ -> f e acc
  | Eeq (e1,e2) -> exp_fold f e2 (exp_fold f e1 (f e acc))
  | Efun1(_,e1) -> exp_fold f e1 (f e acc)
  | Efun2(_,e1,e2) -> exp_fold f e2 (exp_fold f e1 (f e acc))
  | Efun(_,el) -> List.fold (exp_fold f) el (f e acc)
  | Egrp(_,_,nel) -> ie_fold_exp (exp_fold f) nel (f e acc)

let rec mem_exp y l = (* List.exists (equal_exp y) l *)
  match l with
  | [] -> false
  | x :: l -> equal_exp y x || mem_exp y l

let remdup_exp l = match l with | [] | [_] -> l | _ ->
  let l2 = List.stable_sort compare_exp l in
  let rec remf = function
    | x::(y::_ as xs) -> if equal_exp x y then remf xs else x::(remf xs)
    | xs -> xs
  in remf l2

let remdup_and_zero l = match l with 
  | [] -> l
  | [Enum 0] -> []
  | [_] -> l
  | _ ->
      let l2 = List.stable_sort compare_exp l in
      let rec remf = function
	| Enum 0 :: xs -> remf xs
	| x::(y::_ as xs) -> if equal_exp x y then remf xs else x::(remf xs)
	| xs -> xs in
      remf l2

(** return [true] if expression is an existentially quantified identifier *)
let existential_id = function
  | Eident (kind, _, _) -> Id.is_ex_kind kind
  | _ -> false

let rec ie_negate nel = match nel with
  | IEnil -> IEnil 
  | IEcons (e,n,nel) -> IEcons (e,-n,ie_negate nel)

let rec ie_mult_app m acc nel = match nel with
  | IEnil -> acc 
  | IEcons (e,n,nel) -> ie_mult_app m ((e,m * n)::acc) nel


(* -------------------------------------------------------------------------- *)
(** {2 Expression constants} *)
(* -------------------------------------------------------------------------- *)

module E = struct

let zero = Enum 0
let one = Enum 1
let tid = Id.tid
let empty_list = Efun (Sfn_list, [])
let empty_set = Efun (Sfn_set, [])
let undef = Efun (Sfn_undef, [])


(* -------------------------------------------------------------------------- *)
(** {2 Expression constructors} *)
(* -------------------------------------------------------------------------- *)
(** NB: The constructors perform elaborate simplifications. *)

(** Constructor for [Enum n]. *)
let num n = match n with
  | 0 -> zero
  | 1 -> one
  | n -> Enum n

(** Constructor for identifiers (identity function). *)
let id (i: Id.t) = (i: exp)

(** {3 Abelian groups} *)
(* -------------------------------------------------------------------------- *)

(** Constructor for [Egrp(Sfn_plus,n,nel)]. *)
let grp_plus n nel = match n,nel with
   n, IEnil -> num n
 | 0, IEcons(e,1,IEnil) -> e
 | n, nel -> 
  let rec go n res = function (* combine nested functions *)
    | IEnil -> (n, res)
    | IEcons (Enum n',m,nel) -> go (n + (m * n')) res nel
    | IEcons (Egrp(Sfn_plus,n',nel'),m,nel) -> 
	go (n + m * n') (ie_mult_app m res nel') nel
    | IEcons (e,n',nel) -> go n ((e,n')::res) nel in
  let rec go2 res = function (* put same terms together *)
    | (e,0)::nel -> go2 res nel
    | (e,n)::(e',m)::nel when equal_exp e e' ->
        if n+m=0 then go2 res nel else go2 res ((e,n+m)::nel)
    | (e,n)::nel -> go2 (IEcons(e,n,res)) nel
    | [] -> res in
  let (n,nel) = go n [] nel in
  let nel = List.sort (fun (x,_) (y,_) -> -compare_exp x y) nel in
  let nel = go2 IEnil nel in
  match n,nel with 
    | n,IEnil -> num n
    | 0,IEcons(e,1,IEnil) -> e 
    | _ -> Egrp(Sfn_plus,n,nel)

(** Constructor for [Egrp(Sfn_pos,n,nel)]. *)
let grp_pos n nel = match n,nel with
   n, IEnil -> if n >= 0 then one else zero
 | n, nel -> 
  let rec go n res = function (* combine nested functions *)
    | IEnil -> (n, res)
    | IEcons (Enum n',m,nel) -> go (n + (m * n')) res nel
    | IEcons (Egrp(Sfn_plus,n',nel'),m,nel) -> 
	go (n + m * n') (ie_mult_app m res nel') nel
    | IEcons (e,n',nel) -> go n ((e,n')::res) nel in
  let rec go2 res = function (* put same terms together *)
    | (e,0)::nel -> go2 res nel
    | (e,n)::(e',m)::nel when equal_exp e e' ->
        if n+m=0 then go2 res nel else go2 res ((e,n+m)::nel)
    | (e,n)::nel -> go2 (IEcons(e,n,res)) nel
    | [] -> res in
  let (n,nel) = go n [] nel in
  let nel = List.sort (fun (x,_) (y,_) -> -compare_exp x y) nel in
  let nel = go2 IEnil nel in
  match n,nel with 
    | n,IEnil -> if n >= 0 then one else zero
    | _ -> Egrp(Sfn_pos,n,nel)

(** Constructor for [Egrp(i,n,nel)]. *)
let grp i n nel = match i with
  | Sfn_plus -> grp_plus n nel
  | Sfn_pos -> grp_pos n nel

let add e1 e2 = grp_plus 0 (IEcons(e1,1,IEcons(e2,1,IEnil)))
let sub e1 e2 = grp_plus 0 (IEcons(e1,1,IEcons(e2,-1,IEnil)))


(** {3 Boolean operations} *)
(* -------------------------------------------------------------------------- *)

let band el =
  let rec concat_AND e res = match e with
    | Enum n -> if n = 0 then [zero] else res
    | Efun(Sfn_AND,el') -> List.fold concat_AND el' res
    | e -> e::res in 
  match List.reduce concat_AND el with
  | [] -> one
  | [e] -> e
  | el -> 
      if List.exists (fun x -> x==zero) el then zero 
      else Efun(Sfn_AND, remdup_exp el)

let lifted_AND e efn =
  match e with 
  | Enum 0 -> e
  | Enum _ -> efn ()
  | _ -> band [e; efn ()]

let bor el =
  let rec concat_OR e res = match e with
    | Enum n -> if n = 0 then res else [one]
    | Efun(Sfn_OR,el') -> List.fold concat_OR el' res
    | e -> e::res in 
  match List.reduce concat_OR el with
  | [] -> zero
  | [e] -> e
  | el -> 
      if List.exists (fun x -> x==one) el then one
      else Efun(Sfn_OR, remdup_exp el)

let rec bnot e = match e with
  | Enum n -> if n = 0 then one else zero
  | Efun1 (Sfn_NOT,x) -> x
  | Efun (Sfn_AND,x) -> bor (List.map bnot x)
  | Efun (Sfn_OR,x) -> band (List.map bnot x)
(* *)  | Eeq (Enum 0, 
	    (( Efun2 (Sfn_subset, _, _) 
	     | Efun (Sfn_AND, _)
	     | Efun (Sfn_OR, _)
	     | Efun1 (Sfn_NOT, _)
	     ) as x)) -> x
(* *)
  | Egrp (Sfn_pos,n,nel) -> Egrp (Sfn_pos,-n-1,ie_negate nel)
  | _ -> Efun1 (Sfn_NOT, e)

(* bitwise *)
let xor el =
  let rec concat_XOR n acc l = match l with
    | [] -> (n,acc)
    | Enum n' :: l -> concat_XOR (n lxor n') acc l 
    | Efun(Sfn_XOR,Enum n' :: el') :: l -> 
        concat_XOR (n lxor n') (List.rev_append el' acc) l
    | Efun(Sfn_XOR,el') :: l ->
        concat_XOR n (List.rev_append el' acc) l
    | e :: l -> concat_XOR n (e::acc) l in 
  let rec remove_XOR l = match l with
    | e :: e' :: l when equal_exp e e' -> remove_XOR l
    | e :: l -> e :: remove_XOR l
    | [] -> [] in
  let (n,el) = concat_XOR 0 [] el in
  let el = List.sort compare_exp el in
  let el = remove_XOR el in
  match n, el with
    | n, []  -> num n
    | 0, [e] -> e
    | 0, el  -> Efun(Sfn_XOR, el)
    | n, el  -> Efun(Sfn_XOR, num n :: el)


(** {3 Sequences and multisets} *)
(* -------------------------------------------------------------------------- *)

let item e = Efun1 (Sfn_item, e)

let list el =
  let rec concat e res = match e with
    | Efun(Sfn_list,el') -> List.fold concat el' res
    | e -> e::res in 
  match List.reduce concat el with
    | [] -> empty_list
    | [e] -> e
    | el -> Efun(Sfn_list, List.rev el)

let set el =
  let rec concat e res = match e with
    | Efun(Sfn_set,el') -> List.fold concat el' res
    | e -> e::res in 
  match List.reduce concat el with
    | [] -> empty_set
    | [e] -> e
    | el -> Efun(Sfn_set, List.sort compare_exp el)

(** {3 Equality} *)
(* -------------------------------------------------------------------------- *)

let eq_simp e1 e2 =
  let n = compare_exp e1 e2 in
  if n < 0 then Eeq(e1,e2)
  else if n = 0 then one
  else Eeq(e2,e1)

(** Constructor for equalities *)
let rec eq e1 e2 = 
  if e1==e2 then one else
  match (e1,e2) with
    | Enum n, Enum m     -> if n=m then one else zero
    | Efun1(Sfn_item,e1), Efun1(Sfn_item,e2) -> eq e1 e2
    | Efun1(Sfn_item, _), Efun(Sfn_list,el2) -> list_eq [e1] el2
    | Efun1(Sfn_item, _), Efun(Sfn_set,el2)  -> set_eq [e1] el2
    | Efun(Sfn_list,el1), Efun1(Sfn_item, _) -> list_eq el1 [e2]
    | Efun(Sfn_list,el1), Efun(Sfn_list,el2) -> list_eq el1 el2
    | Efun(Sfn_set, el1), Efun1(Sfn_item, _) -> set_eq el1 [e2]
    | Efun(Sfn_set, el1), Efun(Sfn_set, el2) -> set_eq el1 el2
    | Egrp _, _ 
    | _, Egrp _ -> grp_eq e1 e2
    | _ -> eq_simp e1 e2

and grp_eq e1 e2 =
  match sub e1 e2 with
    | Enum 0 -> one
    | Enum _ -> zero
    | (Eident _ | Efun _) as e -> eq_simp zero e
    | Egrp(Sfn_plus,n,IEcons((Eident _ as e),1,nel)) -> 
	eq_simp e (grp_plus (-n) (ie_negate nel))
    | Egrp(Sfn_plus,n,(IEcons((Eident _ as e),-1,nel))) -> 
	eq_simp e (grp_plus n nel)
    | _ -> 
  match xor [e1;e2] with
    | Enum 0 -> one
    | Enum n -> zero
    | Efun(Sfn_XOR,e1::el) -> eq_simp e1 (xor el)
    | e -> eq_simp zero e

and list_eq el1 el2 =
  let has_item =
    List.exists (function Efun1(Sfn_item,_) -> true | _ -> false) in
  let rec i_eq_l x el2 =
    match el2 with
    | [] -> one
    | Efun1(Sfn_item,e2)::el2 ->
	lifted_AND (eq x e2) (fun () -> list_eq [] el2)
    | e2::el2 -> 
	lifted_AND (eq e2 empty_list) (fun () -> i_eq_l x el2) in
  match (el1,el2) with
  (* One or both lists are empty *)
  | [], [] -> one
  | [], el2 ->
      if has_item el2 then zero
      else band (List.map (eq_simp empty_list) el2)
  | el1, [] -> 
      if has_item el1 then zero
      else band (List.map (eq_simp empty_list) el1)
  (* One or both lists start with @item *)
  | (Efun1(Sfn_item,e1)::el1, Efun1(Sfn_item,e2)::el2) ->
      lifted_AND (eq e1 e2) (fun () -> list_eq el1 el2)
  | ([Efun1(Sfn_item,e1)], el2) when has_item el2 -> i_eq_l e1 el2
  | (el1, [Efun1(Sfn_item,e2)]) when has_item el1 -> i_eq_l e2 el1
  (* Simple cases *)
  | ([e1], [e2]) -> eq e1 e2
  | (e1::el1, e2::el2) when equal_exp e1 e2 -> list_eq el1 el2
  | (el1, el2) ->
      begin match (List.rev el1, List.rev el2) with
      | (e1::el1, e2::el2) when equal_exp e1 e2 ->
          list_eq (List.rev el1) (List.rev el2)
      | (Efun1(Sfn_item,e1)::el1, Efun1(Sfn_item,e2)::el2) ->
	  lifted_AND (eq e1 e2)
            (fun () -> list_eq (List.rev el1) (List.rev el2))
      | _ -> 
	  eq_simp (list el1) (list el2)
      end

and set_eq el1 el2 =
  let has_item =
    List.exists (function Efun1(Sfn_item,_) -> true | _ -> false) in
  let rec go el1a el2a el1 el2 =
    match (el1, el2) with
      | [], _ -> (el1a, List.rev_append el2a el2)
      | _, [] -> (List.rev_append el1a el1, el2a)
      | e1::el1b, e2::el2b ->
	  let n = compare_exp e1 e2 in
	  if n = 0 then go el1a el2a el1b el2b
	  else if n < 0 then go (e1::el1a) el2a el1b el2
	  else go el1a (e2::el2a) el1 el2b in
  let (el1,el2) = go [] [] el1 el2 in
  match (el1,el2) with
  | ([],[]) -> one
  | ([], xl) ->
      if has_item xl then zero
      else band (List.map (eq_simp empty_set) xl)
  | (xl, []) -> 
      if has_item xl then zero
      else band (List.map (eq_simp empty_set) xl)
  | ([e1], [e2]) -> eq e1 e2
  | (el1, el2) -> eq_simp (set el1) (set el2)

(** Constructor for [e1 != e2]. *)
let neq e1 e2 = bnot (eq e1 e2)


(** {3 Operations on sequences and multisets} *)
(* -------------------------------------------------------------------------- *)

let hd = function 
  | Efun1 (Sfn_item, e) -> e
  | Efun (Sfn_list, Efun1 (Sfn_item, e)::_) -> e
  | e -> Efun1 (Sfn_hd, e)

let tl = function
  | Efun1 (Sfn_item, e) -> empty_list
  | Efun (Sfn_list, Efun1 (Sfn_item,_)::l) -> list l
  | Efun (Sfn_list, []) -> empty_list
  | e -> Efun1 (Sfn_tl, e)

let set_of_list x = match x with
  | Efun1 (Sfn_item, _)  -> x
  | Efun (Sfn_list, el) ->
      let f y = match y with
				| Efun1 (Sfn_item,_) -> y
				| _ -> Efun1 (Sfn_set_of_list, y) 
			in
      	set (List.map f el)
  | _ -> Efun1 (Sfn_set_of_list, x)

let list_lt e1 e2 =
  let go_item e1 e2 r = 
    if equal_exp e1 e2 then 
      bor [eq e1 empty_list; eq e2 empty_list] :: r
    else
      match e1, e2 with
				| (Efun1 (Sfn_item, Enum x), Efun1 (Sfn_item, Enum y)) ->
	    			if x < y then r else [zero]
				| _ -> Efun2 (Sfn_list_lt, e1, e2)::r
  in
  		let l1 = match e1 with Efun(Sfn_list, xl) -> xl | x -> [x] in
  		let l2 = match e2 with Efun(Sfn_list, xl) -> xl | x -> [x] in
  		band (List.fold (fun x -> List.fold (go_item x) l2) l1 [])


let ltn e1 e2 =
(*  grp_pos (-1) (IEcons (e1, -1, IEcons (e2, 1, IEnil))) *)
  list_lt (Efun1 (Sfn_item, e1)) (Efun1 (Sfn_item, e2)) 

let leq e1 e2 = bnot (ltn e2 e1)

let rec sorted e = match e with
  | Efun1 (Sfn_item, x) -> one
  | Efun (Sfn_list, x) ->
      begin match x with
	| [] -> one
	| x::xl ->
	    let x = list [x] in
	    let y = list xl in
	    band [sorted x; sorted y; list_lt x y]
      end
  | _ -> Efun1 (Sfn_sorted, e)

let set_minus x y =
  let x = match x with Efun (Sfn_set,el) -> el | _ -> [x] in
  let y = match y with Efun (Sfn_set,el) -> el | _ -> [y] in
  let rec go_minus acc_x acc_y xl yl = match xl, yl with
    | x::xl1, y::yl1 ->
	let n = compare_exp x y in
	if n < 0 then go_minus (x::acc_x) acc_y xl1 yl
	else if n = 0 then go_minus acc_x acc_y xl1 yl1
	else go_minus acc_x (y::acc_y) xl yl1
    | [], _::_ -> Efun2 (Sfn_set_minus, set (List.rev acc_x),
                           set (List.rev_append acc_y yl))
    | _, [] ->
	begin match acc_y with
	  | [] -> set (List.rev_append acc_x xl)
	  |  _ -> Efun2 (Sfn_set_minus, set (List.rev_append acc_x xl),
                           set (List.rev acc_y))
	end in
  go_minus [] [] x y

(* TODO -- unsound for multisets *)
let subset x y =
  let x = match x with Efun (Sfn_set,el) -> el | _ -> [x] in
  let y = match y with Efun (Sfn_set,el) -> el | _ -> [y] in
  let x = List.filter (fun e -> not (List.exists (equal_exp e) y)) x in
  begin match (x, y) with
    | ([], _) -> one
    | (_::_, []) -> zero
    | ([Efun1 (Sfn_item, x)], [Efun1 (Sfn_item, y)]) -> eq x y
    | ([Efun1 (Sfn_item, x) as v], _) ->
				bor (List.map (function 
						   | Efun1 (Sfn_item, y) -> eq x y
						   | y -> Efun2 (Sfn_subset, v, y)) y)
    | _ -> Efun2 (Sfn_subset, set x, set y)
  end


(** {3 Summary} *)
(* -------------------------------------------------------------------------- *)

(** Constructor for [Efun(s,el)]. *)
let funn s el = match s with
  | Sfn_list -> list el
  | Sfn_set -> set el
  | Sfn_AND -> band el
  | Sfn_OR -> bor el
  | Sfn_XOR -> xor el
  | Sfn_undef -> undef

let fun1 s e = match s with
  | Sfn_NOT -> bnot e
  | Sfn_hd -> hd e
  | Sfn_tl -> tl e
  | Sfn_set_of_list -> set_of_list e
  | Sfn_sorted -> sorted e
  | Sfn_item
  | Sfn_can_return -> Efun1 (s, e)

let fun2 s e1 e2 = match s with
  | Sfn_list_lt -> list_lt e1 e2
  | Sfn_subset -> subset e1 e2
  | Sfn_set_minus -> set_minus e1 e2


(* -------------------------------------------------------------------------- *)
(** {2 Free variables} *)
(* -------------------------------------------------------------------------- *)

  let rec fv e acc = match e with
    | Enum _ -> acc
    | Eident _ -> IdSet.add e acc
    | Eeq(e1,e2) -> fv e1 (fv e2 acc)
    | Efun1(_,e1) -> fv e1 acc
    | Efun2(_,e1,e2) -> fv e1 (fv e2 acc)
    | Efun(_,el) -> List.fold fv el acc
    | Egrp(_,_,nel) -> ie_fold_exp fv nel acc
  
  let rec exfv e acc = match e with
    | Enum _ -> acc
    | Eident (kind,_,_) -> if Id.is_ex_kind kind then IdSet.add e acc else acc
    | Eeq(e1,e2) -> exfv e1 (exfv e2 acc)
    | Efun1(_,e1) -> exfv e1 acc
    | Efun2(_,e1,e2) -> exfv e1 (exfv e2 acc)
    | Efun(_,el) -> List.fold exfv el acc
    | Egrp(_,_,nel) -> ie_fold_exp exfv nel acc
  
  let rec fhd e acc = match e with
    | Enum _ | Eident _ -> acc
    | Eeq (e1,e2) -> fhd e1 (fhd e2 acc)
    | Efun1 (Sfn_hd, (Eident _ as e')) -> IdSet.add e' acc
    | Efun1(_,e1) -> fhd e1 acc
    | Efun2(_,e1,e2) -> fhd e1 (fhd e2 acc)
    | Efun (_,el) -> List.fold fhd el acc
    | Egrp(_,_,nel) -> ie_fold_exp fhd nel acc
  
  let rec forall_fv (f: Id.t -> bool) e = match e with
    | Enum _ -> true
    | Eident _ -> f e 
    | Eeq(e1,e2) -> forall_fv f e1 && forall_fv f e2
    | Efun1(_,e1) -> forall_fv f e1
    | Efun2(_,e1,e2) -> forall_fv f e1 && forall_fv f e2
    | Efun(_,el) -> List.for_all (forall_fv f) el
    | Egrp(_,_,nel) -> ie_forall_exp (forall_fv f) nel

  let gensym_str s = (Id.gensym_str s : exp)
  let gensym_str_ex s = (Id.gensym_str_ex s : exp)
 end

(* -------------------------------------------------------------------------- *)
(** {2 Substitutions} *)
(* -------------------------------------------------------------------------- *)

type subst = exp -> exp 

let rec map_sub f l = match l with
  | [] -> l
  | x::xl ->
      let y = f x in
      let yl = map_sub f xl in
      if xl==yl && x==y then l else y::yl
			
(** FIXME: Do not implement Egrp subsitution *)
let rec map_id_exp_sub fsub e = match e with
  | Enum _ 
  | Eident _ -> (match fsub e with Some e -> e | None -> e)
  | Eeq (e1,e2) -> Eeq (map_id_exp_sub fsub e1, map_id_exp_sub fsub e2)
  | Efun1(x,e1) -> Efun1 (x, map_id_exp_sub fsub e1)
  | Efun2(x,e1,e2) -> Efun2 (x, map_id_exp_sub fsub e1, map_id_exp_sub fsub e2)
  | Efun(x,el) -> Efun (x, List.map (map_id_exp_sub fsub) el)
  | Egrp(x,y,nel) -> e

let rec map_n_sub (f: subst) l = match l with
  | IEnil -> l
  | IEcons (x,n,xl) ->
      let y = f x in
      let yl = map_n_sub f xl in
      if xl==yl && x==y then l else IEcons(y,n,yl)

let mk_fun_subst subf =
  let rec ff_e e = 
    let e' = subf e in 
    if e'!=e then e' 
		else match e with
      | Enum _ | Eident _ -> e
      | Eeq (e1,e2) ->
	  		let e1' = ff_e e1 in
	  		let e2' = ff_e e2 in
	  		if e1'==e1 && e2'==e2 then e else E.eq e1' e2'
      | Efun1 (i,e1) ->
	  		let e1' = ff_e e1 in
	  		if e1'==e1 then e else E.fun1 i e1'
      | Efun2 (i,e1,e2) ->
	  		let e1' = ff_e e1 in
	  		let e2' = ff_e e2 in
	  		if e1'==e1 && e2'==e2 then e else E.fun2 i e1' e2'
      | Efun (i,el) ->
	  		let el' = map_sub ff_e el in
	  		if el' == el then e else E.funn i el'
      | Egrp(op,n,nel) ->
	  		let nel' = map_n_sub ff_e nel in
	  		if nel' == nel then e else E.grp op n nel'
  in ff_e

let mk_single_subst i' e' =
  let rec sf_e e = match e with
    | Enum _ -> e
    | Eident _ -> if e == i' then e' else e
    | Eeq (e1,e2) ->
			let e1' = sf_e e1 in
			let e2' = sf_e e2 in
			if e1'==e1 && e2'==e2 then e else E.eq e1' e2'
    | Efun1 (i,e1) ->
			let e1' = sf_e e1 in
			if e1'==e1 then e else E.fun1 i e1'
    | Efun2 (i,e1,e2) ->
			let e1' = sf_e e1 in
			let e2' = sf_e e2 in
			if e1'==e1 && e2'==e2 then e else E.fun2 i e1' e2'
    | Efun (i,el) ->
			let el' = map_sub sf_e el in
			if el' == el then e else E.funn i el'
    | Egrp(op,n,nel) ->
			let nel' = map_n_sub sf_e nel in
			if nel' == nel then e else E.grp op n nel' 
	in sf_e

let mk_id_subst (f : Id.t -> exp) =
  let rec f_e e = match e with
    | Enum _ -> e
    | Eident _ -> f e 
    | Eeq (e1,e2) ->
				let e1' = f_e e1 in
				let e2' = f_e e2 in
				if e1'==e1 && e2'==e2 then e else E.eq e1' e2'
    | Efun1 (i,e1) ->
				let e1' = f_e e1 in
				if e1'==e1 then e else E.fun1 i e1'
    | Efun2 (i,e1,e2) ->
				let e1' = f_e e1 in
				let e2' = f_e e2 in
				if e1'==e1 && e2'==e2 then e else E.fun2 i e1' e2'
    | Efun (i,el) ->
				let el' = map_sub f_e el in
				if el' == el then e else E.funn i el'
    | Egrp(op,n,nel) ->
				let nel' = map_n_sub f_e nel in
				if nel' == nel then e else E.grp op n nel'
  in f_e

let rec opt_findq l x = match l with
  | PCons (k, v, ln) ->
      if k == x then v else opt_findq ln x
  | PNil -> E.id x

let rec mk_idl_subst l e = match e with
  | Enum _ -> e
  | Eident _ -> opt_findq l e 
  | Eeq (e1,e2) ->
      let e1' = mk_idl_subst l e1 in
      let e2' = mk_idl_subst l e2 in
      if e1'==e1 && e2'==e2 then e else E.eq e1' e2'
  | Efun1 (i,e1) ->
      let e1' = mk_idl_subst l e1 in
      if e1'==e1 then e else E.fun1 i e1'
  | Efun2 (i,e1,e2) ->
      let e1' = mk_idl_subst l e1 in
      let e2' = mk_idl_subst l e2 in
      if e1'==e1 && e2'==e2 then e else E.fun2 i e1' e2'
  | Efun (i,el) ->
      let el' = map_sub (fun x -> mk_idl_subst l x)  el in
      if el' == el then e else E.funn i el'
  | Egrp(op,n,nel) ->
      let nel' = map_n_sub (fun x -> mk_idl_subst l x) nel in
      if nel' == nel then e else E.grp op n nel'

let rec mk_subst (l: (Id.t, exp) plist) = match l with 
  | PNil -> identity
  | PCons(i', e', PNil) -> mk_single_subst i' e'
  | _ -> mk_idl_subst l

let mk_gensym_garb_subst i =
  mk_single_subst i (Id.gensym_garb i)

let mk_gensym_garb_subst_idset l =
  let l' = IdSet.fold (fun i r -> PCons(i, Id.gensym_garb i, r)) l PNil in
  mk_subst l'

let mk_gensym_garb_subst_idset2 l =
  let (l1, l2) = 
    IdSet.fold 
      (fun i (r1,r2) ->
	 let j = Id.gensym_garb i in
	 (PCons(i, j, r1), PCons(j,i,r2)))
      l (PNil, PNil) in
  (mk_subst l1, mk_subst l2)

(** Replace existentials with gensym'd normal vars. *)
let existentials_rename_tonormal_sub l =
  let (l1, l2) = 
    IdSet.fold 
      (fun i (r1,r2) ->
	 let j = Id.gensym_norm i in
	 (PCons(i, j, r1), PCons(j,i,r2)))
      l (PNil, PNil) in
  (mk_subst l1, mk_subst l2)

(** Replace existentials with gensym'd existential vars. *)
let existentials_rename_sub l =
  mk_subst (IdSet.fold (fun x r -> PCons(x, Id.gensym_garb x, r)) l PNil)

let map_idset f_e ss =
  IdSet.fold (fun i s -> IdSet.add (f_e i) s) ss IdSet.empty

let rec exp_no_s (s : string) e = match e with
  | Enum _ -> true
  | Eident (_,_,s') -> s' != s
  | Eeq (e1,e2) -> exp_no_s s e1 && exp_no_s s e2
  | Efun1(_,e1) -> exp_no_s s e1
  | Efun2(_,e1,e2) -> exp_no_s s e1 && exp_no_s s e2
  | Efun(_,el) -> List.for_all (exp_no_s s) el 
  | Egrp(_,_,nel) -> ie_fold_exp (fun e r -> r && exp_no_s s e) nel true

(* -------------------------------------------------------------------------- *)
(** {2 Disjoint sets} *)
(* -------------------------------------------------------------------------- *)

module Dset = struct 
  type t = exp list
    (** Invariant: list is sorted and does not contain [E.zero]. *)
  
  let compare = compare_exp_list
  let abs_compare = abs_compare_exp_list
  
  let from_list = remdup_and_zero
  
  let mem_component_exp (t,y) l =
    List.exists (fun (s,x) -> s==t && equal_exp x y) l
  
  let emp = []
  let add e s = if e == E.zero then s else remdup_exp (e::s)
  let mem e s = (e == E.zero || mem_exp e s)
  let remove e s = List.filter (fun x -> not (equal_exp e x)) s
  let to_list s = s
  
  let rec inter s1 s2 = (* List.filter (fun x -> mem x s2) s1 *)
    match s1, s2 with
    | [], _ -> []
    | _::_, [] -> []
    | e1::s1', e2::s2' ->
      let n = compare_exp e1 e2 in
      if n > 0 then inter s1 s2'
      else if n = 0 then e1 :: inter s1' s2'
      else inter s1' s2
  
  let rec subset s1 s2 = (* List.for_all (fun x -> mem x s2) s1 *) 
    match s1, s2 with
    | [], _ -> true
    | _::_, [] -> false
    | e1::s1', e2::s2' ->
      let n = compare_exp e1 e2 in
      if n > 0 then subset s1 s2'
      else (n = 0 && subset s1' s2')
  
  let rec union s1 s2 = (* remdup_exp (s1 @ s2) *)
    match s1, s2 with
    | [], _ -> s2
    | _::_, [] -> s1
    | e1::s1', e2::s2' ->
      let n = compare_exp e1 e2 in
      if n > 0 then e2 :: union s1 s2'
      else if n = 0 then e1 :: union s1' s2'
      else e1 :: union s1' s2
  
  let partition f s = List.partition f s 
  let filter f s = List.filter f s
  let fold = List.fold
  
  let map f_e ds =
    let ds' = map_sub f_e ds in
    if ds' == ds then ds else remdup_and_zero ds'
  
  let no_s s = List.for_all (exp_no_s s)
end

(* -------------------------------------------------------------------------- *)
(** {2 Fields} *)
(* -------------------------------------------------------------------------- *)

module Fld = struct

  type t = (component, exp) plist
  
  let rec compare x y = 
    if x == y then 0 else match x with
      | PNil -> -1
      | PCons (s1, e1, l1) ->
          begin match y with 
            | PNil -> 1
            | PCons (s2, e2, l2) ->
                let n = compare_component s1 s2 in if n<>0 then n else
                let n = compare_exp e1 e2 in if n<>0 then n else
                compare l1 l2
          end
  
  let rec abs_compare x y =
    if x == y then 0 else match x with
      | PNil -> -1
      | PCons (s1, e1, l1) ->
          begin match y with 
            | PNil -> 1
            | PCons (s2, e2, l2) ->
                let n = compare_component s1 s2 in if n<>0 then n else
                let n = abs_compare_exp e1 e2 in if n<>0 then n else
                abs_compare l1 l2
          end
  
  let emp = PNil
  let one t e = PCons (t,e, PNil)
  let two t1 e1 t2 e2 = 
    if compare_component t1 t2 < 0 then PCons (t1, e1, PCons (t2, e2, PNil))
    else PCons (t2, e2, PCons (t1, e1, PNil))
  
  let from_list cel =
    let compare_component_exp ((s1:component),e1) (s2,e2) =
      let n = compare_component s1 s2 in if n<>0 then n else
      compare_exp e1 e2 in
    let cel = List.sort compare_component_exp cel in
    List.fold_right (fun (x,y) r -> PCons(x,y,r)) cel PNil
  
  let inter fld1 fld2 =
    PList.filter
      (fun c e -> PList.exists (fun c' e' -> c == c' && equal_exp e e') fld1)
      fld2
  
  let union = PList.merge compare_component
  let hasfld = PList.mem_assq
  let get = PList.assq
  let try_get = PList.try_assq
  let mem t e fld = PList.exists (fun t' e' -> t == t' && equal_exp e e') fld
  let remove = PList.remove_assq
  
  let containing e0 fld =
    match
      PList.get_first (fun c x -> if equal_exp x e0 then Some c else None) fld
    with
      | Some c -> c
      | None -> assert false
  
  let exists = PList.exists
  let filter = PList.filter
  let fold = PList.fold
  let fold_val = PList.fold_val
  let iter_val = PList.iter_val
  
  let rec set t e fld = match fld with
    | PNil -> PCons (t,e, PNil)
    | PCons(t',_,_) when compare_component t t' < 0 -> PCons(t, e, fld)
    | PCons(t',_,xl) when t == t' -> PCons (t, e, xl)
    | PCons(t',e',xl) -> PCons (t', e', set t e xl)
  
  let get_extend t fld = 
    try (get t fld, fld)
    with Not_found ->
      let e = Id.gensym_str_ex "VAL" in
      (e, set t e fld)
  
  (** Return a conjuction of equalities for each component
     that is defined in both fields1 and fields2 *)
  let components_equal fld1 fld2 = 
    let rec go fld el fld1 fld2 = match fld1, fld2 with
      | PNil, _ -> (E.band el, PList.rev_append fld fld2)
      | _, PNil -> (E.band el, PList.rev_append fld fld1)
      | PCons (c1, e1, fld1'), PCons (c2, e2, fld2') ->
        let n = compare_component c1 c2 in
        if n < 0 then go (PCons (c1, e1, fld)) el fld1' fld2
        else if n = 0 then 
          go (PCons (c1, e1, fld)) (E.eq e1 e2 :: el) fld1' fld2'
        else
          go (PCons (c2, e2, fld)) el fld1 fld2'
    in
    go PNil [] fld1 fld2
  
  (** Return a conjunction of equalities implying that 
      fields1 is subset of fields2 *)
  let subset fields1 fields2 =
    E.band 
      (PList.fold
         (fun c e2 eql ->
          match try_get c fields1 with 
            | None -> 
                let split_id = Id.gensym_str (string_of_component c) in
                E.eq split_id e2 :: eql
            | Some e1 -> E.eq e1 e2 :: eql)
         fields2 [])
  
  let no_s  s = PList.for_all (fun _ e -> exp_no_s s e)
  
  let rec map (f: subst) l = match l with
    | PCons (n, x, xl) ->
        let y = f x in
        let yl = map f xl in
        if xl == yl && x == y then l else PCons (n, y, yl)
    | PNil -> l

end

(* -------------------------------------------------------------------------- *)
(** {2 Pretty printing} *)
(* -------------------------------------------------------------------------- *)

let rec pp_seq pp s f = function
  | [] -> ()
  | [x] -> pp f x
  | x::l -> pp f x; Format.pp_print_string f s; pp_seq pp s f l

let rec pp_exp f = function
  | Enum n ->
      Format.pp_print_int f n
  | Eident (kind, uid, name) -> 
      Format.pp_print_string f (Id.string_of_id_internal kind uid name)
  | Eeq (e1,e2) ->
      pp_exp f e1; 
      Format.pp_print_string f "==";
      pp_exp f e2
  | Efun1 (Sfn_NOT, Eeq(e1,e2)) ->
      pp_exp f e1; 
      Format.pp_print_string f "!=";
      pp_exp f e2
  | Efun1 (i, e1) ->
      Format.pp_print_string f (string_of_sfn1 i);
      Format.pp_print_char f '(';
      pp_exp f e1; 
      Format.pp_print_char f ')'
  | Efun2 (i, e1, e2) ->
      Format.pp_print_string f (string_of_sfn2 i);
      Format.pp_print_char f '(';
      pp_exp f e1; 
      Format.pp_print_char f ',';
      pp_exp f e2; 
      Format.pp_print_char f ')'
  | Efun (i, el) -> 
      Format.pp_print_string f (string_of_sfn i);
      Format.pp_print_char f '(';
      pp_seq pp_exp "," f el;
      Format.pp_print_char f ')'
  | Egrp(i,0,nel) ->
      Format.pp_print_string f (string_of_sfn_grp i);
      Format.pp_print_char f '(';
      pp_ie_list false f nel;
      Format.pp_print_char f ')'
  | Egrp(i,n,nel) ->
      Format.pp_print_string f (string_of_sfn_grp i);
      Format.pp_print_char f '(';
      Format.pp_print_int f n;
      pp_ie_list true f nel;
      Format.pp_print_char f ')'

and pp_ie_list not_first f nel = match nel with
  | IEnil -> ()
  | IEcons (e,n,nel) ->
    (if not_first then Format.pp_print_string f ",");
    (if n = 1 then pp_exp f e 
    else if n = -1 then Format.fprintf f "-%a" pp_exp e
    else Format.fprintf f "%i*%a" n pp_exp e);
    pp_ie_list true f nel

let pp_ident = pp_exp

let pp_idset f ids =
  Format.fprintf f "{%a}" (pp_seq pp_ident ",") (IdSet.elements ids)

let rec pp_seq pp s f = function
  | [] -> ()
  | [x] -> pp f x
  | x::l -> pp f x; Format.pp_print_string f s; pp_seq pp s f l

let rec pp_fld f l = match l with
  | PCons (c, e, l) ->
      Format.pp_print_string f (string_of_component c);
      Format.pp_print_char f ':';
      pp_exp f e;
      begin match l with
	| PNil -> ()
	| _ -> Format.pp_print_char f ','; pp_fld f l
      end
  | PNil -> ()


(* -------------------------------------------------------------------------- *)
(** {2 Identifier Pools} *)
(* -------------------------------------------------------------------------- *)

type idpool = 
  { idp_gensym: (string -> Id.t);
    idp_name: string; 
    mutable idp_alloc: Id.t array }

let idpool_new gensym name = 
  { idp_gensym = gensym;
    idp_name = name;
    idp_alloc = Array.init 16 (fun _ -> gensym name) }

let idpool_combine pool xl =
  let rec array_combine arr i xl = match xl with
    | [] -> PNil
    | x::xl -> PCons(x, arr.(i), array_combine arr (i + 1) xl) in
  let rec f n m = if n <= m then f (n * 2) m else n in
  let m = List.length xl in
  let arr = pool.idp_alloc in
  let n = Array.length arr in
  if n >= m then
    array_combine arr 0 xl
  else begin
    let gs = pool.idp_gensym in
    let s = pool.idp_name in
    let new_arr = Array.init (f n m) 
      (fun i -> if i < n then arr.(i) else gs s) in
    pool.idp_alloc <- new_arr;
    array_combine new_arr 0 xl
  end

let idpool_combine2 pool xl =
  let res = idpool_combine pool (IdSet.elements xl) in
  (mk_subst res, mk_subst (PList.fold (fun x y r -> PCons(y,x,r)) res PNil))


