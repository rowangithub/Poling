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
(** Library functions and miscellaneous routines *)

let formatter = ref Format.std_formatter

let pp s = Format.fprintf !formatter s

(* -------------------------------------------------------------------------- *)
(** {2 Additions to the standard library} *)
(* -------------------------------------------------------------------------- *)

module StringSet =
  Set.Make(struct
    type t = string
    let compare = String.compare
  end)

module StringMap =
  Map.Make(struct
    type t = string
    let compare = String.compare
  end)

let identity x = x
let ( |>  ) x f = f x
let ( |>> ) x f = f x; x
let ( >>  ) f g x = g (f x)
let ( >>= ) x f = match x with None -> None | Some v -> f v


let mergeHashtbl tb1 tb2 = 
	let _ = Hashtbl.iter (fun key value ->
		Hashtbl.replace tb1 key value
		) tb2
	in tb1
		
let hashtbltoList tb = 
	Hashtbl.fold (fun key value res -> 
		(key, value) :: res
		) tb []

module List = struct 
  include List

  let rec fold f l r = match l with
    | x::xl -> fold f xl (f x r)
    | [] -> r

  let rec fold_cons f l r = match l with
    | x::xl -> fold_cons f xl (f x :: r)
    | [] -> r
  
  let rec fold_append f l r = match l with
    | x::xl -> fold_append f xl (rev_append (f x) r)
    | [] -> r

  let lifted_fold f =
    let rec go l acc = match l with
      | x :: ln ->
	  begin match f x acc with
	    | None -> None
	    | Some acc -> go ln acc
	  end
      | [] -> Some acc in
    go
  
  let reduce f l = fold f l []
  let reduce_append f l = fold_append f l []
  
  let rec filter_not f l = match l with
    | [] -> []
    | x::xl -> 
        if f x then filter_not f xl else x :: filter_not f xl
  
	let map_i f l = 
		let rec go i = function 
			| [] -> []
			| x :: xl -> (f i x) :: (go (i+1) xl) in
		go 0 l 
	
  let map_partial f l =
    let rec go = function
      | [] -> []
      | x::xl -> match f x with
         | None -> go xl
         | Some y -> y :: go xl in
    go l
  
  let map_option f l =
    let add a b =
      match a with
        | None -> None
        | Some l' ->
  	  match f b with
  	    | None -> None
  	    | Some x -> Some (x::l')
    in match fold_left add (Some []) l
      with
        | None -> None
        | Some l' -> Some (List.rev l')

	(* p [1; 2; 3];; *)
	let rec power_set = function a::b->power_set b@List.map((@)[a])(power_set b)|l->[l]
 
	let remove_duplicates l =
  	let remove_elt e l =
  		let rec go l acc = match l with
    		| [] -> List.rev acc
    		| x::xs when e = x -> go xs acc
    		| x::xs -> go xs (x::acc)
  		in go l []
		in
		let rec go l acc = match l with
    	| [] -> List.rev acc
    	| x :: xs -> go (remove_elt x xs) (x::acc)
  	in go l []
		
	let rec expand f xs ys =
		match xs with
  		| [] -> ys
  		| x::xs ->
      	let (xs',ys') = f x in
      	expand f (List.rev_append xs' xs) (List.rev_append ys' ys)
				
	let rec to_string sep pf l =
		let rec print l = match l with
			| [] -> ""
			| x :: l' -> (pf x) ^ sep ^ (print l') in
		let str = print l in
		pp "%s" str
		
	let flap f xs = 
  List.flatten (List.map f xs)

	let rec lflap es =
	  match es with
	    | s :: [] ->
	        List.map (fun c -> [c]) s
	    | s :: es ->
	        flap (fun c -> List.map (fun d -> c :: d) (lflap es)) s
	    | [] ->
	        []
	
	let tflap3 (e1, e2, e3) f =
	  flap (fun c -> flap (fun d -> List.map (fun e -> f c d e) e3) e2) e1
	
	let tflap2 (e1, e2) f =
	  flap (fun c -> List.map (fun d -> f c d) e2) e1
		
	let rec isPrefix compare l1 l2 = 
		match (l1, l2) with
			| (h1::l1, h2::l2) -> ((compare h1 h2) = 0) && isPrefix compare l1 l2
			| ([], []) -> true  
			| ([], _) -> true
			| (_, []) -> false

	let isSuffix compare l1 l2 = isPrefix compare (rev l1) (rev l2)
	
	(* insert x at all positions into l and return the list of results *)
	let rec insert x l = match l with
		| [] -> [[x]]
		| a::m -> (x::l) :: (List.map (fun y -> a::y) (insert x m))

	(* list of all permutations of l *)
	let rec perms l = match l with
		| a::m -> List.flatten (List.map (insert a) (perms m))
		| _ -> [l]
	
	let intersect l1 l2 f = 
		List.filter (fun x -> List.exists (fun y -> f x y) l2) l1
		
	let copy l = rev (List.fold_left (fun res e -> e :: res) [] l)
	
end

(* -------------------------------------------------------------------------- *)
(** {2 Components} *)
(* -------------------------------------------------------------------------- *)

let component_ht = Hashtbl.create 64
let component_arr = ref (Array.make 64 "")
let component_max = ref 0

type component = int

let string_of_component s = component_arr.contents.(s)

let string_of_field_component s =
  let s = string_of_component s in
  assert(s <> "" && Pervasives.(=) (String.get s 0) '.');
  String.sub s 1 (String.length s - 1)

let component_is_field s = 
  let s = string_of_component s in
  assert(s <> "");
  String.get s 0 = '.'

let component_of_string s = 
  try Hashtbl.find component_ht s 
  with Not_found ->
    (let n = component_max.contents in 
     if n >= Array.length component_arr.contents then begin
	let old_arr = component_arr.contents in
	let old_len = Array.length old_arr in
	let new_arr = Array.init (old_len * 2)
          (fun i -> if i < old_len then old_arr.(i) else "") in
        component_arr.contents <- new_arr
     end;
     component_arr.contents.(n) <- s;
     component_max.contents <- n + 1;
     Hashtbl.add component_ht s n;
     n)

let compare_component (s1:component) (s2:component) = compare s1 s2

let node_component = component_of_string "Node"

module CompSet =
  Set.Make(struct
    type t = component
    let compare = compare_component
  end)

(* default component tags *)
let list_data_tag = component_of_string ".val"
let abs_data_tag  = component_of_string ".abs_val"
let list_link_tag = component_of_string ".tl"
let tree_data_tag = component_of_string ".d"
let tree_link_tags = component_of_string ".l", component_of_string ".r"
let dl_Llink_tag,dl_Rlink_tag = tree_link_tags (* the parser assumes this *)

let abs_res_field = component_of_string ".abs_res"

let is_value_field s = (s == list_data_tag || s == abs_data_tag || s == abs_res_field)
let is_lock_field s = 
  let s = string_of_component s in 
  (s = ".hd" || s = ".lk" || s = ".H_lock" || s = ".T_lock")

let possible_link_fields = ref ([] : component list)

(* -------------------------------------------------------------------------- *)
(** {2 Packed association lists} *)
(* -------------------------------------------------------------------------- *)

type ('a, 'b) plist =
    PNil 
  | PCons of 'a * 'b * ('a, 'b) plist

module PList = struct

  let nil = PNil
    
  let cons k v l = PCons(k,v,l)
    
  let for_all f = 
    let rec go = function
      | PCons(k, v, l) -> f k v && go l
      | PNil -> true in
    go

  let exists f =
    let rec go = function
      | PCons(k, v, l) -> f k v || go l
      | PNil -> false in
    go
      
  let fold f =
    let rec go l acc = match l with
      | PCons(k, v, ln) -> go ln (f k v acc)
      | PNil -> acc in
    go

  let fold_val f =
    let rec go l acc = match l with
      | PCons(_, v, ln) -> go ln (f v acc)
      | PNil -> acc in
    go

  let lifted_fold f =
    let rec go l acc = match l with
      | PCons (k, v, ln) ->
	  begin match f k v acc with
	    | None -> None
	    | Some acc -> go ln acc
	  end
      | PNil -> Some acc in
    go

  let iter f =
    let rec go l = match l with
      | PCons(k, v, ln) -> f k v; go ln
      | PNil -> () in
    go

  let iter_val f =
    let rec go l = match l with
      | PCons(_, v, ln) -> f v; go ln
      | PNil -> () in
    go

  let rec rev_append x y = match x with
    | PCons (k, v, z) -> rev_append z (PCons (k, v, y))
    | PNil -> y

  let length l =
    let rec go acc l = match l with
      | PCons(_, _, ln) -> go (acc + 1) ln
      | PNil -> acc in
    go 0 l

  let filter f =
    let rec go l = match l with
      | PCons(k, v, ln) ->
          if f k v then
            let l' = go ln in
	    if l' == ln then l else PCons (k, v, l')
          else go ln
      | PNil -> PNil in
    go

  let rev_partition f =
    let rec go acc1 acc2 l = match l with
      | PCons(k, v, l) ->
          if f k v then go (PCons (k, v, acc1)) acc2 l
	  else go acc1 (PCons (k, v, acc2)) l
      | PNil -> (acc1, acc2) in
    go PNil PNil

  let map_val f_e =
    let rec go l = match l with
      | PCons (k, v, ln) ->
          let v' = f_e v in
          let l' = go ln in
          if v' == v && l' == ln then l else PCons (k, v', l')
      | PNil -> PNil in
  go

  let rec merge cmp_key l1 l2 = match l1, l2 with
    | PNil, _ -> l2
    | _, PNil -> l1
    | PCons(k1,v1,ln1), PCons(k2,v2,ln2) ->
	if cmp_key k1 k2 < 0 then
	  PCons(k1, v1, merge cmp_key ln1 l2)
	else
	  PCons(k2, v2, merge cmp_key l1 ln2)

  let rec mem_assq k l = match l with
    | PCons (k', _, ln) -> k == k' || mem_assq k ln
    | PNil -> false

  let rec try_assq k l = match l with
    | PCons (k', v', _) when k == k' -> Some v'
    | PCons (_, _, ln) -> try_assq k ln
    | PNil -> None

  let rec assq k l = match l with
    | PCons (k', v', _) when k == k' -> v'
    | PCons (_, _, ln) -> assq k ln
    | PNil -> raise Not_found

  let rec remove_assq k l = match l with
    | PCons (k', _, ln) when k == k' -> ln
    | PCons (k', v', ln) -> PCons (k', v', remove_assq k ln)
    | PNil -> PNil

  let rec findq l e x = match l with
    | PCons (k, v, ln) ->
         if k == x then v else findq ln e x
    | PNil -> e

  let rec get_first f l = match l with
    | PCons (k, v, ln) ->
	begin match f k v with 
	  | (Some _ as o) -> o
	  | None -> get_first f ln
	end
    | PNil -> None

  let rec combine l1 l2 = match l1 with
    | [] -> PNil
    | x :: l1 ->
	begin match l2 with
	  | [] -> PNil
	  | y :: l2 -> PCons (x, y, combine l1 l2)
	end

end
