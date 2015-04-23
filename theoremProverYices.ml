(* Poling: Proof Of Linearizability Generator 
 * Poling is built on top of CAVE and shares the same license with CAVE 
 * See LICENSE.txt for license.
 * Contact: He Zhu, Department of Computer Science, Purdue University
 * Email: zhu103@purdue.edu
 *)

(*
 * Copyright © 2008 The Regents of the University of California. All rights reserved.
 *
 * Permission is hereby granted, without written agreement and without
 * license or royalty fees, to use, copy, modify, and distribute this
 * software and its documentation for any purpose, provided that the
 * above copyright notice and the following two paragraphs appear in
 * all copies of this software.
 *
 * IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY
 * FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES
 * ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN
 * IF THE UNIVERSITY OF CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 * THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS
 * ON AN "AS IS" BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION
 * TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 *
 *)

(* This file is part of the SIMPLE Project.*)

open Predicate

let log_queries = ref false

let args = 
  [("-log_queries", Arg.Set log_queries, " Remember SMT Prover information (Yices 1.0 2013)")]

module type PROVER = 
  sig
    (*
    (* push p: tell prover to assume fact p *)
    val push : Predicate.t -> unit 
    
    (* pop () : tell prover to un-assume last assumed fact *)
    val pop : unit -> unit 
    
    (* reset (): tell prover to remove all assumed facts *)
    val reset : unit -> unit 
    
    (* valid p : do the currently assumed facts imply p ? *)
    val valid : Predicate.t -> bool
    *)

    (* implies p q = true iff predicate p (provably) implies predicate q *)
    val implies : Predicate.t -> Predicate.t -> bool

    val finish : unit -> unit

    val print_stats : unit -> unit
  end


module Y = Oyices

module YicesProver : PROVER = 
  struct
    type yices_instance = { 
      mutable c : Y.yices_context;
      mutable t : Y.yices_type;
      mutable f : Y.yices_type;
      mutable binop: Y.yices_type; (* for uninterp ops *)
      mutable d : (string,Y.yices_var_decl) Hashtbl.t;
      mutable ds : string list ;
      mutable count : int;
      mutable i : int;
      mutable consistent: bool;
    }

    let nb_yices_push = ref 0

    let barrier = "0" 
		
		let union_op = "union"
		
		let concat_op = "union"

		(** do_memo and repeat_fn are two util functions *)
		let do_memo t f arg key =
			try Hashtbl.find t key with Not_found ->
    	let rv = f arg in
    	let _ = Hashtbl.replace t key rv in
    	rv
			
		(** repeats f: unit - > unit i times *)
		let rec repeat_fn f i = 
  		if i = 0 then ()
  		else (f (); repeat_fn f (i-1))

    let yicesVar me s ty =
      let decl = 
        do_memo me.d
        (fun () -> 
          let rv = Y.yices_mk_var_decl me.c s ty in
            me.ds <- s::me.ds;rv) () s in
      Y.yices_mk_var_from_decl me.c decl

    let rec isconst = function
			| Predicate.PInt(i) -> true
      | _ -> false

    let rec yicesExp me e = match e with 
			| Predicate.PInt i -> Y.yices_mk_num me.c i 
      | Predicate.Var s -> yicesVar me (Exp.Id.to_string s) me.t
      | Predicate.FunApp (f,e) -> 
          (*let (fn, e') = (yicesVar me f me.f, List.map (yicesExp me) e) in Y.yices_mk_app me.c fn (Array.of_list e')*)
					let t = me.t in
          let	tl = Array.make (List.length e) t in
          let ftype = Y.yices_mk_function_type me.c tl t in
          let (func, e') = (yicesVar me f ftype, List.map (yicesExp me) e) in
          Y.yices_mk_app me.c func (Array.of_list e')
      | Predicate.Binop (e1,op,e2) ->
				let es' = Array.map (yicesExp me) [|e1;e2|] in
          (match op with 
						| Predicate.Plus  -> Y.yices_mk_sum me.c es'
           	| Predicate.Minus -> Y.yices_mk_sub me.c es'
           	| Predicate.Times ->
							if (isconst e1) || (isconst e2) then
		 						Y.yices_mk_mul me.c es'
	       			else
		 						let (fd, e1, e2) = (yicesVar me "_MUL" me.binop, yicesExp me e1, yicesExp me e2) in
		   					Y.yices_mk_app me.c fd [|e1; e2|]
	   | Predicate.Div ->
				let (fd, e1, e2) = (yicesVar me "_DIV" me.binop, yicesExp me e1, yicesExp me e2) in
		 		Y.yices_mk_app me.c fd [|e1; e2|])
      | Predicate.Field (f, e) ->
        (* pmr: this crucially depends on not having two fields with the same name in the
           same module *)
        let (fn, e') = (yicesVar me (Printf.sprintf "SELECT_%s" f) me.f, yicesExp me e) in
        Y.yices_mk_app me.c fn [|e'|]
      | Predicate.Proj (n, e) ->
      	let (fn, e') = (yicesVar me (Printf.sprintf "PROJ_%d" n) me.f, yicesExp me e) in
        Y.yices_mk_app me.c fn [|e'|]
			| Predicate.Union (e1, e2) ->
				let union_eles = [e1; e2] in
				let t = me.t in
        let	tl = Array.make (List.length union_eles) t in
        let ftype = Y.yices_mk_function_type me.c tl t in
        let (func, e') = (yicesVar me union_op ftype, List.map (yicesExp me) union_eles) in
        Y.yices_mk_app me.c func (Array.of_list e')
			| Predicate.Concat (e1, e2) ->
				let concat_eles = [e1; e2] in
				let t = me.t in
        let	tl = Array.make (List.length concat_eles) t in
        let ftype = Y.yices_mk_function_type me.c tl t in
        let (func, e') = (yicesVar me concat_op ftype, List.map (yicesExp me) concat_eles) in
        Y.yices_mk_app me.c func (Array.of_list e') 
				
    let rec yicesPred me p = 
      match p with 
        Predicate.True -> Y.yices_mk_true me.c
      | Predicate.Not p' -> Y.yices_mk_not me.c (yicesPred me p')
      | Predicate.And (p1,p2) -> Y.yices_mk_and me.c (Array.map (yicesPred me) [|p1;p2|])
      | Predicate.Or (p1,p2) -> Y.yices_mk_or me.c (Array.map (yicesPred me) [|p1;p2|])
      | Predicate.Iff _ as iff -> yicesPred me (Predicate.expand_iff iff)
      | Predicate.Atom (e1,Predicate.Lt,e2) ->
          yicesPred me (Atom (e1, Predicate.Le, Binop(e2,Predicate.Minus,PInt 1)))
    		(* RJ: why not this ?
     		* | P.Atom (e1,P.Gt,e2) -> 
        yicesPred me (Atom (e2, P.Le, Binop(e1,P.Minus,PInt 1))) *)
      | Predicate.Atom (e1,br,e2) ->
          let e1' = yicesExp me e1 in
          let e2' = yicesExp me e2 in
          (match br with 
             Predicate.Eq -> Y.yices_mk_eq me.c e1' e2' 
           | Predicate.Ne -> Y.yices_mk_diseq me.c e1' e2'
           | Predicate.Gt -> Y.yices_mk_gt me.c e1' e2'
           | Predicate.Ge -> Y.yices_mk_ge me.c e1' e2'
           | Predicate.Lt -> Y.yices_mk_lt me.c e1' e2'
           | Predicate.Le -> Y.yices_mk_le me.c e1' e2')
			| Predicate.In (px, qx) ->
				let union_eles = Predicate.flatten_union qx in
				let newp = 
					Predicate.big_or (List.map (fun ue -> Predicate.Atom (px, Predicate.Eq, ue)) union_eles) in
   			yicesPred me newp
			| Predicate.Recpred (f, e) -> 
				let t = me.t in
        let	tl = Array.make 1 t in
        let ftype = Y.yices_mk_function_type me.c tl t in
        let (func, e') = (yicesVar me f ftype, yicesExp me e) in
        Y.yices_mk_app me.c func [|e'|]

    let me = 
    	let c = Y.yices_mk_context () in
      let _ = if !log_queries then Y.yices_enable_log_file "yices.log" else () in
      let t = Y.yices_mk_type c "int" in
      let binop = Y.yices_mk_function_type c [| t; t |] t in
      let f = Y.yices_mk_function_type c [| t |] t in
      let d = Hashtbl.create 37 in
        { c = c; t = t; f = f; binop = binop; d = d; 
          ds = []; count = 0; i = 0; consistent = true}

    let push p =
      me.count <- me.count + 1;
      if (Bstats.time "Yices consistency" Y.yices_inconsistent me.c) = 1 
      then me.i <- me.i + 1 else
        let p' = Bstats.time "Yices mk pred" (yicesPred me) p in
        let _ = me.ds <- barrier :: me.ds in
        let _ = Bstats.time "Yices stackpush" Y.yices_push me.c in
        Bstats.time "Yices assert" (Y.yices_assert me.c) p' 
      
    let rec vpop (cs,s) =
      match s with [] -> (cs,s)
      | h::t when h = barrier -> (cs,t)
      | h::t -> vpop (h::cs,t)

    let pop () =
      me.count <- me.count - 1;
      if me.i > 0 then me.i <- me.i - 1 else
        let (cs,ds') = vpop ([],me.ds) in
				let _ = me.ds <- ds' in
				let _ = List.iter (Hashtbl.remove me.d) cs in
        Bstats.time "popping" Y.yices_pop me.c

    let reset () =
      repeat_fn pop me.count;
      Y.yices_reset me.c;
      me.t <- Y.yices_mk_type me.c "int";
      me.binop <- Y.yices_mk_function_type me.c [| me.t; me.t |] me.t;
      me.f <- Y.yices_mk_function_type me.c [| me.t |] me.t;
      me.d <- Hashtbl.create 37;
      me.ds <- [];
      me.count <- 0;
      me.i <- 0

    let unsat () =
      (*let rv = (Bstats.time "Yices unsat" Y.yices_check me.c) = -1 in
      rv*)
			let result = Y.yices_check me.c in
			(*let _ = Misc.pp "result is %d\n" result in *)
			(result = -1)

    let valid p =
      if unsat () then true else 
				(*let _ = Misc.pp "implies q is %a@." Predicate.pprint p in*)
        let _ = push (Predicate.Not p) in
        let rv = unsat () in
				(*let _ = Misc.pp "checking result is %b\n" rv in*)
        let _ = pop () in rv
    
    let implies p =
      let _ = incr nb_yices_push; Bstats.time "Yices push" push p in
			(*let _ = Misc.pp "symb state is %a\n" Predicate.pprint p in*)
      fun q -> ((*Misc.pp "vc goal is %a\n" Predicate.pprint q;*) Bstats.time "Yices valid" valid q)

    let finish () = 
      Bstats.time "YI pop" pop (); 
      assert (me.count = 0)
  
  	let print_stats () = 
    	Printf.printf "Yices pushes = %d \n" !nb_yices_push

end

module Prover = YicesProver
