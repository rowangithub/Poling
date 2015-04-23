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

(* Common theorem prover interface *)
module P = Predicate

(********************************************************************************)
(************************** Rationalizing Division ******************************)
(********************************************************************************)

let rec fixdiv p = 
  let expr_isdiv = 
    function P.Binop(_, P.Div, _) -> true
      | _ -> false in 
  let pull_const =
    function P.PInt(i) -> i
      | _ -> 1 in
  let pull_divisor =
    function P.Binop(_, P.Div, d1) ->
      pull_const d1 
      | _ -> 1 in
  let rec apply_mult m e =
    match e with
        P.Binop(n, P.Div, P.PInt(d)) ->
          (*let _ = assert ((m/d) * d = m) in*)
            P.Binop(P.PInt(m/d), P.Times, n) 
      | P.Binop(e1, rel, e2) ->
          P.Binop(apply_mult m e1, rel, apply_mult m e2) 
      | P.PInt(i) -> P.PInt(i*m)
      | e -> P.Binop(P.PInt(m), P.Times, e)
  in
  let rec pred_isdiv = 
    function P.Atom(e, _, e') -> (expr_isdiv e) || (expr_isdiv e')
      | P.Iff (px, q) -> expr_isdiv px || pred_isdiv q
      | P.And(p, p') -> (pred_isdiv p) || (pred_isdiv p')
      | P.Or(p, p') -> (pred_isdiv p) || (pred_isdiv p')
      | P.True -> false
      | P.Not p -> pred_isdiv p 
			| P.In (px, qx) -> false
			| P.Recpred _ -> false in
  let calc_cm e1 e2 =
    pull_divisor e1 * pull_divisor e2 in
  if pred_isdiv p then
     match p with
       P.Atom(e, r, e') -> 
         let m = calc_cm e e' in
         let e'' = P.Binop(e', P.Minus, P.PInt(1)) in
         let bound (e, r, e', e'') = 
           P.And(P.Atom(apply_mult m e, P.Gt, apply_mult m e''),
                 P.Atom(apply_mult m e, P.Le, apply_mult m e')) in
           (match (e, r, e') with
                (P.Var v, P.Eq, e') ->
                  bound (e, r, e', e'')
              | (P.PInt v, P.Eq, e') ->
                  bound (e, r, e', e'')
              | _ -> p) 
     | P.And(p1, p2) -> 
         let p1 = if pred_isdiv p1 then fixdiv p1 else p1 in
         let p2 = if pred_isdiv p2 then fixdiv p2 else p2 in
           P.And(p1, p2)      
     | P.Or(p1, p2) ->
         let p1 = if pred_isdiv p1 then fixdiv p1 else p1 in
         let p2 = if pred_isdiv p2 then fixdiv p2 else p2 in
           P.Or(p1, p2) 
     | P.Not p1 -> P.Not(fixdiv p1) 
     | p -> p
    else p

(********************************************************************************)
(*********************** Memo tables and Stats Counters  ************************)
(********************************************************************************)

let nb_push = ref 0
let nb_queries = ref 0
let nb_cache_miss = ref 0
let qcachet: (string * string, bool) Hashtbl.t = Hashtbl.create 1009 

(********************************************************************************)
(************************************* API **************************************)
(********************************************************************************)

(* API *)
let print_stats () =
  TheoremProverYices.Prover.print_stats ();
  Misc.pp
    "@[Prover stats:@ %d@ pushes,@ %d@ queries,@ %d@ cache misses\n@]" 
    !nb_push !nb_queries !nb_cache_miss; flush stdout


(* API *)
let reset () =
  Hashtbl.clear qcachet; 
  nb_push  := 0;
  nb_queries := 0; 
  nb_cache_miss := 0

(* API Usage Pattern: implies must be followed by finish *)
let implies p = 
  let _ = incr nb_push in
  let p = fixdiv p in
  
  let check_yi = Bstats.time "YI implies(1)" TheoremProverYices.Prover.implies p in
  fun q -> 
    let q = incr nb_queries; Bstats.time "fixdiv" fixdiv q in
    Bstats.time "YI implies(2)" check_yi q 
 

let finish () = 
  TheoremProverYices.Prover.finish ()
	
(*
let test () = 
	let var1 = Exp.Id.gensym_str "a" in
	let var2 = Exp.Id.gensym_str "b" in
	let p1 = Predicate.Atom ((Predicate.Var var1), Predicate.Eq, (Predicate.Var var2)) in
	let p2 = Predicate.Atom ((Predicate.Var var1), Predicate.Ge, (Predicate.Var var2)) in
	let result = implies p2 p1 in
	let _ = finish () in
	Misc.pp "@.testing theorem prover result is %b@." result*)
	
