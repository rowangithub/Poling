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

let print_stats = ref false

(** shape qualifiers file *)
let qfile = ref ""
(** pure qualifiers file *)
let pfile = ref ""
(** inv file *)
let ifile = ref ""

(** loading user-provied shape qualifiers *)
let load_shape_qualifier qname = 
	let comm = if Genarith.enabled () then "// " else "" in
  let ic = 
    Misc.pp "%sQFile %s@." comm qname;
    open_in qname
  in
  let lex = Lexing.from_channel ic in
  Lexer.init lex qname;
  let qs = Qualifier.convert (Parser.assn Lexer.token lex) in
	let _ = Misc.pp "shape qualifier: %a@." Assertions.pp_cprop qs in
  close_in ic;
  qs

let load_pure_qualifier pname = 
	let comm = if Genarith.enabled () then "// " else "" in
  let ic = 
    Misc.pp "%sPFile %s@." comm pname;
    open_in pname
  in
  let lex = Lexing.from_channel ic in
  Lexer.init lex pname;
  let ps = Qualifier.transl_pure_qualifiers (Parser.qualifiers Lexer.token lex) in
	let _ = List.iter Qualifier.print_pure_qual ps in
  close_in ic;
  ps
	
let verify lex =
  let prover = Prover.default_prover in
  let abstraction = Abstraction.mk_abstraction prover in
  Symbsimp.stabilisation_iterations := 0;
  Abstraction.prover_calls := 0;
  try 
		(** The program is converted into intermediate representation *)
    let xs = Tycheck.convert (Parser.program Lexer.token lex) in
		(*let qs = 
			if ((String.compare "" !qfile) = 0) then []
			else (Symbsimp.qs_given := true; load_shape_qualifier !qfile) in*)
		let ps = 
			if ((String.compare "" !pfile) = 0) then []
			else (Symbsimp.ps_given := true; load_pure_qualifier !pfile) in
		let qs = 
			if ((String.compare "" !ifile) = 0) then []
			else (Symbsimp.inv_given:= true; load_shape_qualifier !ifile) in
    let init_time = Sys.time () in
    let valid = Symbsimp.check_props prover abstraction xs qs ps in
    let final_time = Sys.time () in
    let comm = if Genarith.enabled () then "// " else "" in
    Misc.pp "%s%sValid@." comm (if valid then "" else "NOT ");
    Misc.pp "%sTime (RGSep%s): %.2fs@." comm (if !Symbsimp.infer >= 2 then "+Linear" else "") (final_time -. init_time);
    if !print_stats then begin
      Misc.pp "@.=======================[ Stabilization statistics ]=========================";
      Misc.pp "@.Iterations:           %6d"   (!Symbsimp.stabilisation_iterations);
      Misc.pp "@.Theorem prover calls: %6d@." (!Abstraction.prover_calls);
    end; valid
  with Location.Parse_error (s, loc) ->
    print_endline (Location.sprint loc ^ s); false

(** @version for calls from gui. *)
let verify_string s =
  verify (Lexing.from_string s)

(** start verifying from this call. *)
let verify_stdin () =
  let lex = Lexing.from_channel stdin in
  Lexer.init lex "<stdin>";
  verify lex
  
(** @version Not used in the tool. See the above one. *)
let verify_fname fname =
  let comm = if Genarith.enabled () then "// " else "" in
  let ic = 
		print_string "OUTPUT: \n";
    Misc.pp "%sFile %s@." comm fname;
    open_in fname
  in
  let lex = Lexing.from_channel ic in
  Lexer.init lex fname;
  let res = verify lex in
  close_in ic;
  res