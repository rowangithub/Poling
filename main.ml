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

let columns = ref 72
let fnames = ref []

let _ =
  let prM s (w: float) = Misc.pp "@.%s%9.2fMB" s (w *. 4.0 /. 1048576.0) in

  let speclist = 
    let (++) = List.append in
    (Assertions.args
     ++ Prover.args 
     ++ Abstraction.args
     ++ Symbsimp.args
     ++ Genarith.args
     ++ [("-columns", Arg.Set_int columns, "<n> Format output for a number of columns");
	 		("-stats", Arg.Set Mcpamain.print_stats, " Display memory statistics");
			("-qfile", Arg.Set_string Mcpamain.qfile, " Set shape qualifiers input file");
			("-pfile", Arg.Set_string Mcpamain.pfile, " Set pure qualifiers input file");
			("-ifile", Arg.Set_string Mcpamain.ifile, " Set invariant input file ")]) in

  let re = Str.regexp_string "Display" in
  let cmp ((_,_,xd) as x) ((_,_,yd) as y) =
    let f x = try ignore (Str.search_forward re x 0); true with Not_found -> false in
    let n = Pervasives.compare (f xd) (f yd) in if n <> 0 then n else
    Pervasives.compare x y in

  Arg.parse 
    (Arg.align (List.sort cmp speclist))
    (fun s -> fnames := s :: !fnames)
    ("Usage: " ^ Sys.argv.(0) ^ " [options] <files>");
  fnames := List.rev !fnames;

  Format.pp_set_margin    !Misc.formatter !columns;
  Format.pp_set_max_boxes !Misc.formatter max_int;

	
  begin match !fnames with
    | [] -> ignore (Mcpamain.verify_stdin ())
    | l -> List.iter (fun x -> ignore (Mcpamain.verify_fname x)) l
  end;
  if !Mcpamain.print_stats then begin
    let gc = Gc.quick_stat () in 
    Misc.pp "@.==========================[ Memory statistics ]=============================";
    prM "Total:   " (gc.Gc.minor_words +. gc.Gc.major_words -. gc.Gc.promoted_words);
    prM "Max:     " (float_of_int gc.Gc.top_heap_words);
    prM "Minor:   " gc.Gc.minor_words;
    Misc.pp "      Minor collections: %7d" gc.Gc.minor_collections;
    prM "Major:   " gc.Gc.major_words;
    Misc.pp "      Major collections: %7d" gc.Gc.major_collections;
    prM "Promoted:" gc.Gc.promoted_words;
    Misc.pp "      Compactions:       %7d@." gc.Gc.compactions;
  end
