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

open Tk


let verify inwidg outwidg =
  Text.configure ~background:(`Color "#FFDD80") outwidg;
  let s = Text.get ~start:(`Atxy(0,0),[]) ~stop:(`End,[]) inwidg in
  let b = Mcpamain.verify_string s in
  Text.configure ~background:(if b then `Color "#A0FFA0" else `Color "#FF8080") outwidg


let _ =
  let top = openTk () in 
  Wm.title_set top "CAVE: Concurrent Algorithm VErifier";
  
  (* Base frame *)
  let base = Frame.create top in

  (* Text and scrollbar *)
  let (left,input_txt) = 
    let frame = Frame.create base in 
    let txt   = Text.create ~width:100 ~height:50 ~background:(`Color "#FFEECC") frame in
    let sb    = Scrollbar.create frame in
    Text.insert ~index:(`End,[]) ~text:"// Type your program here" txt;
    Text.configure ~yscrollcommand:(Scrollbar.set sb) txt;
    Scrollbar.configure ~command:(Text.yview txt) sb;
    pack ~side:`Right ~fill:`Y [sb];
    pack ~side:`Left ~fill:`Both ~expand:true [txt];
    (frame, txt)
  in

  let (right,output_txt) =
    let frame = Frame.create base in 
    let txt   = Text.create ~width:100 ~height:50 ~background:(`Color "#FFDD80") frame in
    let sb    = Scrollbar.create frame in
    Text.insert ~index:(`End,[]) ~text:"Prover's output goes here." txt;
    Text.configure ~yscrollcommand:(Scrollbar.set sb) txt;
    Scrollbar.configure ~command:(Text.yview txt) sb;
    pack ~side:`Right ~fill:`Y [sb];
    pack ~side:`Left ~fill:`Both ~expand:true [txt];
    (frame, txt)
  in
 
  (* Buttons *)

  let newf_fn () = 
     Text.delete ~start:(`Atxy(0,0),[]) ~stop:(`End,[]) input_txt in
  let openf_fn () = 
    let fname = getOpenFile ~title:"CAVE: Open file" () in
    if fname <> "" then begin
      try 
        let ic = open_in fname in
        let len = in_channel_length ic in
        let s = String.create len in
        really_input ic s 0 len;
        close_in ic;
        Text.delete ~start:(`Atxy(0,0),[]) ~stop:(`End,[]) input_txt;
        Text.insert ~index:(`End,[]) ~text:s input_txt;
      with Sys_error s ->
        ignore (messageBox 
           ~icon:`Error
           ~message:s
           ~title:"CAVE: File open error"
           ~typ:`Ok ())
    end in
  let insertf_fn () = 
    let fname = getOpenFile ~title:"CAVE: Insert file at current location" () in
    if fname <> "" then begin
      try 
        let ic = open_in fname in
        let len = in_channel_length ic in
        let s = String.create len in
        really_input ic s 0 len;
        close_in ic;
        Text.insert ~index:(`Mark "insert",[]) ~text:s input_txt;
      with Sys_error s ->
        ignore (messageBox 
           ~icon:`Error
           ~message:s
           ~title:"CAVE: File open error"
           ~typ:`Ok ())
    end in
  let save_fn () = 
    let fname = getSaveFile ~title:"CAVE: Save file" () in
    Text.insert ~index:(`End,[]) ~text:fname input_txt
  in
  let quit_fn () = closeTk (); exit 0 in

  let verify_ai_fn () = Symbsimp.infer := 1; verify input_txt output_txt in
  let verify_lin_fn () = Symbsimp.infer := 2; verify input_txt output_txt in

  pack ~side:`Left [left; right];
  pack [base];

  let menu = Menu.create top in

  let m = Menu.create menu in
  Menu.add_cascade ~label:"File" ~menu:m menu;
  Menu.add_command ~label:"New"             ~command:newf_fn m;
  Menu.add_command ~label:"Open File..."    ~command:openf_fn m;
  Menu.add_command ~label:"Insert File..."  ~command:insertf_fn m;
  Menu.add_command ~label:"Save"            ~command:save_fn m;
  Menu.add_command ~label:"Save As..."      ~command:save_fn m;
  Menu.add_separator m;
  Menu.add_command ~label:"Quit"            ~command:quit_fn m;
  
  let m = Menu.create menu in
  Menu.add_cascade ~label:"Verify" ~menu:m menu;
  Menu.add_command ~label:"Action Inference" ~command:verify_ai_fn m;
  Menu.add_command ~label:"Linearizability"  ~command:verify_lin_fn m;

  let m = Menu.create menu in
  Menu.add_cascade ~label:"Help" ~menu:m menu;
  Menu.add_command ~label:"Version" ~command:(fun () ->
        ignore (messageBox 
           ~message:"CAVE version 0.1\nCopyright (c) 2010, Viktor Vafeiadis"
           ~title:"CAVE: Concurrent Algorithm VErifier"
           ~typ:`Ok ())
     ) m;

  Toplevel.configure ~menu:menu top;

  Printexc.print mainLoop () 

