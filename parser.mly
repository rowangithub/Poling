%{
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
open Parsetree

let mkexp d = { pexp_desc = d; pexp_loc = Location.symbol_loc() }
let mkexp_ghost d = { pexp_desc = d; pexp_loc = Location.none }
let mkstm d = { pstm_desc = d; pstm_loc = Location.symbol_loc() }
let mkstm_ghost d = { pstm_desc = d; pstm_loc = Location.none }

(** // MCPA takes user specifications & qualifiers into verification *)
let mkqpat d =
  { pqual_pat_desc = d; pqual_pat_loc = Location.symbol_loc () }
let mkpredpat d =
  { ppredpat_desc = d; ppredpat_loc = Location.symbol_loc() }
let mkpredpatexp d =
  { ppredpatexp_desc = d; ppredpatexp_loc = Location.symbol_loc() }
(** // *)

let exp_one = mkexp_ghost (Pexp_num 1)

let mk_ref_params cel loc =
  let check_par = function
    | {pexp_desc = Pexp_ident i; pexp_loc=l} -> (i,l)
    | _ -> 
    raise(Location.Parse_error("Syntax error: Reference parameters must be variables.", loc)) in
  List.map check_par cel
  
let mk_indpred_params cel =
  let check_par = function
    | {pexp_desc = Pexp_ident i; pexp_loc=l} -> (i,l)
    | {pexp_loc = l} -> 
    raise(Location.Parse_error("Syntax error: Node parameters must be variables.", l)) in
  List.map check_par cel
 
(* implicitly called when no grammar rules apply *)
let parse_error _ =
  raise(
    Location.Parse_error("Syntax error.",
      match !Location.lexbuf with
	| None -> Location.symbol_loc()
	| Some lexbuf ->
	    (* the Parsing library only updates symbol_end_pos when successfully
	     * reducing a grammar rule, so here we ask the lexer for the current
	     * position directly *)
	    Location.mkloc (Parsing.symbol_start_pos()) lexbuf.Lexing.lex_curr_p))


%} /* declarations */

/* tokens */

%token ACTION
%token AMPERAMPER
%token AS
%token ASSUME
%token BARBAR
%token <bool> BOOL
%token BREAK
%token CLASS
%token COLON
%token COMMA
%token COMMENT
%token CONSTRUCTOR
%token CONTINUE
%token DISPOSE
%token DO
%token DOT
%token ELSE
%token EMPTY
%token ENSURES
%token EOF
%token EQUAL
%token <string> IDENT
%token <string> QIDENT
%token <string> FIDENT
%token IF
%token <string> INFIXOP1
%token <string> INFIXOP2
%token <string> INFIXOP3
%token INTERFERE
%token INVARIANT
%token LBRACE
%token LBRACKET
%token LET
%token LPAREN
%token MINUSGREATER
%token <int> NAT
%token NEW
%token PAR
%token POINTSTO
%token RBRACE
%token RBRACKET
%token REQUIRES
%token RESOURCE
%token RETURN
%token RPAREN
%token <string> STRING
%token SEMI
%token STAR
%token THEN
%token TREE
%token <string> UNARYOP
%token UNDERSCORE
%token VOID
%token WHEN
%token WHILE
%token WITH
%token QUALIF
%token SINGLE_QUALIF
%token SPEC
%token TILDE
%token LBRACELESS
%token GREATERRBRACE
%token WILD
%token IN
%token UNION
%token CONCAT
%token REC
%token PURESPEC
%token EFFSPEC
%token IMPLIES
%token SETDECL
%token TDESC

/* precedences (increasing) and associativities for expressions */

%nonassoc bELSE
%nonassoc ELSE AS 
%right BARBAR
%left STAR AMPERAMPER
%left POINTSTO
%left INFIXOP1 EQUAL
%left INFIXOP2
%left INFIXOP3
%nonassoc UNARYOP
%left MINUSGREATER
%left IMPLIES

/* entry points */

%start program         /* verifying programs. FIXME: 1 shift/reduce conflict */
%type <Parsetree.p_program> program
%start assn            /* runtime shape qualifier files */
%type <Parsetree.a_proposition> assn
%start qualifiers      /* runtime pure qualifier files. FIXME: 1 shift/reduce confict */
%type <Parsetree.qualifier_declaration list> qualifiers


%% /* rules */

/* entry points */
program:
  | p_items               { List.rev $1 }
;
p_items:
  | /* empty */           { [] }
  | p_items decl          { $2 :: $1 }
  | p_items d_vars        { $2 @ $1 }
;
d_vars:
  | IDENT ids_ne SEMI        { List.rev_map (fun (x,y)-> Pdec_var(x,$1,y)) $2 }
;
decl:
  | COMMENT STRING SEMI                 { Pdec_comment($2) }
	| CLASS IDENT LBRACE d_fields RBRACE  
			{ Pdec_class($2, None, List.rev $4, Location.rhs_loc 2) }
  | CLASS IDENT class_specs LBRACE d_fields RBRACE  
			{ Pdec_class($2, $3, List.rev $5, Location.rhs_loc 2) }
  | LET IDENT LPAREN ids RPAREN EQUAL LBRACKET assn RBRACKET
      { Pdec_indpred($2,$4,$8,Location.symbol_loc()) }
  | RESOURCE IDENT LBRACE inv set_decl constructor_decl interfere_decl actions RBRACE
      { Pdec_resource(component_of_string $2,[],$4,$6,$7,List.rev $8,$5,Location.symbol_loc()) }
  | RESOURCE IDENT LPAREN ids RPAREN LBRACE inv set_decl constructor_decl interfere_decl actions RBRACE
      { Pdec_resource(component_of_string $2,$4,$7,$9,$10,List.rev $11,$8,Location.symbol_loc()) }
  | VOID IDENT LPAREN formals RPAREN top_block
      { Pdec_fun($2,"void",$4,(None,None,None,None),$6,Location.symbol_loc()) }
  | VOID IDENT LPAREN formals RPAREN fun_specs top_block
      { Pdec_fun($2,"void",$4,$6,$7,Location.symbol_loc()) }
  | fun_specs VOID IDENT LPAREN formals RPAREN top_block
      { Pdec_fun($3,"void",$5,$1,$7,Location.symbol_loc()) }
  | IDENT IDENT LPAREN formals RPAREN top_block
      { Pdec_fun($2,$1,$4,(None,None,None,None),$6,Location.symbol_loc()) }
  | IDENT IDENT LPAREN formals RPAREN fun_specs top_block
      { Pdec_fun($2,$1,$4,$6,$7,Location.symbol_loc()) }
  | fun_specs IDENT IDENT LPAREN formals RPAREN top_block
      { Pdec_fun($3,$2,$5,$1,$7,Location.symbol_loc()) }
;
d_fields:
  | /* empty */                { [] }
  | d_fields IDENT IDENT SEMI  { ("."^$3,$2,Location.rhs_loc 3)::$1 }
;
fun_specs:
  | REQUIRES assn              { (Some $2, None, None, None) }
  | ENSURES assn               { (None, Some $2, None, None) }
  | REQUIRES assn ENSURES assn { (Some $2, Some $4, None, None) }
	| PURESPEC IDENT qualifier_pattern EFFSPEC IDENT qualifier_pattern
			{ (None, None, Some ($2,$3), Some ($5,$6)) }
	| REQUIRES assn PURESPEC IDENT qualifier_pattern EFFSPEC IDENT qualifier_pattern
			{ (Some $2, None, Some ($4,$5), Some ($7,$8)) }
	| ENSURES assn PURESPEC IDENT qualifier_pattern EFFSPEC IDENT qualifier_pattern
			{ (None, Some $2, Some ($4,$5), Some ($7,$8)) }
	| REQUIRES assn ENSURES assn PURESPEC IDENT qualifier_pattern EFFSPEC IDENT qualifier_pattern
			{ (Some $2, Some $4, Some ($6,$7), Some ($9,$10)) }
;
class_specs:
	| TDESC qualifier_pattern { Some $2 }
;
inv_restr:
  | /* empty */            { None }
  | LBRACKET assn RBRACKET { Some $2 }
;
inv:
  | INVARIANT assn         { Some $2 }
  | inv_restr              { $1 }
;
set_decl:
	| SETDECL qualifier_pattern { $2 }
;
constructor_decl:
  | /* empty */            { ([], []) }
  | CONSTRUCTOR top_block  { $2 }
;
interfere_decl:
  | /* empty */              { None }
  | INTERFERE LBRACE stmts RBRACE  { Some (List.rev $3) }
;
action_decl:
  | ACTION IDENT LPAREN ids RPAREN
        LBRACKET assn RBRACKET
	LBRACKET assn RBRACKET
      { ($2,$4,a_prop_empty,$7,$10,[],Location.symbol_loc()) }
  | ACTION IDENT LPAREN ids RPAREN
        LBRACKET assn RBRACKET
	LBRACKET assn RBRACKET
        LBRACKET assn RBRACKET
      { ($2,$4,$7,$10,$13,[],Location.symbol_loc()) }
  | ACTION IDENT LPAREN ids RPAREN 
        LBRACKET assn RBRACKET
	LBRACKET assn RBRACKET
        LBRACE stmts RBRACE
      { ($2,$4,a_prop_empty,$7,$10,List.rev $13,Location.symbol_loc()) }
  | ACTION IDENT LPAREN ids RPAREN 
        LBRACKET assn RBRACKET
        LBRACKET assn RBRACKET
	LBRACKET assn RBRACKET
        LBRACE stmts RBRACE
      { ($2,$4,$7,$10,$13,List.rev $16,Location.symbol_loc()) }
;
actions: | { [] } | actions action_decl { $2::$1 } ;
ids: | { [] } | ids_ne { $1 } ;
ids_ne:
  | IDENT            { [($1,Location.rhs_loc 1)] }
  | IDENT COMMA ids_ne { ($1,Location.rhs_loc 1)::$3 }
;
tyids:  { [] } | tyids_ne { $1 } ;
tyids_ne:
  | IDENT IDENT      { [($2,$1,Location.rhs_loc 2)] }
  | IDENT IDENT COMMA tyids_ne  { ($2,$1,Location.rhs_loc 2)::$4 }
;
top_block:
  | LBRACE top_stmts RBRACE     { $2 }
;
top_stmts:
  |                             { ([],[]) }
  | stmt stmts                  { ([], $1 :: List.rev $2) }
  | IDENT ids_ne SEMI top_stmts { (List.map (fun (x,y) -> (x,$1,y)) $2 @ fst $4, snd $4) }
;
stmts: | { [] } | stmts stmt { $2::$1 }
;
fldassigns:
  | exp MINUSGREATER IDENT EQUAL exp { [($1, component_of_string ("."^$3), $5)] }
  | exp MINUSGREATER IDENT EQUAL exp COMMA fldassigns { ($1, component_of_string ("."^$3), $5)::$7 }
;
stmt:
  | fldassigns SEMI                { mkstm(Pstm_fldassign($1)) }
  | IDENT EQUAL opt_exp SEMI       { mkstm(Pstm_assign($1, $3)) }
  | DISPOSE exp SEMI               { mkstm(Pstm_dispose($2,exp_one)) }
  | DISPOSE LPAREN exp COMMA exp RPAREN SEMI { mkstm(Pstm_dispose($3,$5)) }
  | LBRACE stmts RBRACE            { mkstm(Pstm_block(List.rev $2)) }
  | ASSUME LPAREN exp RPAREN SEMI  { mkstm(Pstm_assume($3)) }
  | INTERFERE IDENT DOT IDENT SEMI { mkstm(Pstm_interfere(component_of_string $2,$4)) }
  | exp SEMI                       { mkstm(Pstm_exp($1)) }
  | PAR LBRACE proc_calls RBRACE   { mkstm(Pstm_parblock(List.rev $3)) }
  | RETURN SEMI                    { mkstm(Pstm_return(None)) }
  | RETURN exp SEMI                { mkstm(Pstm_return(Some $2)) }
  | BREAK SEMI                     { mkstm(Pstm_break) }
  | CONTINUE SEMI                  { mkstm(Pstm_continue) }
  | COMMENT STRING SEMI            { mkstm(Pstm_comment($2)) }
  | IF LPAREN opt_exp RPAREN stmt %prec bELSE  { mkstm(Pstm_if($3, $5, mkstm_ghost(Pstm_block []))) }
  | IF LPAREN opt_exp RPAREN stmt ELSE stmt    { mkstm(Pstm_if($3, $5, $7)) }
  | WHILE LPAREN opt_exp RPAREN inv_restr stmt { mkstm(Pstm_while($5, $3, $6)) }
  | WITH IDENT opt_when stmt %prec bELSE       { mkstm(Pstm_withres(component_of_string $2,$3,$4,"",[])) }
  | WITH IDENT opt_when stmt AS IDENT LPAREN exps RPAREN SEMI { mkstm(Pstm_withres(component_of_string $2,$3,$4,$6,$8)) }
  | DO stmt AS IDENT DOT IDENT LPAREN exps RPAREN SEMI        { mkstm(Pstm_action($2,component_of_string $4,$6,$8)) }
;
proc_call:
  | IDENT LPAREN actuals RPAREN SEMI              { (None,$1,$3) }
  | IDENT EQUAL IDENT LPAREN actuals RPAREN SEMI  { (Some $1,$3,$5) }
;
proc_calls:
  | proc_call             { [$1] }
  | proc_calls proc_call  { $2::$1 }
;
opt_when:
  | /* empty */            { mkexp(Pexp_infix("==", mkexp_ghost(Pexp_num 0), mkexp_ghost(Pexp_num 0))) }
  | WHEN LPAREN exp RPAREN { $3 }
;
exp:
  | IDENT                       { mkexp(Pexp_ident($1)) }
  | NAT                         { mkexp(Pexp_num($1)) }
  | BOOL                        { mkexp(Pexp_bool $1) }
  | LPAREN exp RPAREN           { $2 }
  | LPAREN exp AS IDENT RPAREN  { mkexp(Pexp_cast($2,$4)) }
  | UNARYOP exp                 { mkexp(Pexp_prefix($1, $2)) }
  | INFIXOP2 exp %prec UNARYOP  { mkexp(Pexp_prefix($1, $2)) }
  | exp MINUSGREATER IDENT      { mkexp(Pexp_fld($1, component_of_string ("."^$3))) }
  | NEW LPAREN RPAREN           { mkexp(Pexp_new ("any",exp_one)) }
  | NEW IDENT LPAREN RPAREN     { mkexp(Pexp_new ($2,exp_one)) }
  | NEW IDENT LPAREN exp RPAREN { mkexp(Pexp_new ($2,$4)) }
  | exp BARBAR exp              { mkexp(Pexp_infix("||", $1, $3)) }
  | exp AMPERAMPER exp          { mkexp(Pexp_infix("&&", $1, $3)) }
  | exp STAR exp                { mkexp(Pexp_infix("*", $1, $3)) }
  | exp INFIXOP1 exp            { mkexp(Pexp_infix($2, $1, $3)) }
  | exp INFIXOP2 exp            { mkexp(Pexp_infix($2, $1, $3)) }
  | exp INFIXOP3 exp            { mkexp(Pexp_infix($2, $1, $3)) }
  | IDENT LPAREN actuals RPAREN { mkexp(Pexp_fcall($1, $3)) }
  | FIDENT LPAREN exps RPAREN   { mkexp(Pexp_fun($1, $3)) }
;
opt_exp:
  | STAR          { None }
  | exp           { Some $1 }
;
exps:
  | /* empty */   { [] }
  | exps_ne       { $1 }
;
exps_ne:
  | exp            { [$1] }
  | exp COMMA exps_ne { $1::$3 }
;
a_exps:
  | /* empty */  { [] }
  | a_exps_ne    { $1 }
;
a_exps_ne:
  | a_exp                 { [$1] }
  | a_exp COMMA a_exps_ne { $1::$3 }
;
formals:
  | tyids               { ([],$1) }
  | tyids SEMI tyids { ($1,$3) }
;
actuals:
  | exps           { ([],$1) }
  | exps SEMI exps { (mk_ref_params $1 (Location.rhs_loc 1), $3) }
;
assn:
  | LPAREN assn RPAREN           { $2 }
  | EMPTY                        { a_prop_empty }
  | a_exp                        { Aprop_exp $1}
  | a_exp POINTSTO a_fields      { Aprop_node(component_of_string "Node",$1,$3) }
  | a_exp POINTSTO a_exp         { Aprop_node(component_of_string "Node",$1,[(Misc.list_link_tag, $3)]) }
  | IF a_exp THEN assn ELSE assn { Aprop_ifthenelse($2,$4,$6) }
  | assn STAR assn               { Aprop_star($1,$3) }
  | assn BARBAR assn             { Aprop_barbar($1,$3) }
  | IDENT COLON LBRACKET assn RBRACKET      { Aprop_box (component_of_string $1, $4) }
  | IDENT LPAREN a_exps RPAREN              { Aprop_indpred($1,[],$3,Location.symbol_loc()) }
  | IDENT LPAREN a_exps SEMI a_exps RPAREN  { Aprop_indpred($1,mk_indpred_params $3,$5,Location.symbol_loc()) }
;
a_exp:
  | LPAREN a_exp RPAREN          { $2 }
  | IDENT                        { mkexp(Pexp_ident($1)) }
  | QIDENT                       { mkexp(Pexp_ident($1)) }
  | NAT                          { mkexp(Pexp_num($1)) }
  | BOOL                         { mkexp(Pexp_bool($1)) }
  | FIDENT LPAREN a_exps RPAREN  { mkexp(Pexp_fun($1,$3)) }
  | UNARYOP exp                  { mkexp(Pexp_prefix($1, $2)) }
  | INFIXOP2 a_exp %prec UNARYOP { mkexp(Pexp_prefix($1, $2)) }
  | a_exp AMPERAMPER a_exp       { mkexp(Pexp_infix("&&",$1,$3)) }
  | a_exp INFIXOP1 a_exp         { mkexp(Pexp_infix($2,$1,$3)) }
  | a_exp INFIXOP2 a_exp         { mkexp(Pexp_infix($2,$1,$3)) }
  | a_exp INFIXOP3 a_exp         { mkexp(Pexp_infix($2,$1,$3)) }
;
a_fields:
  | UNDERSCORE   { [] }
  | a_fields_ne  { $1 }
;
a_fields_ne:
  | IDENT COLON a_exp                   { [(component_of_string ("."^$1),$3)] }
  | IDENT COLON a_exp COMMA a_fields_ne { (component_of_string ("."^$1),$3)::$5 }
;

/* MCPA takes user specifications & qualifiers into verification */
/* Qualifiers & Specification */

qualifiers:
    qualifier_list EOF
      { $1 }
			
qualifier_list:
    /* empty */
      { [] }
  | QUALIF qualifier_pattern_declaration qualifier_list
      { $2::$3 }

qualifier_pattern_declaration:
    IDENT LPAREN IDENT RPAREN LPAREN qual_ty_anno RPAREN COLON qualifier_pattern  
    { ($1, mkqpat($3, $6, $9)) }
  | IDENT LPAREN IDENT RPAREN COLON qualifier_pattern
    { ($1, mkqpat($3, [], $6))  }

qual_ty_anno:
    IDENT COLON IDENT
    { [($1, $3)] } 
  | IDENT COLON IDENT COMMA qual_ty_anno
    { ($1, $3)::$5 }

/* corresponding to predicate */
qualifier_pattern:
    BOOL                                    { if ($1) then mkpredpat Ppredpat_true else 
																								mkpredpat (Ppredpat_not (mkpredpat Ppredpat_true))
																						}                    
  |	qualifier_pattern AMPERAMPER qualifier_pattern { mkpredpat (Ppredpat_and($1, $3)) }
  | qualifier_pattern BARBAR qualifier_pattern  { mkpredpat (Ppredpat_or($1, $3)) }
		/** FIXME: the only option for UNARYOP is ! */
  | UNARYOP qualifier_pattern              { mkpredpat (Ppredpat_not($2)) }              
  | LPAREN qualifier_pattern RPAREN         { $2 }
  | qual_expr qual_rel qual_expr            
      { mkpredpat (Ppredpat_atom($1, $2, $3)) }
	| qual_expr IN qual_expr
	    { mkpredpat (Ppredpat_in ($1, $3)) }
	| REC IDENT LPAREN qual_expr RPAREN
	    { mkpredpat (Ppredpat_predrec ($2, $4)) }
	| qualifier_pattern IMPLIES qualifier_pattern
			{ mkpredpat (Ppredpat_or (mkpredpat (Ppredpat_not($1)), $3)) }

/* a set of relations */
qual_rel:
    qual_lit_rel                            { [$1] }
  | LBRACE qual_rel_list RBRACE             { $2 }
  | LBRACE STAR STAR RBRACE                 
    { [] }
  
qual_lit_rel:
    INFIXOP1               
    {   if $1 = "<=" then Pred_le
        else if $1 = "!=" then Pred_ne
				else if $1 = ">=" then Pred_ge
        else if $1 = "==" then Pred_eq
        else if $1 = "<" then Pred_lt
        else if $1 = ">" then Pred_gt
        else raise Parse_error
    }
  | EQUAL                                   { Pred_eq }

qual_rel_list:
    qual_lit_rel                            { [$1] }
  | qual_lit_rel COMMA qual_rel_list        { $1::$3 }

/* corresponding to pexpr */
qual_expr:
    qual_expr qual_op qual_expr_1           
    { mkpredpatexp (Ppredpatexp_binop($1, $2, $3)) }
	| qual_expr UNION qual_expr_1
		{ mkpredpatexp (Ppredpatexp_union($1, $3)) }
	| qual_expr CONCAT qual_expr_1
	  { mkpredpatexp (Ppredpatexp_concat($1, $3)) }
  | qual_expr_1                             { $1 }

qual_expr_1: 
    IDENT LPAREN qual_term_list RPAREN
    { mkpredpatexp (Ppredpatexp_funapp($1, $3)) } 
  | qual_term                               { $1 }

qual_term:
    LPAREN qual_expr RPAREN                 { $2 }
  | IDENT /* literal */
    { mkpredpatexp (Ppredpatexp_var([ $1 ])) } 
  | LBRACKET qual_litident_list RBRACKET
    { mkpredpatexp (Ppredpatexp_var($2)) }
  | TILDE IDENT /* var */
    { mkpredpatexp (Ppredpatexp_mvar($2)) } 
  | NAT
    { mkpredpatexp (Ppredpatexp_int([$1])) }
  | WILD /* wild int * */
    { mkpredpatexp (Ppredpatexp_any_int) }
  | LBRACKET qual_intlist RBRACKET
    { mkpredpatexp (Ppredpatexp_int($2)) }
  | qual_term DOT IDENT                
    { mkpredpatexp (Ppredpatexp_field($3, $1)) }
  | qual_term DOT NAT
    { mkpredpatexp (Ppredpatexp_proj($3, $1)) }

/* a set of integers */
qual_intlist:
    NAT                                     { [$1] }
  | NAT COMMA qual_intlist                  { $1::$3 }

/* a set of variabls */
qual_litident_list:
    IDENT COMMA qual_litident_list  { $1 :: $3 }
  | IDENT                           { [ $1 ] }

/* a set of function parameters */
qual_term_list:
    qual_term                               { [$1] }
  | qual_term qual_term_list                { $1::$2 }

/* a set of operators */
qual_op:
    qual_lit_op                                { [$1]  }
  | LBRACELESS qual_lit_op_list GREATERRBRACE  { $2 }
  | LBRACELESS STAR STAR GREATERRBRACE         
    { [] }

qual_lit_op:
    INFIXOP2
		{ match $1 with
			| "+" -> Predexp_plus
			| "-" -> Predexp_minus 
			| _ -> raise Parse_error}
  | STAR                                    { Predexp_times }  
  | INFIXOP3                                
    {  match $1 with 
			  "/" -> Predexp_div 
      | "*" -> Predexp_times
      | _ -> raise Parse_error }

qual_lit_op_list:
    qual_lit_op                             { [$1] }
  | qual_lit_op COMMA qual_lit_op_list      { $1::$3 }


%% (* trailer *)
