(** Generating equations from abstract syntax tree *)

open Cil_types
open Equation
(*  ********************************************************************** *)
(** {2 Useful Information for generating equations} *)
(*  ********************************************************************** *)

(*  ---------------------------------------------------------------------- *)
(** {3 Utility functions} *)
(*  ---------------------------------------------------------------------- *)


(** Extract an array of variables from variable declaration list *)
let convert (lvar:varinfo list) : Apron.Var.t array =
  Array.of_list
  	(List.map (fun var->Apron.Var.of_string var.vname) lvar)

(** Add to an environment a list of variables *)
let add_env (env:Apron.Environment.t) (lvar:varinfo list) :Apron.Environment.t =
  let (lint,lreal) =
    List.fold_left
      (begin fun (lint,lreal) var ->
      	match var.vtype with
      	| TInt(_,_)->((Apron.Var.of_string var.vname)::lint,lreal)
      	| TFloat(_,_)->(lint,(Apron.Var.of_string var.vname)::lreal)
      	| _->(lint,lreal)
			end) ([],[]) lvar
  in
  Apron.Environment.add env
    (Array.of_list lint)
    (Array.of_list lreal)

(*  ---------------------------------------------------------------------- *)
(** {3 Building preprocessed information} *)
(*  ---------------------------------------------------------------------- *)

(** Build a [Equation.procinfo] object from [Spl_syn.procedure]. *)
let make_procinfo (proc:Cil_types.kernel_function) : Equation.procinfo =
	match proc.fundec with
	| Definition(dec,_)->
	let fundec = Kernel_function.get_definition proc in
	let (pcode:block) = fundec.sbody in
	let (p1,p2) = Li_utils.get_stmt_location (List.nth pcode.bstmts 0) in
  let pstart = {pos1=p1;pos2=p2} in
  let (p1,p2) = Li_utils.get_stmt_location (List.nth pcode.bstmts ((List.length pcode.bstmts)-1)) in
  let pexit = {pos1=p1;pos2=p2} in

  let pinput = convert fundec.sformals in
  let plocal = convert fundec.slocals in

  let penv = Apron.Environment.make [||] [||] in
  let penv = add_env penv fundec.sformals in
  let penv = add_env penv fundec.slocals in

  {
  	Equation.kf = proc;
    Equation.pname = fundec.svar.vname;
    Equation.pstart = pstart;
    Equation.pexit = pexit;
    Equation.pinput = pinput;
    Equation.plocal = plocal;
    Equation.penv = penv;
  }
  | Declaration(spec,v,vlo,loc)->
  	let pinput = ref [||] in
  	let penv = ref (Apron.Environment.make [||] [||]) in
  	(match vlo with
  	| Some(vl)->
  		pinput := convert vl;
  		penv := add_env !penv vl;
  	| None->();
  	);
  	{
  		Equation.kf = Kernel_function.dummy ();
		  Equation.pname = v.vname;
		  Equation.pstart = Equation.vertex_dummy;
		  Equation.pexit = Equation.vertex_dummy;
		  Equation.pinput = !pinput;
		  Equation.plocal = [||];
		  Equation.penv = !penv;
  	}

(** Build a [Equation.info] object from [Spl_syn.program]. *)
let make_info (prog:Cil_types.file) : Equation.info =
  let procinfo = Hashhe.create 3 in
  Globals.Functions.iter(fun kf ->
  	match kf.fundec with
  	| Definition(dec,_)->
			let info = make_procinfo kf in
			Printf.printf "make procinfo:\n";
			Equation.print_procinfo Format.std_formatter info;
			Printf.printf "info.pname=%s\n" info.pname;
			Hashhe.add procinfo info.pname info
		| Declaration(spec,v,vlo,loc)->
			let info = make_procinfo kf in
			Printf.printf "make procinfo:\n";
			Equation.print_procinfo Format.std_formatter info;
			Printf.printf "info.pname=%s\n" info.pname;
			Hashhe.add procinfo info.pname info
	);

  let callret = DHashhe.create 3 in
  Globals.Functions.iter(fun kf ->
  	match kf.fundec with
  	| Definition(dec,_)->
			let fundec = Kernel_function.get_definition kf in
			let (pcode:block) = fundec.sbody in
			let (p1,p2) = Li_utils.get_stmt_location (List.nth pcode.bstmts 0) in
			let bpoint = {pos1=p1;pos2=p2} in
			List.iter(fun stmt->
				match stmt.skind with
				| Instr(ins)->
					(match ins with
					| Call(_,_,_,(p3,p4))->
						DHashhe.add callret bpoint {pos1=p3;pos2=p4};
					| _->();
					);
				| _->();
			)pcode.bstmts;
		| Declaration(spec,v,vlo,loc)->
			let (p1,p2) = loc in
			let bpoint = {pos1=p1;pos2=p2} in
			DHashhe.add callret bpoint bpoint;
	);
  
  let pointenv = Hashhe.create 3 in
  
  Globals.Functions.iter(fun kf ->
  	match kf.fundec with
  	| Definition(dec,_)->
			let fundec = Kernel_function.get_definition kf in
			let (pcode:block) = fundec.sbody in
			let pinfo = Hashhe.find procinfo fundec.svar.vname in
		  let env = pinfo.Equation.penv in
		  Hashhe.add pointenv Equation.vertex_dummy env;
		  let (p1,p2) = Li_utils.get_stmt_location (List.nth pcode.bstmts 0) in
		  let bpoint = {pos1=p1;pos2=p2} in
		  List.iter(fun stmt->
		  	let (p1,p2) = Li_utils.get_stmt_location stmt in
		  	let p = {pos1=p1;pos2=p2} in
		  	if not (Hashhe.mem pointenv bpoint) then
					Hashhe.add pointenv bpoint env;
				if not (Hashhe.mem pointenv p) then
					Hashhe.add pointenv p env;
		  )pcode.bstmts;
    | Declaration(spec,v,vlo,loc)->
    	let (p1,p2) = loc in
    	let bpoint = {pos1=p1;pos2=p2} in
    	let pinfo = Hashhe.find procinfo v.vname in
		  let env = pinfo.Equation.penv in
		  if not (Hashhe.mem pointenv bpoint) then
				Hashhe.add pointenv bpoint env;
	);
  {
    Equation.procinfo = procinfo;
    Equation.callret = callret;
    Equation.pointenv = pointenv;
    Equation.counter = 0;
  }
  
(*  ********************************************************************** *)
(** {2 Translating expressions} *)
(*  ********************************************************************** *)

(** Numerical expressions *)
type iexpr = Apron.Texpr1.expr

(** Numerical constraint type *)
type constyp = EQ | NEQ | GT | GEQ | LEQ | LT

(** Numerical constraint *)
type cons = iexpr * constyp * iexpr

(** Boolean expression *)
type bexpr =
  | TRUE
  | FALSE
  | BRANDOM
  | CONS of cons
  | AND  of bexpr*bexpr
  | OR   of bexpr*bexpr
  | NOT  of bexpr (** *)
	
let negate_texpr (texpr:Apron.Texpr1.t) : Apron.Texpr1.t
  =
  let expr = Apron.Texpr1.to_expr texpr in
  let nexpr = match expr with
    | Apron.Texpr1.Unop(Apron.Texpr1.Neg,e,typ,round) ->
	e
    | _ ->
	Apron.Texpr1.Unop(
	  Apron.Texpr1.Neg, expr,
	  Apron.Texpr1.Real, Apron.Texpr1.Rnd
	)
  in
  let env = Apron.Texpr1.get_env texpr in
  Apron.Texpr1.of_expr env nexpr

let negate_tcons (tcons:Apron.Tcons1.t) : Apron.Tcons1.t
  =
  let texpr = Apron.Tcons1.get_texpr1 tcons in
  let (ntyp,ntexpr) = match Apron.Tcons1.get_typ tcons with
    | Apron.Tcons1.EQ -> (Apron.Tcons1.DISEQ,texpr)
    | Apron.Tcons1.DISEQ -> (Apron.Tcons1.EQ,texpr)
    | Apron.Tcons1.SUPEQ -> (Apron.Tcons1.SUP, negate_texpr texpr)
    | Apron.Tcons1.SUP -> (Apron.Tcons1.SUPEQ, negate_texpr texpr)
    | Apron.Tcons1.EQMOD _ -> failwith "EQMOD not supported now"
  in
  Apron.Tcons1.make ntexpr ntyp

let tcons_of_cons env (cons:cons) : Apron.Tcons1.t
  =
  let (expr1,typ,expr2) = cons in
  let (typ,expr) = match typ with
  | EQ ->
      (Apron.Tcons1.EQ,
       Apron.Texpr1.Binop(Apron.Texpr1.Sub,expr1,expr2,Apron.Texpr1.Real, Apron.Texpr1.Rnd))
  | NEQ ->
      (Apron.Tcons1.DISEQ,
       Apron.Texpr1.Binop(Apron.Texpr1.Sub,expr1,expr2,Apron.Texpr1.Real, Apron.Texpr1.Rnd))
  | GEQ ->
      (Apron.Tcons1.SUPEQ,
       Apron.Texpr1.Binop(Apron.Texpr1.Sub,expr1,expr2,Apron.Texpr1.Real, Apron.Texpr1.Rnd))
  | GT ->
      (Apron.Tcons1.SUP,
       Apron.Texpr1.Binop(Apron.Texpr1.Sub,expr1,expr2,Apron.Texpr1.Real, Apron.Texpr1.Rnd))
  | LEQ ->
      (Apron.Tcons1.SUPEQ,
       Apron.Texpr1.Binop(Apron.Texpr1.Sub,expr2,expr1,Apron.Texpr1.Real, Apron.Texpr1.Rnd))
  | LT ->
      (Apron.Tcons1.SUP,
       Apron.Texpr1.Binop(Apron.Texpr1.Sub,expr2,expr1,Apron.Texpr1.Real, Apron.Texpr1.Rnd))
  in
  Apron.Tcons1.make (Apron.Texpr1.of_expr env expr) typ

let rec push_not (bexpr:bexpr) : bexpr
    =
  match bexpr with
  | TRUE | FALSE | BRANDOM | CONS _ -> 
      bexpr
  | NOT(e) ->
      begin match e with
      | TRUE -> FALSE
      | FALSE -> TRUE
      | BRANDOM -> BRANDOM
      | CONS(cons) -> e 
      | AND(e1,e2) -> OR(push_not (NOT e1), push_not (NOT e2))
      | OR(e1,e2) -> AND(push_not (NOT e1), push_not (NOT e2))
      | NOT(e) -> push_not e
      end
  | AND(e1,e2) -> AND(push_not e1, push_not e2)
  | OR(e1,e2) -> OR(push_not e1, push_not e2)

let boolexpr0_of_bexpr env (bexpr:bexpr) :Apron.Tcons1.t array Boolexpr.t =
  let cand t1 t2 = Boolexpr.make_conjunction (Array.append t1 t2) in
  let rec translate bexpr = 
    match bexpr with
    | TRUE | BRANDOM -> Boolexpr.make_cst true
    | FALSE -> Boolexpr.make_cst false
    | CONS(cons) ->
    	Boolexpr.print (fun e->Apron.Texpr1.print_expr e;) Format.std_formatter;
    	Format.print_flush ();Printf.printf "\n";
			let tcons = tcons_of_cons env cons in
			Boolexpr.make_conjunction [|tcons|]
		| AND(e1,e2) ->
			Boolexpr.make_and ~cand	(translate e1) (translate e2)
		| OR(e1,e2) ->
			Boolexpr.make_or (translate e1) (translate e2)
		| NOT(e) ->
			begin match e with
			| FALSE | BRANDOM -> Boolexpr.make_cst true
			| TRUE -> Boolexpr.make_cst false
			| CONS(cons) ->
				let tcons = tcons_of_cons env cons in
				let tcons = negate_tcons tcons in
				Boolexpr.make_conjunction [|tcons|]
			| AND(e1,e2) ->
				Boolexpr.make_or (translate (NOT e1)) (translate (NOT e2))
			| OR(e1,e2) ->
				Boolexpr.make_and ~cand (translate (NOT e1)) (translate (NOT e2))
			| NOT(e) -> translate e
			end
  in
  translate bexpr

let boolexpr_of_bexpr env (bexpr:bexpr) : Apron.Tcons1.earray Boolexpr.t =
  let bexpr0 = boolexpr0_of_bexpr env bexpr in
  Boolexpr.map
    (fun tcons ->
      assert(tcons<>[||]);
      let res = Apron.Tcons1.array_make env (Array.length tcons) in
      Array.iteri	(fun i cons -> Apron.Tcons1.array_set res i cons)	tcons;
      res
    )
    bexpr0

let rec force_exp_to_texp (exp:Cil_types.exp) :Apron.Texpr1.expr =
	match exp.enode with
	| BinOp(op,e1,e2,ty)->
		(match op with
		| PlusA->
			let te1 = force_exp_to_texp e1 in
			let te2 = force_exp_to_texp e2 in
			Apron.Texpr1.Binop(Apron.Texpr1.Add,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| MinusA->
			let te1 = force_exp_to_texp e1 in
			let te2 = force_exp_to_texp e2 in
			Apron.Texpr1.Binop(Apron.Texpr1.Sub,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| Div->
			let te1 = force_exp_to_texp e1 in
			let te2 = force_exp_to_texp e2 in
			Apron.Texpr1.Binop(Apron.Texpr1.Div,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| Mult->
			let te1 = force_exp_to_texp e1 in
			let te2 = force_exp_to_texp e2 in
			Apron.Texpr1.Binop(Apron.Texpr1.Mul,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| Mod->
			let te1 = force_exp_to_texp e1 in
			let te2 = force_exp_to_texp e2 in
			Apron.Texpr1.Binop(Apron.Texpr1.Mod,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		|_->
			Printf.printf "unknownBinOp\n";
			Li_utils.print_exp_type exp;
			Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";
			Apron.Texpr1.Var(Apron.Var.of_string "unknownBinOp");
		)
	| UnOp(op,e,ty)->
		(match op with
		| Neg->
			let te = force_exp_to_texp e in
			Apron.Texpr1.Unop(Apron.Texpr1.Neg,te,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| _->
			Printf.printf "unknownUnOp\n";
			Li_utils.print_exp_type exp;
			Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";
			Apron.Texpr1.Var(Apron.Var.of_string "unknownUnOp");
		)
	| Const(cons)->
		(match cons with
		| CInt64(i,kind,_)->
			Apron.Texpr1.Cst(Apron.Coeff.s_of_int (My_bigint.to_int i));
		| CReal(f,_,_)->
			Apron.Texpr1.Cst(Apron.Coeff.s_of_float f);
		| _->
			Printf.printf "unknownConst\n";
			Li_utils.print_exp_type exp;
			Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";
			Apron.Texpr1.Var(Apron.Var.of_string "unknownConst");
		)
	| Lval((host,offset))->
		(match host with
		| Var(v)->
			Apron.Texpr1.Var(Apron.Var.of_string v.vname);
		| Mem(e)->
			force_exp_to_texp e;
		);
	|_->
		Printf.printf "unknownEnode\n";
		Li_utils.print_exp_type exp;
		Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";
		Apron.Texpr1.Var(Apron.Var.of_string "unknownEnode")
	  
let rec force_exp2bexp (exp:Cil_types.exp) : bexpr =
	match exp.enode with
	| BinOp(op,e1,e2,tp)->
		let te1 = force_exp_to_texp e1 in
		let te2 = force_exp_to_texp e2 in
		(match op with
		| Lt->
			CONS(te1,LT,te2)
		| Gt->
			CONS(te1,GT,te2)
		| Le->
			CONS(te1,LEQ,te2)
		| Ge->
			CONS(te1,GEQ,te2)
		| Eq->
			CONS(te1,EQ,te2)
		| Ne->
			CONS(te1,NEQ,te2)
		| _->assert false
		);
	| _->assert false
	
(*  ********************************************************************** *)
(** {2 Forward equations} *)
(*  ********************************************************************** *)
	
module Forward = struct
  let make (prog:Cil_types.file) (fmt:Format.formatter): Equation.graph =
  	let info = make_info prog in
  	Printf.printf "make info:\n";
  	Equation.print_info fmt info;
  	Printf.printf "\n";
    let graph = Equation.create 3 info in
		Format.fprintf fmt "print graph just new 1\n";
		Equation.print_graph fmt graph;
		Format.fprintf fmt "print graph just new 2\n";
		Equation.print_point fmt Equation.vertex_dummy;
		
    let rec iter_block (procinfo:Equation.procinfo) (block:block) : unit =
      let env = procinfo.Equation.penv in
      let (p1,p2) = Li_utils.get_block_spoint block in
      let bpoint = {pos1=p1;pos2=p2} in
      if bpoint != Equation.vertex_dummy then
      ignore begin
      Printf.printf "bpoint\n";
      Equation.print_point fmt bpoint;      
      Cil.d_block fmt block;Format.print_flush ();Printf.printf "\n";
      List.fold_left(fun bpoint stmt->
      	Li_utils.print_stmtkind stmt.skind;
      	let (p1,p2) = Li_utils.get_stmt_location stmt in
      	let spoint = {pos1=p1;pos2=p2} in
				if spoint != Equation.vertex_dummy then
      	(Printf.printf "spoint\n";
				Equation.print_point fmt spoint;
      	match stmt.skind with
      	| Instr(instr)->
      		Printf.printf "c2equation Forward make Instr\n";
      		(match instr with
      		| Set(lval,e,_)->
      			Printf.printf "meet Set\n";
      			Cil.d_stmt Format.std_formatter stmt;
      			Printf.printf "\n";
      			let (host,offset) = lval in
      			(match host with
      			| Var(v)->
      				let var = Apron.Var.of_string v.vname in
		   				let (texpr:Apron.Texpr1.t) =
		   					let texp = (force_exp_to_texp e) in
		   					Apron.Texpr1.print_expr fmt texp;
		   					Printf.printf "\n";
								Apron.Texpr1.of_expr env texp
							in
							let transfer = Equation.Tassign(var,texpr) in
							Equation.print_transfer fmt transfer;
							Printf.printf "\n";
							
							Equation.add_equation graph [|spoint|] transfer spoint;
						| _->
      				let transfer = Equation.Condition(Boolexpr.make_cst true) in
							Equation.add_equation graph [|bpoint|] transfer spoint;
						);
      		| _->
      			let transfer = Equation.Condition(Boolexpr.make_cst true) in
						Equation.add_equation graph [|bpoint|] transfer spoint;
      		);
      	| Loop(_,b,_,_,_)->
      		iter_block procinfo b;
      	| Block(b)->
      		iter_block procinfo b;
      	| UnspecifiedSequence(seq)->
					iter_block procinfo (Cil.block_from_unspecified_sequence seq);
      	| If(exp,b1,b2,l)->
      		Printf.printf "c2equation Forward make If\n";
      		let bexpr = force_exp2bexp exp in
      		Apron.Environment.print fmt env;
      		let cond = boolexpr_of_bexpr env bexpr in
					let condnot = boolexpr_of_bexpr env (NOT bexpr) in
					let condtransfer = Equation.Condition(cond) in
					let condnottransfer = Equation.Condition(condnot) in
					let (p1,p2) = Li_utils.get_block_spoint b1 in
					Equation.add_equation graph
						[|bpoint|] condtransfer {pos1=p1;pos2=p2};
					let (p1,p2) = Li_utils.get_block_epoint b1 in
					Equation.add_equation graph
						[|{pos1=p1;pos2=p2}|] (Equation.Condition(Boolexpr.make_cst true)) spoint;
						
					let (p1,p2) = Li_utils.get_block_spoint b2 in
					Equation.add_equation graph
						[|bpoint|] condnottransfer {pos1=p1;pos2=p2};
					let (p1,p2) = Li_utils.get_block_epoint b1 in
					Equation.add_equation graph
						[|{pos1=p1;pos2=p2}|] (Equation.Condition(Boolexpr.make_cst true)) spoint;
							
					iter_block procinfo b1;
					iter_block procinfo b2
      	| _->
      		let transfer = Equation.Condition(Boolexpr.make_cst true) in
					Equation.add_equation graph [|bpoint|] transfer spoint;
				);
				bpoint
     	)bpoint block.bstmts;
      end
      (*ignore begin
			List.fold_left
				(begin fun point instr ->
					begin match instr.instruction with
					| SKIP ->
						let transfer = Equation.Condition(Boolexpr.TRUE) in
						Equation.add_equation graph [|point|] transfer instr.ipoint;
					| HALT
					| FAIL ->
						(* We still put a dummy equation *)
						let transfer = Equation.Condition(Boolexpr.DISJ([])) in
						Equation.add_equation graph [|point|] transfer instr.ipoint;
						()
					| ASSUME(bexpr) ->
						let cond = boolexpr_of_bexpr env bexpr in
						let transfer = Equation.Condition(cond) in
						Equation.add_equation graph [|point|] transfer instr.ipoint;
					| ASSIGN(var,iexpr) ->
						let (texpr:Apron.Texpr1.t) =
							Apron.Texpr1.of_expr env iexpr
						in
						let transfer = Equation.Tassign(var,texpr) in
						Equation.add_equation graph [|point|] transfer instr.ipoint;
					| CALL(pout,name,pin) ->
						let callee = Hashhe.find info.Equation.procinfo name in
						let pin = Array.of_list pin in
						let pout = Array.of_list pout in
						let calltransfer = Equation.Call(procinfo,callee,pin,pout) in
						let rettransfer = Equation.Return(procinfo,callee, pin, pout) in
						Equation.add_equation graph
							[|point|] calltransfer callee.Equation.pstart;
						Equation.add_equation graph
							[|point; callee.Equation.pexit|] rettransfer instr.ipoint;
					| IF(bexpr,block) ->
						let cond = boolexpr_of_bexpr env bexpr in
						let condnot = boolexpr_of_bexpr env (NOT bexpr) in
						let condtransfer = Equation.Condition(cond) in
						let condnottransfer = Equation.Condition(condnot) in
						Equation.add_equation graph
							[|point|] condtransfer block.bpoint;
						Equation.add_equation graph
							[|exit_of_block block|] (Equation.Condition(Boolexpr.make_cst true)) instr.ipoint;
						Equation.add_equation graph
							[|point|]  condnottransfer instr.ipoint;
						iter_block procinfo block
					| IFELSE(bexpr,block1,block2) ->
						let cond = boolexpr_of_bexpr env bexpr in
						let condnot = boolexpr_of_bexpr env (NOT bexpr) in
						let condtransfer = Equation.Condition(cond) in
						let condnottransfer = Equation.Condition(condnot) in
						Equation.add_equation graph
							[|point|]  condtransfer block1.bpoint;
						Equation.add_equation graph
							[|exit_of_block block1|] (Equation.Condition(Boolexpr.make_cst true)) instr.ipoint;
						Equation.add_equation graph
							[|point|] condnottransfer block2.bpoint;
						Equation.add_equation graph
							[|exit_of_block block2|] (Equation.Condition(Boolexpr.make_cst true)) instr.ipoint;
						iter_block procinfo block1;
						iter_block procinfo block2
					| LOOP(bexpr,block) ->
						let cond = boolexpr_of_bexpr env bexpr in
						let condnot = boolexpr_of_bexpr env (NOT bexpr) in
						let condtransfer = Equation.Condition(cond) in
						let condnottransfer = Equation.Condition(condnot) in
						Equation.add_equation graph
							[|point|] condtransfer block.bpoint;
						Equation.add_equation graph
							[|exit_of_block block|] (Equation.Condition(Boolexpr.make_cst true)) point;
						Equation.add_equation graph
							[|point|] condnottransfer instr.ipoint;
						iter_block procinfo block
					end;
					instr.ipoint
				end)
				block.bpoint
				block.instrs
			end*)
   	in

		Globals.Functions.iter(fun kf ->
			match kf.fundec with
			| Definition(_,_)->
				let fundec = Kernel_function.get_definition kf in
				let procinfo = Hashhe.find info.Equation.procinfo fundec.svar.vname in
				Printf.printf "in make graph procinfo Definition\n";
				Equation.print_procinfo fmt procinfo;
				iter_block procinfo fundec.sbody;
			| Declaration(spec,v,vlo,loc)->
				let procinfo = Hashhe.find info.Equation.procinfo v.vname in
				Printf.printf "in make graph procinfo Declaration\n";
				Equation.print_procinfo fmt procinfo;
		);

    graph

end

(*  ********************************************************************** *)
(** {2 Backward equations} *)
(*  ********************************************************************** *)

module Backward = struct
  let make (prog:Cil_types.file) : Equation.graph =
  	let info = make_info prog in
    let graph = Equation.create 3 info in

		let rec iter_block (procinfo:Equation.procinfo) (block:block) : unit =
      let env = procinfo.Equation.penv in
      let bpoint = Li_utils.get_stmt_location (List.nth block.bstmts 0) in
      ();
      (*ignore begin
			List.fold_left
			(begin fun point instr ->
			  begin match instr.instruction with
			  | SKIP ->
					let transfer = Equation.Condition(Boolexpr.make_cst true) in
					Equation.add_equation graph [|instr.ipoint|] transfer point;
			  | HALT
			  | FAIL ->
					(* We still put a dummy equation *)
					let transfer = Equation.Condition(Boolexpr.make_cst false) in
					Equation.add_equation graph [|instr.ipoint|] transfer point;
			  | ASSUME(bexpr) ->
					let cond = boolexpr_of_bexpr env bexpr in
					let transfer = Equation.Condition(cond) in
					Equation.add_equation graph [|instr.ipoint|] transfer point;
			  | ASSIGN(var,iexpr) ->
					let (texpr:Apron.Texpr1.t) =
						Apron.Texpr1.of_expr env iexpr
					in
					let transfer = Equation.Tassign(var,texpr) in
					Equation.add_equation graph [|instr.ipoint|] transfer point;
			  | CALL(pout,name,pin) ->
					let callee = Hashhe.find info.Equation.procinfo name in
					let pin = Array.of_list pin in
					let pout = Array.of_list pout in
					let calltransfer = Equation.Call(procinfo,callee,pin,pout) in
					let rettransfer = Equation.Return(procinfo,callee,pin,pout) in
					Equation.add_equation graph
						[|callee.Equation.pstart|] calltransfer point;
					Equation.add_equation graph
						[|instr.ipoint|] rettransfer callee.Equation.pexit;
			  | IF(bexpr,block) ->
					let cond = boolexpr_of_bexpr env bexpr in
					let condnot = boolexpr_of_bexpr env (NOT bexpr) in
					let condtransfer = Equation.Condition(cond) in
					let condnottransfer = Equation.Condition(condnot) in
					Equation.add_equation graph
						[|block.bpoint|] condtransfer point;
					Equation.add_equation graph
						[|instr.ipoint|] (Equation.Condition(Boolexpr.make_cst true)) (exit_of_block block);
					Equation.add_equation graph
						[|instr.ipoint|] condnottransfer point;
					iter_block procinfo block
			  | IFELSE(bexpr,block1,block2) ->
					let cond = boolexpr_of_bexpr env bexpr in
					let condnot = boolexpr_of_bexpr env (NOT bexpr) in
					let condtransfer = Equation.Condition(cond) in
					let condnottransfer = Equation.Condition(condnot) in
					Equation.add_equation graph
						[|block1.bpoint|] condtransfer point;
					Equation.add_equation graph
						[|instr.ipoint|] (Equation.Condition(Boolexpr.make_cst true)) (exit_of_block block1);
					Equation.add_equation graph
						[|block2.bpoint|] condnottransfer point;
					Equation.add_equation graph
						[|instr.ipoint|] (Equation.Condition(Boolexpr.make_cst true)) (exit_of_block block2);
					iter_block procinfo block1;
					iter_block procinfo block2
			  | LOOP(bexpr,block) ->
					let cond = boolexpr_of_bexpr env bexpr in
					let condnot = boolexpr_of_bexpr env (NOT bexpr) in
					let condtransfer = Equation.Condition(cond) in
					let condnottransfer = Equation.Condition(condnot) in
					Equation.add_equation graph
						[|block.bpoint|] condtransfer point;
					Equation.add_equation graph
						[|point|] (Equation.Condition(Boolexpr.make_cst true)) (exit_of_block block);
					Equation.add_equation graph
						[|instr.ipoint|] condnottransfer point;
					iter_block procinfo block
			  end;
			  instr.ipoint
			end)
			block.bpoint
			block.instrs
      end
      *)
    in

    (*Globals.Functions.iter(fun kf ->
			let fundec = Kernel_function.get_definition kf in
			let procinfo = Hashhe.find info.Equation.procinfo fundec.svar.vname in
			iter_block procinfo fundec.sbody;
		);
		List.iter(fun procedure ->
			let procinfo = Hashhe.find info.Equation.procinfo procedure.pname in
			iter_block procinfo procedure.pcode;
    )prog.procedures;*)

    graph

end
