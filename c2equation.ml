(** Generating equations from abstract syntax tree *)

open Cil_types
open Equation
  
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

	
let negate_tcons (tcons:Apron.Tcons1.t) : Apron.Tcons1.t
  =
  let texpr = Apron.Tcons1.get_texpr1 tcons in
  let (ntyp,ntexpr) = match Apron.Tcons1.get_typ tcons with
    | Apron.Tcons1.EQ -> (Apron.Tcons1.DISEQ,texpr)
    | Apron.Tcons1.DISEQ -> (Apron.Tcons1.EQ,texpr)
    | Apron.Tcons1.SUPEQ -> (Apron.Tcons1.SUP, Translate.negate_texpr texpr)
    | Apron.Tcons1.SUP -> (Apron.Tcons1.SUPEQ, Translate.negate_texpr texpr)
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


let rec force_exp2bexp (exp:Cil_types.exp) : bexpr =
	begin match exp.enode with
	| BinOp(op,e1,e2,tp)->
		let te1 = Translate.force_exp_to_texp e1 in
		let te2 = Translate.force_exp_to_texp e2 in
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
	| UnOp(op,e,_)->
		(match op with
		| LNot->
			NOT(force_exp2bexp e);
		| Neg->assert false;(*-*)
		| BNot->assert false;
		)
	| _->assert false
	end

(** Extract an array of variables from variable declaration list *)
let convert (lvar:varinfo list) : Apron.Var.t array =
  Array.of_list
  	(List.map (fun var->Apron.Var.of_string var.vname) lvar)


(*  ---------------------------------------------------------------------- *)
(** {3 Building preprocessed information} *)
(*  ---------------------------------------------------------------------- *)

(** Build a [Equation.procinfo] object from [Spl_syn.procedure]. *)
let make_procinfo (proc:Cil_types.kernel_function) : Equation.procinfo =
	let name = Kernel_function.get_name proc in
	match proc.fundec with
	| Definition(dec,loc)->
		let fundec = Kernel_function.get_definition proc in
		let (pcode:block) = fundec.sbody in
		let pstart = {fname=pcode.kf_name;sid = pcode.bid} in
		let pexit = ref Equation.vertex_dummy in
		if (List.length pcode.bstmts)==0 then
		(pexit := pstart;)
		else
		(
		let last_stmt = List.nth pcode.bstmts ((List.length pcode.bstmts)-1) in
		pexit := {fname=name;sid = last_stmt.Cil_types.sid};
		);
		let pinput = convert fundec.sformals in
		let plocal = convert fundec.slocals in

		let penv = Apron.Environment.make [||] [||] in
		let penv = Apron.Environment.add penv [|(Apron.Var.of_string "unknownEnode");Apron.Var.of_string "unknownConst";Apron.Var.of_string "unknownUnOp";Apron.Var.of_string "unknownBinOp"|] [||] in
		let avar2cvar = Hashhe.create 3 in
		let penv = Translate.add_env penv fundec.sformals avar2cvar in
		let penv = Translate.add_env penv fundec.slocals avar2cvar in
		(*convert and add lval to env*)
		let lvals = ref [] in
		let strfmt = Format.str_formatter in
		let fmt = Format.std_formatter in
		
		let add_lval lv =
			let (host,offset) = lv in
			begin match host with
			| Var(v)->
				begin match v.vtype with
				| TArray(_)->();
				| _->
					Cil.d_lval strfmt lv;
					let name = Format.flush_str_formatter () in
					if (List.for_all (fun v->(String.compare (Apron.Var.to_string v) name)!=0) !lvals)==true then
					begin lvals := (Apron.Var.of_string name)::(!lvals);end;
				end;
			| Mem(m)->();
			end;
		in
		let rec add_env_exp e =
			begin match e.enode with
			| Const(cons)->
				Cil.d_const strfmt cons;
				let name = Format.flush_str_formatter () in
				if (List.for_all (fun v->(String.compare (Apron.Var.to_string v) name)!=0) !lvals)==true then
				begin lvals := (Apron.Var.of_string name)::(!lvals);end;
			| SizeOfStr(_)|AlignOf(_)|SizeOf(_)->();
			| Lval(l)|AddrOf(l)|StartOf(l)->add_lval l;
			| SizeOfE(e1)|AlignOfE(e1)|UnOp(_,e1,_)|CastE(_,e1)|Info(e1,_)->add_env_exp e1;
			| BinOp(_,e1,e2,_)->add_env_exp e1;add_env_exp e2;
			end;
		in
		let rec add_env_block b =
			List.iter(fun s->
				begin match s.skind with
				| Instr (ins)->
					begin match ins with
					| Set(lv,e,_)->
						add_lval lv;
						add_env_exp e;
					| Call(lvo,e,el,_)->
						begin match lvo with
						| Some(lv)->
							add_lval lv;
						| None->();
						end;
						add_env_exp e;
						List.iter(fun e1->
							add_env_exp e1;
						)el;
					| Asm _|Skip _|Code_annot _->();
					end;
				| Cil_types.Return(eo,_)->
					begin match eo with
					| Some(e1)->
						add_env_exp e1;
					| None->();
					end;
				| Goto _|Break _|Continue _->();
				| If(e,b1,b2,_)->
					add_env_exp e;
					add_env_block b1;
					add_env_block b2;
				| Switch(e,b1,_,_)->
					add_env_exp e;
					add_env_block b1;
				| Loop(_,b1,_,_,_)|Block(b1)->
					add_env_block b1;
				| UnspecifiedSequence(seq)->
					let b1 = Cil.block_from_unspecified_sequence seq in
					add_env_block b1;
				| TryFinally(b1,b2,_)|TryExcept(b1,_,b2,_)->
					add_env_block b1;
					add_env_block b2;
				end
			)b.bstmts;
		in
		
		add_env_block fundec.sbody;
		let penv = Translate.add_vars penv !lvals avar2cvar in
		Printf.printf "env of %s\n" name;Apron.Environment.print fmt penv;Format.print_flush ();Printf.printf "\n";
		{
			Equation.kf = proc;
		  Equation.pname = Kernel_function.get_name proc;
		  Equation.pstart = pstart;
		  Equation.pexit = !pexit;
		  Equation.pinput = pinput;
		  Equation.plocal = plocal;
		  Equation.penv = penv;
		  Equation.avar2cvar = avar2cvar;
 	 }
  | Declaration(spec,v,vlo,loc)->
  	let pinput = ref [||] in
  	let penv = ref (Apron.Environment.make [||] [||]) in
		let avar2cvar = Hashhe.create 3 in
  	(match vlo with
  	| Some(vl)->
  		pinput := convert vl;
  		penv := Translate.add_env !penv vl avar2cvar;
  	| None->();
  	);
  	{
  		Equation.kf = Kernel_function.dummy ();
		  Equation.pname = Kernel_function.get_name proc;
		  Equation.pstart = {fname=name;sid = -1};
		  Equation.pexit = {fname=name;sid = -1};
		  Equation.pinput = !pinput;
		  Equation.plocal = [||];
		  Equation.penv = !penv;
		  Equation.avar2cvar = avar2cvar;
  	}

(** Build a [Equation.info] object from [Spl_syn.program]. *)
let make_info (prog:Cil_types.file) : Equation.info =
  let procinfo = Hashhe.create 3 in
  let fmt = Format.std_formatter in
  Globals.Functions.iter(fun kf ->
  	match kf.fundec with
  	| Definition(dec,_)->
			let info = make_procinfo kf in
			Hashhe.add procinfo info.pname info
		| Declaration(spec,v,vlo,loc)->
			let info = make_procinfo kf in
			Hashhe.add procinfo info.pname info
	);

  let callret = DHashhe.create 3 in
  Globals.Functions.iter(fun kf ->
  	let name = Kernel_function.get_name kf in
  	match kf.fundec with
  	| Definition(dec,loc)->
			let fundec = Kernel_function.get_definition kf in
			let (pcode:block) = fundec.sbody in
			
			let rec add_callret b =
				if(List.length b.bstmts)>0 then begin
					let first_stmt = List.nth b.bstmts 0 in
					let bpoint = {fname=name;sid=first_stmt.Cil_types.sid} in
					List.iter(fun s->
						match s.skind with
						| Instr(ins)->
							(match ins with
							| Call(_,_,_,(p3,p4))->
								DHashhe.add callret bpoint {fname=name;sid=s.Cil_types.sid};
							| _->();
							)
						| If(e,b1,b2,_)->
							add_callret b1;
							add_callret b2;
						| Switch(_,b1,_,_)->
							add_callret b1;
						| Block(b1)->add_callret b1
						| UnspecifiedSequence(seq)->
							let block = Cil.block_from_unspecified_sequence seq in
							add_callret block
						| Loop(_,b1,_,_,_)->add_callret b1
						| TryFinally(b1,b2,_)|TryExcept(b1,_,b2,_)|If(_,b1,b2,_)->
							add_callret b1;add_callret b2
						| _->()
					)b.bstmts;
				end
			in
			
			add_callret pcode
		| Declaration(spec,v,vlo,loc)->()
	);
  
  let pointenv = Hashhe.create 3 in
  
  Globals.Functions.iter(fun kf ->
  	let name = Kernel_function.get_name kf in
  	match kf.fundec with
  	| Definition(dec,loc)->
			let fundec = Kernel_function.get_definition kf in
			let (pcode:block) = fundec.sbody in
			let pinfo = Hashhe.find procinfo (Kernel_function.get_name kf) in
		  let env = pinfo.Equation.penv in
		  
  		let fpoint = {fname=pcode.kf_name;sid = pcode.bid} in
		  if not (Hashhe.mem pointenv fpoint) then
				Hashhe.add pointenv fpoint env;
		  
		  let rec add_env b =
		  	if (List.length b.bstmts)>0 then begin
					let first_stmt = List.nth b.bstmts 0 in
					let bpoint = {fname=b.kf_name;sid=b.bid} in
					if not (Hashhe.mem pointenv bpoint) then
					(Hashhe.add pointenv bpoint env;);
					
					List.iter(fun stmt->
						let p = {fname=name;sid=stmt.Cil_types.sid} in
						(*if the location is dummy, we generate a new vertex id 
						and add to pointenv and also record the new id*)
						if not (Hashhe.mem pointenv p) then
						(Hashhe.add pointenv p env;);
					
						match stmt.skind with
						| If(e,b1,b2,_)->
							add_env b1;
							add_env b2;
						| Switch(_,b1,_,_)->
							add_env b1;
						| Block(b1)->
							add_env b1;
						| UnspecifiedSequence(seq)->
							let block = Cil.block_from_unspecified_sequence seq in
							add_env block;
						| Loop(_,b1,_,_,_)->
							add_env b1;
						| TryFinally(b1,b2,_)|TryExcept(b1,_,b2,_)|If(_,b1,b2,_)->
							add_env b1;
							add_env b2;
						| _->();
						
					)b.bstmts
				end
			in
		  add_env pcode;
    | Declaration(spec,v,vlo,loc)->()
	);
  {
    Equation.procinfo = procinfo;
    Equation.callret = callret;
    Equation.pointenv = pointenv;
    Equation.counter = 0;
  }

(*  ********************************************************************** *)
(** {2 Forward equations} *)
(*  ********************************************************************** *)
	
module Forward = struct
  let make (info:Equation.info) arrayvars (fmt:Format.formatter) ipl wp_compute: Equation.graph =
  	
    let graph = Equation.create 3 info in
		
    let rec iter_block (name:string) (procinfo:Equation.procinfo) (block:block) : unit =
    	if (List.length block.bstmts)>0 then(
      let env = procinfo.Equation.penv in
      let first_stmt = List.hd block.bstmts in
      let bpoint = {fname=block.kf_name;sid=block.bid} in
      
      if (Equation.compare_point bpoint Equation.vertex_dummy)!=0 then(
      List.fold_left(fun point stmt->
      	let (p1,p2) = LiUtils.get_stmt_location stmt in
      	let spoint = {fname=name;sid=stmt.Cil_types.sid} in
				if (Equation.compare_point spoint Equation.vertex_dummy)!=0 then
      	(
      	match stmt.skind with
      	| Instr(instr)->
      		(match instr with
      		| Set(lval,e,_)->
      			let (host,offset) = lval in
      			(match host with
      			| Var(v)->
      				let var = Apron.Var.of_string v.vname in
		   				let (texpr:Apron.Texpr1.t) =
		   					let texp = (Translate.force_exp_to_texp e) in
								Apron.Texpr1.of_expr env texp
							in
							let transfer = Equation.Tassign(var,texpr) in
							
							Equation.add_equation graph [|point|] transfer spoint;
						| Mem(e1)->Cil.d_exp fmt e1;Format.print_flush ();Printf.printf "\n";
							let strfmt = Format.str_formatter in
							Cil.d_lval strfmt lval;
							let name = Format.flush_str_formatter () in
							let var = Apron.Var.of_string name in(*(LiUtils.get_exp_name e1)*)
		   				let (texpr:Apron.Texpr1.t) =
		   					let texp = (Translate.force_exp_to_texp e) in
								Apron.Texpr1.of_expr env texp
							in
      				let transfer = Equation.Tassign(var,texpr) in
							Equation.add_equation graph [|point|] transfer spoint;
						);
					| Skip(l)->
						let transfer = Equation.Condition(Boolexpr.make_cst true) in
						Equation.add_equation graph [|point|] transfer spoint;
					| Call(lvo,e,el,l)->
						match lvo with
						| Some(lv)->
							let (host,offset) = lv in
							(match host with
							| Var(v)->
								let callee = Hashhe.find info.Equation.procinfo (LiUtils.get_exp_name e) in
								let pin = ref [] in
								List.iter(fun e->
									pin := !pin@[Translate.force_exp_to_arg env e];
								)el;
								let pout = Apron.Texpr1.of_expr env (Apron.Texpr1.Var((Apron.Var.of_string v.vname))) in
								let calltransfer = Equation.Calle(procinfo,callee,(Array.of_list !pin),Some([|LiType.APTexpr(pout)|])) in
								let returntransfer = Equation.Return(procinfo,callee,(Array.of_list !pin),[|LiType.APTexpr(pout)|]) in
								Equation.add_equation graph [|point|] calltransfer callee.Equation.pstart;
								Equation.add_equation graph [|point;callee.Equation.pexit|] returntransfer spoint;
							| Mem(e)->
								let callee = Hashhe.find info.Equation.procinfo (LiUtils.get_exp_name e) in
								let pin = ref [] in
								List.iter(fun e->
									pin := !pin@[Translate.force_exp_to_arg env e];
								)el;
								let pout = Apron.Texpr1.of_expr env (Apron.Texpr1.Var((Apron.Var.of_string (LiUtils.get_exp_name e)))) in
								let calltransfer = Equation.Calle(procinfo,callee,(Array.of_list !pin),Some([|LiType.APTexpr(pout)|])) in
								let returntransfer = Equation.Return(procinfo,callee,(Array.of_list !pin),[|LiType.APTexpr(pout)|]) in
								Equation.add_equation graph [|point|] calltransfer callee.Equation.pstart;
								Equation.add_equation graph [|point;callee.Equation.pexit|] returntransfer spoint;
							);
						| None->
      				let fname = LiUtils.get_exp_name e in
      				if (String.compare fname "__assert_fail")==0 then
      				((*assert()*)
		    				let last = List.nth stmt.preds ((List.length stmt.preds)-1) in
		    				Cil.d_stmt fmt last;Format.print_flush ();Printf.printf "\n";
      				)else
      				(
							let callee = Hashhe.find info.Equation.procinfo fname in
							let pin = ref [] in
							List.iter(fun e->
								Printf.printf "pin=\n";Cil.d_exp fmt e;Format.print_flush ();Printf.printf "\n";
								let arg = Translate.force_exp_to_arg env e in
								LiType.print_arg fmt arg;Printf.printf "\n";
								pin := !pin@[arg];
							)el;
							let calltransfer = Equation.Calle(procinfo,callee,(Array.of_list !pin),None) in
							let returntransfer = Equation.Return(procinfo,callee,(Array.of_list !pin),[||]) in
							Equation.add_equation graph [|point|] calltransfer callee.Equation.pstart;
							Equation.add_equation graph [|point;callee.Equation.pexit|] returntransfer spoint;
							);
      		| _->
      			Cil.d_stmt fmt stmt;Format.print_flush ();Printf.printf "\n";
      			let transfer = Equation.Condition(Boolexpr.make_cst true) in
						Equation.add_equation graph [|point|] transfer spoint;
      		);
      	| Loop(_,_,_,_,_)->
      		Translate.generate_array fmt procinfo.kf (Hashtbl.find arrayvars (Kernel_function.get_id procinfo.kf)) stmt;
      		let loop = Translate.extract_loop stmt in
      		let rec find_con s conl =
      			match s.skind with
      			| Instr(ins)->
      				begin match ins with
		    			| Call(lvo,e,el,l)->
		    				let fname = LiUtils.get_exp_name e in
		    				if (String.compare fname "__assert_fail")==0 then
		    				(
		    					let last = List.nth stmt.preds ((List.length stmt.preds)-1) in
				  				match last.skind with
				  				| If(e,b1,b2,_)->
				  					if (List.exists(fun (s,e1)->e1==e) !conl)==false then
				  					begin conl := (last,e)::(!conl); end;
				  				| _->();
		    				);
		    			| Skip(_)->
				  			List.iter(fun su->
				  				find_con su conl;
				  			)s.succs;
		    			| _->(); 
		    			end;
      			| If(e,b1,b2,_)->
      				if (List.exists(fun (s,e1)->e1==e) !conl)==false then
      				begin conl := (s,e)::!conl; end;
      				List.iter(fun s->
      					find_con s conl;
      				)b1.bstmts;
      				List.iter(fun s->
      					find_con s conl;
      				)b2.bstmts;
      			|TryFinally(b1,b2,_)|TryExcept(b1,_,b2,_)->
      				List.iter(fun s->
      					find_con s conl;
      				)b1.bstmts;
      				List.iter(fun s->
      					find_con s conl;
      				)b2.bstmts;
      			| Switch(e,b,_,_)->
      				if (List.exists(fun (s,e1)->e1==e) !conl)==false then
      				begin conl := (s,e)::!conl; end;
      				List.iter(fun s->
      					find_con s conl;
      				)b.bstmts;
      			|Loop(_,b,_,_,_)|Block(b)->
      				List.iter(fun s->
      					find_con s conl;
      				)b.bstmts;
      			| UnspecifiedSequence(l)->
      				let b = Cil.block_from_unspecified_sequence l in
      				List.iter(fun s->
      					find_con s conl;
      				)b.bstmts;
      			| Goto(s,_)->
      				find_con !s conl;
      			| _->();
      		in
      		
      		let conl = ref [] in
      		find_con stmt conl;
      		Printf.printf "cons after loop1\n";
      		List.iter(fun (_,e)->
      			Cil.d_exp fmt e;Format.print_flush ();Printf.printf "\n";
      		)!conl;
      		Printf.printf "cons after loop2\n";
      		
      		
      		let first_stmt = List.nth loop.body 0 in
      		let first_id = LiUtils.get_stmt_id first_stmt in
      		let ffirst_stmt = LiUtils.get_stmt_first first_stmt in
      		let end_stmt =  LiUtils.get_stmt_end (List.nth loop.body ((List.length loop.body)-1)) in
      		
      		let vars = LiUtils.extract_varinfos_from_stmt stmt in
			 		let lvars = Cil_datatype.Varinfo.Set.elements vars in
					
					
					let transfers = Translate.generate_template fmt procinfo.kf loop lvars !conl stmt env ipl wp_compute in
					List.iter(fun constransfer->
						Equation.add_equation graph [|point|] constransfer {fname=name;sid=first_stmt.Cil_types.sid};
						Equation.add_equation graph [|{fname=name;sid=end_stmt.Cil_types.sid}|] constransfer point;
					)transfers;
					
      		(*let code_annotation = Apply.apply_lincons1 fmt procinfo.kf stmt cons in
          let root_code_annot_ba = Cil_types.User(code_annotation) in
          Annotations.add procinfo.kf stmt [Ast.self] root_code_annot_ba;
          LiAnnot.prove_code_annot procinfo.kf stmt code_annotation;*)
          
      		let bexpr = force_exp2bexp loop.con in
      		let cond = boolexpr_of_bexpr env bexpr in
					let condnot = boolexpr_of_bexpr env (NOT bexpr) in
					let condtransfer = Equation.Condition(cond) in
					let condnottransfer = Equation.Condition(condnot) in
					
					Equation.add_equation graph [|point|] condtransfer {fname=name;sid=first_stmt.Cil_types.sid};
					Equation.add_equation graph [|{fname=name;sid=first_stmt.Cil_types.sid}|] (Equation.Condition(Boolexpr.make_cst true)) {fname=name;sid=first_id};
					Equation.add_equation graph [|{fname=name;sid=end_stmt.Cil_types.sid}|] (Equation.Condition(Boolexpr.make_cst true)) point;
					Equation.add_equation graph [|point|] condnottransfer {fname=name;sid=stmt.Cil_types.sid};
					
      		iter_block name procinfo (Cil.mkBlock loop.body);
      	| Block(b)->
      		iter_block name procinfo b;
      	| UnspecifiedSequence(seq)->
					iter_block name procinfo (Cil.block_from_unspecified_sequence seq);
      	| If(exp,b1,b2,l)->
      		let bexpr = force_exp2bexp exp in
      		let cond = boolexpr_of_bexpr env bexpr in
					let condnot = boolexpr_of_bexpr env (NOT bexpr) in
					let condtransfer = Equation.Condition(cond) in
					let condnottransfer = Equation.Condition(condnot) in
					
					if (List.length b1.bstmts)>0 then(
						(*let first_stmt = List.hd b1.bstmts in
						let last_stmt = List.nth first_stmt.preds ((List.length first_stmt.preds)-1) infailure if empty*)
						Equation.add_equation graph
							[|point|] condtransfer {fname=b1.kf_name;sid=b1.bid};
						
						let last_stmt = List.nth b1.bstmts ((List.length b1.bstmts)-1) in
						if (List.length last_stmt.succs)>0 then
						(
						let first_stmt = List.nth last_stmt.succs 0 in
						
						if (Equation.compare_point {fname=name;sid=first_stmt.Cil_types.sid} Equation.vertex_dummy)!=0 then(
							let last_stmt = List.nth b1.bstmts ((List.length b1.bstmts)-1) in
							Equation.add_equation graph
								[|{fname=name;sid=last_stmt.Cil_types.sid}|] (Equation.Condition(Boolexpr.make_cst true)) {fname=name;sid=first_stmt.Cil_types.sid};
						);
						(*the edge should link to the first succed-stmt of the last stmt of b1?bpoint or spoint?not sure*)
						);
					);
					
					if (List.length b2.bstmts)>0 then(
						(*let first_stmt = List.nth b1.bstmts 0 in
						let last_stmt = List.nth first_stmt.preds ((List.length first_stmt.preds)-1) infailure if empty*)
						Equation.add_equation graph
							[|point|] condnottransfer {fname=b2.kf_name;sid=b2.bid};
							
						let last_stmt = List.nth b2.bstmts ((List.length b2.bstmts)-1) in
						if (List.length last_stmt.succs)>0 then
						(
						let first_stmt = List.nth last_stmt.succs 0 in
						
						if (Equation.compare_point {fname=name;sid=first_stmt.Cil_types.sid} Equation.vertex_dummy)!=0 then(
							let last_stmt = List.nth b2.bstmts ((List.length b2.bstmts)-1) in
							Equation.add_equation graph
								[|{fname=name;sid=last_stmt.Cil_types.sid}|] (Equation.Condition(Boolexpr.make_cst true)) {fname=name;sid=first_stmt.Cil_types.sid};
						);
						);
					)else
					(
						let last_stmt = List.nth b1.bstmts ((List.length b1.bstmts)-1) in
						let first_stmt = List.nth last_stmt.succs 0 in
						if (Equation.compare_point {fname=name;sid=first_stmt.Cil_types.sid} Equation.vertex_dummy)!=0 then(
							Equation.add_equation graph	[|point|] condnottransfer {fname=name;sid=first_stmt.Cil_types.sid};
						);
					);
					
					iter_block name procinfo b1;
					iter_block name procinfo b2
				| Goto(sr,loc)->
						let (p1,p2) = LiUtils.get_stmt_location !sr in
						let transfer = Equation.Condition(Boolexpr.make_cst true) in
						Equation.add_equation graph [|spoint|] transfer {fname=name;sid=(!sr).Cil_types.sid};
				| Cil_types.Return(_,_)->(*wonder whether it is right*)
					Printf.printf "Return transfer\n";
					(*let transfer = Equation.Condition(Boolexpr.make_cst true) in
					let transfer = Equation.Condition(Boolexpr.DISJ([])) in
					Equation.add_equation graph [|point|] transfer spoint;*)
      	| _->Printf.printf "other stmt\n";TypePrinter.print_stmtkind fmt stmt.skind;Format.print_flush ();Printf.printf "\n";
      		let transfer = Equation.Condition(Boolexpr.make_cst true) in
					Equation.add_equation graph [|point|] transfer spoint;
				);
				spoint
     	)bpoint block.bstmts;
     	()
     	);
      );
   	in

		Globals.Functions.iter(fun kf ->
			let name = Kernel_function.get_name kf in
			begin match kf.fundec with
			| Definition(_,(p1,p2))->
				let fundec = Kernel_function.get_definition kf in
				let procinfo = Hashhe.find info.Equation.procinfo name in
				let transfer = Equation.Condition(Boolexpr.make_cst true) in
				iter_block name procinfo fundec.sbody;
			| Declaration(spec,v,vlo,loc)->();
			end;
		);

    graph

end

(*  ********************************************************************** *)
(** {2 Backward equations} *)
(*  ********************************************************************** *)

module Backward = struct
  let make (info:Equation.info) : Equation.graph =
  	
    let graph = Equation.create 3 info in

		let rec iter_block (name:string) (procinfo:Equation.procinfo) (block:block) : unit =
      if (List.length block.bstmts)>0 then(
      let fmt = Format.std_formatter in
      let env = procinfo.Equation.penv in
      let first_stmt = List.hd block.bstmts in
      let bpoint = {fname=name;sid=first_stmt.Cil_types.sid} in
      
      if (Equation.compare_point bpoint Equation.vertex_dummy)!=0 then
      ignore begin
      List.fold_left(fun point stmt->
      	let spoint = {fname=name;sid=stmt.Cil_types.sid} in
				if (Equation.compare_point spoint Equation.vertex_dummy)!=0 then
      	(
      	match stmt.skind with
      	| Instr(instr)->
      		(match instr with
      		| Set(lval,e,_)->
      			let (host,offset) = lval in
      			(match host with
      			| Var(v)->
      				let var = Apron.Var.of_string v.vname in
		   				let (texpr:Apron.Texpr1.t) =
		   					let texp = (Translate.force_exp_to_texp e) in
								Apron.Texpr1.of_expr env texp
							in
							let transfer = Equation.Tassign(var,texpr) in
							
							Equation.add_equation graph [|spoint|] transfer point;
						| Mem(e1)->
							let strfmt = Format.str_formatter in
							Cil.d_lval strfmt lval;
							let name = Format.flush_str_formatter () in
							let var = Apron.Var.of_string name in(*(LiUtils.get_exp_name e1)*)
		   				let (texpr:Apron.Texpr1.t) =
		   					let texp = (Translate.force_exp_to_texp e) in
								Apron.Texpr1.of_expr env texp
							in
      				let transfer = Equation.Tassign(var,texpr) in
							Equation.add_equation graph [|spoint|] transfer point;
						);
					| Skip(l)->
						let transfer = Equation.Condition(Boolexpr.make_cst true) in
						Equation.add_equation graph [|point|] transfer spoint;
					| Call(lvo,e,el,l)->
						match lvo with
						| Some(lv)->
							let (host,offset) = lv in
							(match host with
							| Var(v)->
								let callee = Hashhe.find info.Equation.procinfo (LiUtils.get_exp_name e) in
								let pin = callee.pinput in
								let ain = ref [] in
								Array.iter(fun v->
									ain := !ain@[LiType.APTexpr(Apron.Texpr1.of_expr env (Apron.Texpr1.Var(v)))];
								)pin;
								
								let pout = Apron.Texpr1.of_expr env (Apron.Texpr1.Var(Apron.Var.of_string v.vname)) in
								let calltransfer = Equation.Calle(procinfo,callee,(Array.of_list !ain),Some([|LiType.APTexpr(pout)|])) in
								let returntransfer = Equation.Return(procinfo,callee,(Array.of_list !ain),[|LiType.APTexpr(pout)|]) in
								Equation.add_equation graph [|callee.Equation.pstart|] calltransfer point;
								Equation.add_equation graph [|spoint|] returntransfer callee.Equation.pexit;
							| Mem(e)->
								let callee = Hashhe.find info.Equation.procinfo (LiUtils.get_exp_name e) in
								let pin = callee.pinput in
								let ain = ref [] in
								Array.iter(fun v->
									ain := !ain@[LiType.APTexpr(Apron.Texpr1.of_expr env (Apron.Texpr1.Var(v)))];
								)pin;
								
								let pout = Apron.Texpr1.of_expr env (Apron.Texpr1.Var((Apron.Var.of_string (LiUtils.get_exp_name e)))) in
								let calltransfer = Equation.Calle(procinfo,callee,(Array.of_list !ain),Some([|LiType.APTexpr(pout)|])) in
								let returntransfer = Equation.Return(procinfo,callee,(Array.of_list !ain),[|LiType.APTexpr(pout)|]) in
								Equation.add_equation graph [|callee.Equation.pstart|] calltransfer point;
								Equation.add_equation graph [|spoint|] returntransfer callee.Equation.pexit;
							);
						| None->
							let fname = LiUtils.get_exp_name e in
							if (String.compare fname "__assert_fail")==0 then
      				((*assert()*)
		    				let last = List.nth stmt.preds ((List.length stmt.preds)-1) in
		    				Cil.d_stmt fmt last;Format.print_flush ();Printf.printf "\n";
      				)else
      				(
							let callee = Hashhe.find info.Equation.procinfo fname in
							let pin = callee.pinput in
							let ain = ref [] in
							
							List.iter(fun e->
								ain := !ain@[Translate.force_exp_to_arg env e];
							)el;
							(*Array.iter(fun v->
								Apron.Var.print fmt v;Format.print_flush ();Printf.printf "\n";
								ain := !ain@[Apron.Texpr1.of_expr env (Apron.Texpr1.Var(v))];
							)pin;*)
								
							let calltransfer = Equation.Calle(procinfo,callee,(Array.of_list !ain),None) in
							let returntransfer = Equation.Return(procinfo,callee,(Array.of_list !ain),[||]) in
							Equation.add_equation graph [|callee.Equation.pstart|] calltransfer point;
							Equation.add_equation graph [|spoint|] returntransfer callee.Equation.pexit;(*no return transfer*)
							);
      		| _->
      			Printf.printf "c2equation Forward make Instr not Set,Skip,Call\n";
      			Cil.d_stmt fmt stmt;Format.print_flush ();Printf.printf "\n";
      			let transfer = Equation.Condition(Boolexpr.make_cst true) in
						Equation.add_equation graph [|spoint|] transfer point;
      		);
      	| Loop(_,b,_,_,_)->
      		iter_block name procinfo b;
      	| Block(b)->
      		iter_block name procinfo b;
      	| UnspecifiedSequence(seq)->
					iter_block name procinfo (Cil.block_from_unspecified_sequence seq);
      	| If(exp,b1,b2,l)->
      		let bexpr = force_exp2bexp exp in
      		let cond = boolexpr_of_bexpr env bexpr in
					let condnot = boolexpr_of_bexpr env (NOT bexpr) in
					let condtransfer = Equation.Condition(cond) in
					let condnottransfer = Equation.Condition(condnot) in
					
					if (List.length b1.bstmts)>0 then(
						let first_stmt = List.hd b1.bstmts in
						let last_stmt = List.nth first_stmt.preds ((List.length first_stmt.preds)-1) in(*failure when empty*)
						Equation.add_equation graph
							[|{fname=name;sid=last_stmt.Cil_types.sid}|] condtransfer point;
							
						let last_stmt = List.nth b1.bstmts ((List.length b1.bstmts)-1) in
						
						if (Equation.compare_point {fname=name;sid=last_stmt.Cil_types.sid} Equation.vertex_dummy)!=0 then(
							let first_stmt = List.hd last_stmt.succs in
							Equation.add_equation graph
								[|{fname=name;sid=first_stmt.Cil_types.sid}|] (Equation.Condition(Boolexpr.make_cst true)) {fname=name;sid=last_stmt.Cil_types.sid};Printf.printf "add transfer Condition\n";
						);					
						(*let (p1,p2) = LiUtils.get_block_epoint b1 in
						Printf.printf "if b1 true\n";
						Equation.add_equation graph
							[|spoint|] (Equation.Condition(Boolexpr.make_cst true)) {pos1=p1;pos2=p2};*)
					);
					
					if (List.length b2.bstmts)>0 then(
						let first_stmt = List.hd b2.bstmts in
						Equation.add_equation graph
							[|{fname=name;sid=first_stmt.Cil_types.sid}|] condnottransfer point;
							
						let last_stmt = List.nth b2.bstmts ((List.length b2.bstmts)-1) in
						Printf.printf "if b2 true\n";
						Equation.add_equation graph
							[|spoint|] (Equation.Condition(Boolexpr.make_cst true)) {fname=name;sid=last_stmt.Cil_types.sid};
					)else
					(
						let last_stmt = List.nth b1.bstmts ((List.length b1.bstmts)-1) in
						let first_stmt = List.nth last_stmt.succs 0 in
						
						if (Equation.compare_point {fname=name;sid=first_stmt.Cil_types.sid} Equation.vertex_dummy)!=0 then
							Equation.add_equation graph [|{fname=name;sid=first_stmt.Cil_types.sid}|] condnottransfer point;
					);
					
					iter_block name procinfo b1;
					iter_block name procinfo b2
      	| _->
      		let transfer = Equation.Condition(Boolexpr.make_cst true) in
					()(*Equation.add_equation graph [|spoint|] transfer point;*)
				);
				spoint
     	)bpoint block.bstmts;
      end
     )
    in

    Globals.Functions.iter(fun kf ->
    	let name = Kernel_function.get_name kf in
			match kf.fundec with
			| Definition(_,_)->
				let fundec = Kernel_function.get_definition kf in
				let procinfo = Hashhe.find info.Equation.procinfo fundec.svar.vname in
				iter_block name procinfo fundec.sbody;
			| Declaration(spec,v,vlo,loc)->()
		);

    graph

end
