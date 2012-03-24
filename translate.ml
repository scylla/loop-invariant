open Cil
open Cil_types
open Cil_datatype
open LiVisitor
open LiAnnot
open LiUtils
open Equation

let avar_to_lvar va =
	let lv =
		{	lv_name = (Apron.Var.to_string va);
			lv_id = -1;
			lv_type = Cil_types.Ctype(Cil.intType);
			lv_origin = None
		}
	in
	lv;;


(** Add to an environment a list of variables *)
let add_env (env:Apron.Environment.t) (lvar:varinfo list) avar2cvar :Apron.Environment.t =
	let names = ref [] in
	let (a1,a2)= Apron.Environment.vars env in
	Array.iter(fun v->
		names := (Apron.Var.to_string v)::!names;
	)a1;
	Array.iter(fun v->
		names := (Apron.Var.to_string v)::!names;
	)a2;
	let lint = ref [] and lreal = ref [] in
	List.iter(fun var->
		if (List.for_all (fun vn->(String.compare vn var.vname)!=0) !names)==true then
		(
		match var.vtype with
		| TInt(_,_)->
			let avar = (Apron.Var.of_string var.vname) in
			lint := avar::!lint;
			names := var.vname::(!names);
			(*update [names]??*)
			Hashhe.add avar2cvar avar var;
		| TFloat(_,_)->
			let avar = (Apron.Var.of_string var.vname) in
			lreal := avar::!lreal;
			names := var.vname::(!names);
			Hashhe.add avar2cvar avar var;
		| TPtr(tp,attr)->(*pointer,how to?*)
			Cil.d_var Format.std_formatter var;Format.print_flush ();Printf.printf "\n";
			let avar = (Apron.Var.of_string var.vname) in
			lint := avar::!lint;
			names := var.vname::(!names);
			Hashhe.add avar2cvar avar var;
		| TArray(tp,eo,size,attr)->
			begin match eo with
			| Some(e)->
				let avar = (Apron.Var.of_string var.vname) in
				lint := avar::!lint;
			names := var.vname::(!names);
				Hashhe.add avar2cvar avar var;
			| None->();
			end;
		| _->Cil.d_type Format.std_formatter var.vtype;Format.print_flush ();Printf.printf "\n";
		);
	)lvar;
  Apron.Environment.add env
    (Array.of_list !lint)
    (Array.of_list !lreal)

let add_vars (env:Apron.Environment.t) (lvar:Apron.Var.t list) avar2cvar :Apron.Environment.t =
	let names = ref [] in
	
	let (a1,a2)= Apron.Environment.vars env in
	Array.iter(fun v->
		names := (Apron.Var.to_string v)::!names;
	)a1;
	Array.iter(fun v->
		names := (Apron.Var.to_string v)::!names;
	)a2;
	let lint = ref [] and lreal = ref [] in
	List.iter(fun av->
		if (List.for_all (fun vn->(String.compare (Apron.Var.to_string av) vn)!=0) !names)==true then
		(
			lint := av::!lint;
		);
	)lvar;
  Apron.Environment.add env
    (Array.of_list !lint)
    (Array.of_list !lreal)
    
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

let negate_linexpr (lexpr:Apron.Linexpr1.t) : Apron.Linexpr1.t
	=
	let copy = Apron.Linexpr1.copy lexpr in
	Apron.Linexpr1.iter(fun c v->
		Apron.Linexpr1.set_coeff copy v (Apron.Coeff.neg c);
	)copy;
	Apron.Linexpr1.set_cst copy (Apron.Coeff.neg (Apron.Linexpr1.get_cst copy));
	copy


let rec force_exp_to_texp (exp:Cil_types.exp) : Apron.Texpr1.expr =
	begin match exp.enode with
	| BinOp(op,e1,e2,ty)->
		let te1 = force_exp_to_texp e1 in
		let te2 = force_exp_to_texp e2 in
		(match op with
		| PlusA->
			Apron.Texpr1.Binop(Apron.Texpr1.Add,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| MinusA->
			Apron.Texpr1.Binop(Apron.Texpr1.Sub,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| Div->
			Apron.Texpr1.Binop(Apron.Texpr1.Div,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| Mult->
			Apron.Texpr1.Binop(Apron.Texpr1.Mul,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| Mod->
			Apron.Texpr1.Binop(Apron.Texpr1.Mod,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| Le->(*<=*)
			Apron.Texpr1.Binop(Apron.Texpr1.Sub,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| Lt->(*<*)
			Apron.Texpr1.Binop(Apron.Texpr1.Sub,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| Eq->
			Apron.Texpr1.Binop(Apron.Texpr1.Sub,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| Ne->(*!=*)
			Apron.Texpr1.Binop(Apron.Texpr1.Sub,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| PlusPI->(*pointer + interger*)
			Apron.Texpr1.Binop(Apron.Texpr1.Add,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| IndexPI->
			Apron.Texpr1.Binop(Apron.Texpr1.Add,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		|_->
			Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";
			Printf.printf "unknownBinOp\n";
			(*TypePrinter.print_exp_type Format.std_formatter exp;
			Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";*)
			Apron.Texpr1.Var(Apron.Var.of_string "unknownBinOp");
		)
	| UnOp(op,e,ty)->
		(match op with
		| Neg->
			let te = force_exp_to_texp e in
			Apron.Texpr1.Unop(Apron.Texpr1.Neg,te,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| _->
			Printf.printf "unknownUnOp\n";
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
			TypePrinter.print_exp_type Format.std_formatter exp;
			Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";
			Apron.Texpr1.Var(Apron.Var.of_string "unknownConst");
		)
	| CastE(ty,e)->
		force_exp_to_texp e;(*not exactly right*)
	| Lval((host,offset))->
		Printf.printf "unknownEnode1 in translate\n";
		begin match host with
		| Mem(m)->
			();(*Cil.d_exp Format.std_formatter m;Format.print_flush ();Printf.printf "\n";*)
		| Var(v)->();
		end;
		Apron.Texpr1.Var(Apron.Var.of_string "unknownEnode")
	|_->
		Printf.printf "unknownEnode2 in translate\n";
		Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";
		Apron.Texpr1.Var(Apron.Var.of_string "unknownEnode")
	end

let rec force_exp_to_arg (env:Apron.Environment.t) (exp:Cil_types.exp) : LiType.arg =
	begin match exp.enode with
	| StartOf(lv)|AddrOf(lv)|Lval(lv)->
		let strfmt = Format.str_formatter in
		Cil.d_lval strfmt lv;	
		let name = Format.flush_str_formatter () in
		LiType.APVar((Apron.Var.of_string name))
	| Const(cons)->
		begin match cons with
		|	CInt64(big,_,_)->
			LiType.APScalar(Apron.Scalar.of_int (My_bigint.to_int big));
		| CReal(f,_,_)->
			LiType.APScalar(Apron.Scalar.of_float f);
		| _->
			LiType.APScalar(Apron.Scalar.of_float 0.0);
		end;
	| Lval(lval)->
		let (host,offset) = lval in
		begin match host with
		| Mem(m)->
			let strfmt = Format.str_formatter in
			Cil.d_lval strfmt lval;
			let name = Format.flush_str_formatter () in
			LiType.APVar(Apron.Var.of_string name);
		| Var(v)->
			LiType.APVar(Apron.Var.of_string (LiUtils.get_vname v));
		end;
	| CastE(ty,e)->
		force_exp_to_arg env e;
	| _->
		let expr = force_exp_to_texp exp in
		LiType.APTexpr(Apron.Texpr1.of_expr env expr)
	end


let force_exp2tcons (e:Cil_types.exp) env: Apron.Tcons1.t =
	let texpr = force_exp_to_texp e in
	let vars = LiUtils.extract_varinfos_from_exp e in
	let lvars = Cil_datatype.Varinfo.Set.elements vars in
	(*let env = add_env env lvars in*)
	let texpr = Apron.Texpr1.of_expr env texpr in
	begin match e.enode with
	| BinOp(op,_,_,_)->
		(match op with
		| Eq->Apron.Tcons1.make texpr Apron.Tcons1.EQ;
		| Ne->Apron.Tcons1.make texpr Apron.Tcons1.DISEQ;
		| Gt->Apron.Tcons1.make texpr Apron.Tcons1.SUP;
		| Ge->Apron.Tcons1.make texpr Apron.Tcons1.SUPEQ;
		| Lt->Apron.Tcons1.make (negate_texpr texpr) Apron.Tcons1.SUP;
		| Le->Apron.Tcons1.make (negate_texpr texpr) Apron.Tcons1.SUPEQ;
		| _->Apron.Tcons1.make texpr Apron.Tcons1.EQ;
		);
	| _->Apron.Tcons1.make texpr Apron.Tcons1.EQ;
	end

(*get max sid in block*)
let rec get_block_maxid (id:int ref) (b:Cil_types.block) =
	List.iter(fun s->
		let fmt = Format.std_formatter in
		if s.Cil_types.sid> !id then id := s.Cil_types.sid;
		match s.Cil_types.skind with
		| Instr(_)|Cil_types.Return(_,_)|Goto(_,_)|Break(_)|Continue(_)->();
		| If(e,b1,b2,_)->
			get_block_maxid id b1;
			get_block_maxid id b2;
		| TryFinally(b1,b2,_)->
			get_block_maxid id b1;
			get_block_maxid id b2;
		| Switch(_,b,sl,_)->
			List.iter(fun s->
				if s.Cil_types.sid> !id then id := s.Cil_types.sid;
			)sl;
			get_block_maxid id b;
		| Loop(_,b,_,_,_)|Block(b)->
			get_block_maxid id b;
		| UnspecifiedSequence(seq)->
			let b = Cil.block_from_unspecified_sequence seq in
			get_block_maxid id b;
		| TryExcept(b1,_,b2,_)->
			get_block_maxid id b1;
			get_block_maxid id b2;
	)b.bstmts;;

(*assign bpoint with name and id.id starts from max id in all stmts and increases
step by 1 every assignment*)
let rec generate_bpoint (id:int ref) (name:string) (b:Cil_types.block) =
	id := !id+1;
	b.Cil_types.bid <- !id;
	b.Cil_types.kf_name <- name;
	List.iter(fun s->
		match s.skind with
		| Instr(_)|Cil_types.Return(_,_)|Goto(_,_)|Break(_)|Continue(_)->();
		| If(_,b1,b2,_)|TryFinally(b1,b2,_)->
			generate_bpoint id name b1;
			generate_bpoint id name b2;
		| Switch(_,b,sl,_)->
			generate_bpoint id name b;
		| Loop(_,b,_,_,_)|Block(b)->
			generate_bpoint id name b;
		| UnspecifiedSequence(seq)->
			let b = Cil.block_from_unspecified_sequence seq in
			generate_bpoint id name b;
		| TryExcept(b1,_,b2,_)->
			generate_bpoint id name b1;
			generate_bpoint id name b2;
	)b.bstmts;;

let preprocess_bpoint maxid =
	Globals.Functions.iter(fun kf ->
		match kf.fundec with
		| Definition(dec,loc)->
			let name = Kernel_function.get_name kf in
			dec.sbody.kf_name <- name;
			dec.sbody.bid <- !maxid+1;
			maxid := !maxid+1;
			generate_bpoint maxid name dec.sbody;
		| Declaration(spec,v,vlo,_)->
		  ()
	);;
	
let force_stmt2block (stmt:Cil_types.stmt) :Cil_types.block =
	(match stmt.skind with
	| Cil_types.Block(b)->
		b;
	| _->
		Cil.mkBlock [stmt];
	);;
	
let extract_loop stmt :Equation.loop =
	let fmt = Format.std_formatter in
	(match stmt.skind with
	| Loop(_,b,loc,_,_)->
		let con_stmt = List.nth b.bstmts 1 in
		let body_stmt = ref [] in
		for i=2 to ((List.length b.bstmts)-1) do
			body_stmt := !body_stmt@[List.nth b.bstmts i];
		done;
		begin match con_stmt.skind with
		| If(con,_,_,_)->
			{Equation.con=con;Equation.body=(!body_stmt)};
		| _->(*while(1){},so the con should be true*)
			Printf.printf "con_stmt:";TypePrinter.print_stmtkind fmt con_stmt.skind;
			let con = Cil.one ~loc:loc in
			let body_stmt = Cil.dummyStmt in
			{Equation.con=con;Equation.body = [body_stmt]};
		end;
	| _->
		let con = Cil.dummy_exp (Cil_types.Const(Cil_types.CStr("dummy_con2"))) in
		let body_stmt = Cil.dummyStmt in
		{Equation.con=con;Equation.body = [body_stmt]};
	);;

let rec force_assert_to_annot (e:Cil_types.exp) (kf:Cil_types.kernel_function) (s:Cil_types.stmt) = 
	(match e.enode with
	| BinOp(op,e1,e2,_)->
		Cil.d_binop Format.std_formatter op;Format.print_flush ();Printf.printf "\n";
		force_assert_to_annot e1 kf s;
		force_assert_to_annot e2 kf s;
	| _->
		let code_annot = !Db.Properties.Interp.force_exp_to_assertion e in
    let assert_root_code_annot_ba = Cil_types.User(code_annot) in
    Annotations.add kf s [Ast.self] assert_root_code_annot_ba;
  );;
           			
let translate_kf (kf:Cil_types.kernel_function) =
	let fundec = Kernel_function.get_definition kf in
	List.iter(fun stmt ->
		match stmt.skind with
		| Instr(ins) ->
		  (match ins with
		  | Call(lo,e,el,l) ->
        Printf.printf "\n";
      | _->();
      );
    | _->();
	)fundec.sallstmts;;

let copy_env env =
	let (va1,va2) = Apron.Environment.vars env in
	Apron.Environment.make va1 va2;;
	
let merge_env env1 env2 =
	let (va1,va2) = Apron.Environment.vars env2 in
	(*Apron.Environment.add env1 va1 va2;*)
	Array.iter(fun v->
		if (Apron.Environment.mem_var !env1 v)==false then
			env1 := Apron.Environment.add !env1 [|v|] [||];
		();
	)va1;
	Array.iter(fun v->
		if (Apron.Environment.mem_var !env1 v)==false then
			env1 := Apron.Environment.add !env1 [||] [|v|];
		();
	)va2;
	!env1;;

let rec extract_const_from_exp (lv:lval option) e =
	begin match e.enode with
	| Const(c)->
		begin match c with
		| CInt64(big,_,_)->
			[(lv,My_bigint.to_int big)];
		| CReal(f,_,_)->[(lv,int_of_float f)];
		| _->[];
		end;
	| BinOp(op,e1,e2,_)->
		(extract_const_from_exp lv e1)@(extract_const_from_exp lv e2);
	| UnOp(op,e1,_)->
		extract_const_from_exp lv e1;
	| _->[];
	end;;

let extract_const_from_stmt cons s =
	let rec extract s =
		begin match s.skind with
		| Instr(ins)->
			begin match ins with
			| Set(lv,e,_)->
				begin match e.enode with
				| BinOp(op,e1,e2,_)->
					begin match op with
					| PlusA|MinusA->
						let l = extract_const_from_exp (Some(lv)) e2 in
						List.iter(fun (lv,c)->
							if (List.exists(fun (lv1,c1)->
									match (lv1,lv) with
									| ((Some(v1)),(Some(v2)))->
										((Cil.compareLval v1 v2) && (c1==c));
									| _->true;
									) (!cons)
								)==false then
							begin cons := [(lv,c)]@(!cons); end;
						)l;
					| _->();
					end;
				| _->();
				end;				
			| _->();
			end;
		| If(_,b1,b2,_)|TryFinally(b1,b2,_)|TryExcept(b1,_,b2,_)->
			List.iter(fun s1->
				extract s1;
			)b1.bstmts;
			List.iter(fun s1->
				extract s1;
			)b2.bstmts;
		| Switch(_,b,sl,_)->
			List.iter(fun s1->
				extract s1;
			)b.bstmts;
		| Loop(_,b,_,_,_)|Block(b)->
			List.iter(fun s1->
				extract s1;
			)b.bstmts;
		| UnspecifiedSequence(seq)->
			let b = Cil.block_from_unspecified_sequence seq in
			List.iter(fun s1->
				extract s1;
			)b.bstmts;
		| _->();
		end;
	in
	extract s;;
	
let extract_step kf vars stmt =
	let fmt =  Format.std_formatter in
	let steps = ref [] in
	let dec = Kernel_function.get_definition kf in
	let fname = Kernel_function.get_name kf in
	
	Printf.printf "extract_step\n";
	let pdg = (!Db.Pdg.get) kf in
	(*(!Db.Pdg.extract) pdg ("/home/lzh/pdg_"^fname^".dot");*)
	
	let vlist = LiPdg.find_vnodes vars pdg in
	let blist = LiPdg.find_bnodes dec.sbody pdg in
	Printf.printf "vlist.len=%d\n" (List.length vlist);
	
	begin match stmt.skind with
	| Loop(_,b,_,_,_)->
		let llist = LiPdg.find_bnodes b pdg in
		let len_llist = List.length vlist in
		
		try
		for i=0 to (len_llist-1) do
			Printf.printf "nth1:%d\n" i;
			let node = List.nth vlist i in
			Printf.printf "nth2:%d\n" i;
			Printf.printf "pretty_node:";(!Db.Pdg.pretty_node) false fmt node;Format.print_flush ();Printf.printf "\n";
			let nodes = (!Db.Pdg.direct_uses) pdg node in(*all_uses.if nodes are too many it will be stack overflow*)
			Printf.printf "use nodes.len=%d\n" (List.length nodes);
			Printf.printf "llist.len=%d\n" len_llist;
			
			let len_nodes = List.length nodes in
			for j=0 to (len_nodes-1) do
				let n = List.nth nodes j in
				Printf.printf "pretty_:";(!Db.Pdg.pretty_node) false fmt n;Format.print_flush ();Printf.printf "\n";
				
				let exists n l =
					let flag = ref false in
					let len = List.length l in
					for i=0 to (len-1) do
						let n1 = List.nth l i in
						if n==n1 then 
						begin flag := true; end;
					done;
					
					!flag
				in
				
				if (exists n llist)==true then
				begin
					let s = PdgTypes.Node.stmt n in
					begin match s with
					| Some(s1)->
						let tmp = ref [] in
						Printf.printf "steps.len1=%d\n" (List.length !steps);
						extract_const_from_stmt tmp s1;
						steps := !tmp@(!steps);
						Printf.printf "steps.len2=%d\n" (List.length !steps);
					| None->();
					end;
				end;
			done;
			
		done;
		with Stack_overflow->Printf.printf "Stack_overflow\n";
	| _->();
	end;
	let res = Hashtbl.create 3 in
	Printf.printf "get res:step.len=%d\n" (List.length !steps);
	List.iter(fun (lv,c)->
		begin match lv with
		| Some(v)->
			let (host,offset) = v in
			begin match host,offset with
			| Var(var),NoOffset->
				let name = LiUtils.get_vname var in
				Printf.printf "step name:%s" name;
				try
					let l = Hashtbl.find res var.vname in
					if (List.for_all(fun c1->c!=c1) !l)==true then			
						l := c::(!l);
				with Not_found->Hashtbl.add res name (ref [c]);
			| _->();
			end;
		| None->();
		end;
	)(!steps);
	Printf.printf "get res end.\n";
	res;;

let rec extract_coeff_from_exp coeffs e varo =
	let ltype = Cil_types.Ctype(Cil.intType) in(*temporary*)
	let fmt = Format.std_formatter in
	let strfmt = Format.str_formatter in
	
	begin match varo with
	| Some(e1)->
		Cil.d_exp strfmt e1;
		let name = Format.flush_str_formatter () in
		Printf.printf "extract:%s" name;
		let res = Hashtbl.find coeffs name in
		begin match e.enode with
		| Const(c)->
			begin match c with
			| CInt64(big,_,_)->
				if (List.for_all(fun c->(Apron.Coeff.cmp c (Apron.Coeff.s_of_int (My_bigint.to_int big)))!=0)
						 !res)==true then
				res := (Apron.Coeff.s_of_int (My_bigint.to_int big))::(!res);
			| CReal(f,_,_)->
				if (List.for_all(fun c->(Apron.Coeff.cmp c (Apron.Coeff.s_of_float f))!=0) !res)==true then
				res := (Apron.Coeff.s_of_float f)::(!res);
			| _->();(*or 1?*)
			end;
		| Lval((host,offset))->();
		| BinOp(op,e1,e2,_)->
			begin match op with
			| Mult->
				(extract_coeff_from_exp coeffs e1 (Some(e2)));(extract_coeff_from_exp coeffs e2 (Some(e1)));
			| Gt->
				(extract_coeff_from_exp coeffs e1 None);(extract_coeff_from_exp coeffs e2 None);
			| _->();
			end;
		| UnOp(op,e1,_)->
			extract_coeff_from_exp coeffs e1 None;
		| _->();
		end;
	| None->
		begin match e.enode with
		| BinOp(op,e1,e2,_)->
			begin match op with
			| Mult->
				(extract_coeff_from_exp coeffs e1 (Some(e2)));(extract_coeff_from_exp coeffs e2 (Some(e1)));
			| Gt->
				(extract_coeff_from_exp coeffs e1 None);(extract_coeff_from_exp coeffs e2 None);
			| _->();
			end;
		| UnOp(op,e1,_)->
			extract_coeff_from_exp coeffs e1 None;
		| _->();
		end;		
	end;;

let extract_coeff_from_loop coeffs stmt =
	let rec analysis_exp e =
		begin match e.enode with
		| BinOp(op,e1,e2,_)->
			begin match op with
			| Mult->
				(extract_coeff_from_exp coeffs e1 (Some(e2)));(extract_coeff_from_exp coeffs e2 (Some(e1)));
			| _->
				analysis_exp e1;
				analysis_exp e2;
			end;
		| _->();
		end;
	in
	
	let rec analysis s =
		begin match s.skind with
		| Instr(ins)->
			begin match ins with
			| Set(lv,e,_)->
				Printf.printf "analysis_exp\n";Cil.d_exp Format.std_formatter e;Format.print_flush ();Printf.printf "\n";
				analysis_exp e;
			| _->();
			end;
		| Loop(_,b,_,_,_)|Block(b)->
			List.iter(fun s->
				analysis s;
			)b.bstmts;
		| If(e,b1,b2,_)->
				analysis_exp e;
			List.iter(fun s->
				analysis s;
			)b1.bstmts;
			List.iter(fun s->
				analysis s;
			)b2.bstmts;
		| Switch(e,b,_,_)->
				analysis_exp e;
			List.iter(fun s->
				analysis s;
			)b.bstmts;
		| UnspecifiedSequence(seq)->
			let b = Cil.block_from_unspecified_sequence seq in
			List.iter(fun s1->
				analysis s;
			)b.bstmts;
		| TryFinally(b1,b2,_)|TryExcept(b1,_,b2,_)->
			List.iter(fun s->
				analysis s;
			)b1.bstmts;
			List.iter(fun s->
				analysis s;
			)b2.bstmts;
		| _->();
		end;
	in
	
	try
	analysis stmt;
	with Stack_overflow ->Printf.printf "Stack_overflow when [extract_coeff_from_loop]\n";;

(*stmt is a [loop] stmt. this deals with array access operations in loop body*)
let generate_array fmt kf (arrayvars:LiType.array_info list) stmt =
	let exps = ref [] in
	
	let rec analysis_exp fmt e =
		(*when access an array element,these should be held*)
		let apply_index fmt base index =
			try
				let info = List.find (fun info->(String.compare info.LiType.v.vname (LiUtils.get_exp_name base))==0) arrayvars in
				if (List.for_all (fun e->(Cil.compareExp e index)==false) !exps)==true then
				begin
					exps := index::(!exps);
					(*i>=0*)
					let zero_term = Cil.lzero () in
					let t = !Db.Properties.Interp.force_exp_to_term index in
					let pnamed = Logic_const.unamed (Prel(Rge,t,zero_term)) in
					let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
					let root_code_annot_ba = Cil_types.User(code_annotation) in
					Annotations.add kf stmt [Ast.self] root_code_annot_ba;
					(*i<=n-1*)
					begin match info.LiType.size with
					| LiType.CSize(size)->
						begin match size.scache with
						| Not_Computed->Printf.printf "Not_Computed\n";
						| Not_Computable(exn)->Printf.printf "Not_Computable\n";
						| Computed(i)->Printf.printf "Computed\n";
						end;
					| LiType.CTerm(t1)->
						let t = !Db.Properties.Interp.force_exp_to_term index in
						let pnamed = Logic_const.unamed (Prel(Rle,t,t1)) in
						let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
						Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
						let root_code_annot_ba = Cil_types.User(code_annotation) in
						Annotations.add kf stmt [Ast.self] root_code_annot_ba;
					end;
				end;
			with Not_found->();
		in
		
		begin match e.enode with
		| Lval((host,offset))->
			begin match (host,offset) with
			| (Mem(e1),NoOffset)->
				begin match e1.enode with
				| BinOp(op,e2,e3,_)->
					apply_index fmt e2 e3;
				| _->();
				end;
			| _->();
			end;
		| BinOp(op,e1,e2,ty)->
			analysis_exp fmt e1;analysis_exp fmt e2;
		| UnOp(op,e,ty)->
			analysis_exp fmt e;
		| CastE(ty,e)->
			analysis_exp fmt e;
		| _->();
		end
	in

	let rec analysis_stmt s=
		begin match s.skind with
		| Instr(instr)->
			begin match instr with
			| Set(lval,e,_)->
				analysis_exp fmt e;
			| _->();
			end;
		| Loop(_,_,_,_,_)->
			let loop = extract_loop s in
			analysis_exp fmt loop.con;
			List.iter(fun s1->
				analysis_stmt s1;
			)loop.body;
		| Block(b)->
			List.iter(fun s1->
				analysis_stmt s1;
			)b.bstmts;
		| UnspecifiedSequence(seq)->
			let b = Cil.block_from_unspecified_sequence seq in
			List.iter(fun s1->
				analysis_stmt s1;
			)b.bstmts;
		| If(exp,b1,b2,l)->
			analysis_exp fmt exp;
			List.iter(fun s1->
				analysis_stmt s1;
			)b1.bstmts;
			List.iter(fun s1->
				analysis_stmt s1;
			)b2.bstmts;
		| _->();
		end
	in
	analysis_stmt stmt;;

let generate_template fmt kf loop (lvars:Cil_types.varinfo list) (conl:(Cil_types.stmt * Cil_types.exp) list) stmt loc env (ipl:Property.identified_property list ref) wp_compute : Equation.transfer list =	
	let cond = force_exp2tcons loop.con env in  
	let transfers = ref [] in
	let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int 0),Cil_types.IInt,None)) in
	let term_vars = ref (Logic_const.term tnode (Cil_types.Ctype(Cil.intType))) in
	let zero_term = Cil.lzero () in
	let mone_term = Cil.lconstant (My_bigint.of_int (-1)) in(*-1*)
	let ltype = Cil_types.Ctype(Cil.intType) in
	let strfmt = Format.str_formatter in
	
	(*get all valEles in conl*)
	let vars = ref [] in
	List.iter(fun (s,e)->
		let evars = !(LiUtils.extract_valEle_from_exp e) in
		List.iter(fun v->
			LiType.print_valEle fmt v;
			if (List.for_all(fun v1->(LiUtils.compareValele v1 v)==false) (!vars))==true then
			begin
				vars := v::(!vars);
			end;
			();
		)evars;
	)conl;

	(*get min and max value of vars after the loop stmt*)
	let most = ref [] in
	let mini = Big_int.big_int_of_int min_int and maxi = Big_int.big_int_of_int max_int in
	List.iter(fun v->(*valEle*)
		let lv =
			begin match v with
			| LiType.Var(vi)->
				Cil.var vi;
			| LiType.Lval(li)->li;
			end;
		in
		
		let value = !Db.Value.access_after (Kstmt(stmt)) lv in
		begin match value with
		| Cvalue.V.Top(_,_)->
			Printf.printf "Top\n";
		| Cvalue.V.Map(m)->
			Printf.printf "Map\n";
			Cvalue.V.pretty fmt value;Format.print_flush ();Printf.printf "\n";
			try
				let iv = Cvalue.V.project_ival value in(*Ival.t*)
				begin match iv with
				| Ival.Set(set)->Printf.printf "Set\n";
					let min = ref ((Array.get set 0)) and max = ref ((Array.get set 0)) in
					Array.iter(fun i->
						if (My_bigint.lt i (!min))==true then min := i;
						if (My_bigint.gt i (!max))==true then max := i;
					)set;
					most := (v,!min,!max)::!most;
				| Ival.Float(f)->Printf.printf "Float\n";
				| Ival.Top(to1,to2,t1,t2)->Printf.printf "Top\n";(*interval;to1--min,to2--max*)
					try
					begin match to1,to2 with
					| Some(i1),Some(i2)->
						Printf.printf "to1=%s,to2=%s\n" (My_bigint.to_string i1) (My_bigint.to_string i2);
						most := (v,i1,i2)::!most;
					| Some(i1),None->
						most := (v,i1,maxi)::!most;
					| None,Some(i2)->
						most := (v,mini,i2)::!most;
					| None,None->Printf.printf "to1 None\n";
						most := (v,mini,maxi)::!most;
					end;
					Printf.printf "\n";
					with Failure "int_of_big_int"->(*two big*)();
				end;
			with Cvalue.V.Not_based_on_null->();
		end;
	)!vars;
	
	(*get step of potential step vars in loop body*)
	let steps = extract_step kf !vars stmt in
	(*get coeff of var in Mult op,both in loop body and conds*)
	let coeffs = Hashtbl.create 3 in
	Printf.printf "lvars.len=%d\n" (List.length lvars);
	List.iter(fun v->
		let name = LiUtils.get_vname v in
		Hashtbl.add coeffs name (ref [(Apron.Coeff.s_of_int 1);
		(Apron.Coeff.s_of_int 0);
		(Apron.Coeff.s_of_int (-1))]);
	)lvars;
	Printf.printf "coeffs.len1=%d\n" (Hashtbl.length coeffs);
	extract_coeff_from_loop coeffs stmt;
	Printf.printf "coeffs.len2=%d\n" (Hashtbl.length coeffs);
	
	List.iter(fun (_,e)->
		let tcons = force_exp2tcons e env in
		
		let t = Logic_utils.expr_to_term false e in
		let pred = match t.term_node with
			| TBinOp(op,t1,t2)->
				begin match op with
				| Eq->Prel(Req,t1,t2);
				| Le->Prel(Rle,t1,t2);
				| Lt->Prel(Rlt,t1,t2);
				| Ge->Prel(Rge,t1,t2);
				| Gt->Prel(Rgt,t1,t2);
				| Ne->Prel(Rneq,t1,t2);
				| _->Ptrue;
				end
			| _->Ptrue;
		in
		
		let pnamed = Logic_const.unamed pred in
		let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
		Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
		let root_code_annot_ba = Cil_types.User(code_annotation) in
		Annotations.add kf stmt [Ast.self] root_code_annot_ba;
		(*if (LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute)==0 then
		begin(*wp cannot prove*)
			transfers := Tcons(cond,tcons,code_annotation,ref true)::!transfers; 
		end;*)
	)conl;
	
	
	(*enumerate the combinations of coeffs and steps. coeffs both in loop body and conds.steps in loop body*)
		(*the form is sum(cof*var)+const?0,? represents >,<,>=,<=,!=,== etc*)
		
	(*var and cof part*)
	(*merge lvars and vars.lvars represents all var in loop body. varhash:name->var*)
	let varhash = Hashtbl.create 3 in
	let avars = ref lvars in
	List.iter(fun valele->
		begin match valele with
		| LiType.Var(v)->
			if (List.for_all(fun v1->v.vid!=v1.vid) !avars)==true then
			begin
				avars := v::(!avars);
			end;
		| LiType.Lval(_)->();
		end;
	)(!vars);
		
	List.iter(fun v->			
		begin match v.vtype with
		| TPtr(_,_)->
			let lv = Cil.new_exp ~loc:loc (Lval(Mem((Cil.evar ~loc:loc v)),NoOffset)) in
			Cil.d_exp strfmt lv;
			let name = Format.flush_str_formatter () in
			Hashtbl.add varhash name v;
			Printf.printf "TPtr:%s\n" name;
		| _->
			Hashtbl.add varhash v.vname v;
		end;
	)(!avars);
		
	let coeffl = ref [] in
	let total = ref 1 and count = ref 0 in	
	Hashtbl.iter(fun name l->
		coeffl := ((ref 0),name,!l)::(!coeffl);
		total := !total*(List.length !l);
	)coeffs;
	
	let len = List.length !coeffl in
	Printf.printf "total=%d\n" !total;
	if len>0 then
	begin		
		let cof_to_int c =(*maybe exist problem*)
			Apron.Coeff.print strfmt c;
			int_of_string (Format.flush_str_formatter ());
		in
		
		let template_size = 2 in
		while !count<(!total) do
			let com = ref [] in
			
			for i=0 to (len-1) do
				let (indexi,name,li) = List.nth !coeffl i in
				let c = List.nth li !indexi in
				if (cof_to_int c)!=0 then
				begin
					com := (name,c)::(!com);
				end;
				indexi := !indexi+1;
				
				if !indexi==(List.length li) then
				begin
					indexi := 0;
					let rec inc j =
						if j<len then begin
							let (indexj,name,lj) = List.nth !coeffl j in
							indexj := !indexj+1;
							if !indexj==(List.length lj) then
							begin indexj := 0;inc (j+1);end;
						end;
					in
				
					inc (i+1);
				end;				
			done;
			
			Printf.printf "com:";
			
			(*make cons*)
			let lterm = ref [] in
			let vars = ref [||] in
			let cofs = ref [||] in
			let cofl = ref [] in
			let term_vars = ref zero_term in
			let const_min = ref Big_int.zero_big_int and const_max = ref Big_int.zero_big_int in
			
			if (List.length !com)<=template_size then
			begin
			List.iter(fun (name,c)->
				Printf.printf "name:%s\n" name;
				let v = Hashtbl.find varhash name in
				begin match v.vtype with
				| TArray _->();
				| _->
				let lv = Cil.cvar_to_lvar v in
				let tnode = TLval((TVar(lv),TNoOffset)) in
				let tvar = Logic_const.term tnode ltype in				
				
				if (cof_to_int c)!=0 then
				begin
					let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int (cof_to_int c)),Cil_types.IInt,None)) in
					let tcof = Logic_const.term tnode ltype in				
				
					let tnode = TBinOp(Mult,tcof,tvar) in
					lterm := !lterm@[Logic_const.term tnode ltype];
				
					let lval = Cil.var v in
			
					(*sum of steps of var v.vname??*)
					try
						let step = Hashtbl.find steps name in			
						List.iter(fun c->
							const_min := Big_int.add_big_int !const_min (Big_int.big_int_of_int c);
							const_max := Big_int.add_big_int !const_max (Big_int.big_int_of_int c);
						)(!step);
					with Not_found->Printf.printf "Not_found:";Cil.d_var fmt v;Format.print_flush ();Printf.printf "\n";
			
					let mostv = 
						List.find_all (fun (v1,min,max)->
						begin match v1 with
						| LiType.Var(v2)->v2==v
						| LiType.Lval(_)->false
						end;) !most
					in
			
					List.iter(fun (v,min,max)->
						const_min := Big_int.add_big_int !const_min min;
						const_max := Big_int.add_big_int !const_max max;
						Printf.printf ",min=%s,max=%s\n" (My_bigint.to_string min) (My_bigint.to_string max);
					)mostv;
					
				
					Printf.printf "env var name:%s\n" name;
					let av = Apron.Var.of_string name in
					vars := Array.append !vars [|av|];
					cofs := Array.append !cofs [|Apron.Var.of_string (name^"cof")|];

					cofl := (c,av)::!cofl;
					end;
				end;
					
					
			)(!com);
			Printf.printf "\n";
			
			(*constant part*)
			let tnode_min = Cil_types.TConst(Cil_types.CInt64(!const_min,Cil_types.IInt,None)) in
			let tnode_max = Cil_types.TConst(Cil_types.CInt64(!const_max,Cil_types.IInt,None)) in
			let tcon_min = Logic_const.term tnode_min ltype in
			let tcon_max = Logic_const.term tnode_max ltype in
	
			(*make sum to get the last term being the form above.we can create [code_annotation] with this term*)
			if (List.length !lterm)>0 then
			begin
			term_vars := List.nth !lterm 0;(*remove zero_term*)
			for i=1 to ((List.length !lterm)-1) do
				let t = List.nth !lterm i in
				term_vars := Logic_const.term (TBinOp(PlusA,!term_vars,t)) ltype;
			done;(*(!lterm@[tcon_max]);*)
			Printf.printf "term_vars:";Cil.d_term fmt (!term_vars);Format.print_flush ();Printf.printf "\n";
			
			Printf.printf "len=%d\n" len;
			let new_env = Apron.Environment.make (!vars) (!cofs) in
			let tab = Apron.Lincons1.array_make new_env len in
			let expr = Apron.Linexpr1.make new_env in
			
			
			let mk_lincons =
				if (Big_int.ge_big_int !const_max (Big_int.big_int_of_int max_int))==false then
				begin
					let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_max)) ltype in
					let pred = Prel(Rgt,term,zero_term) in(**>*)
					Apron.Linexpr1.set_array expr (Array.of_list !cofl)
					(Some (Apron.Coeff.s_of_int (Big_int.int_of_big_int !const_max)))(*constant part*)
					;
					let cons = Apron.Lincons1.make expr Apron.Lincons1.SUP in
					Apron.Lincons1.array_set tab 0 cons;
			
					let pnamed = Logic_const.unamed pred in
					let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
					Printf.printf "annota5:";Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
					let root_code_annot_ba = Cil_types.User(code_annotation) in
					Annotations.add kf stmt [Ast.self] root_code_annot_ba;
					if (LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute)==0 then
					begin(*wp cannot prove*)
						Apron.Lincons1.array_set tab 0 cons;(*0-index*)
						transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
						
						let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_max)) ltype in
						let pred = Prel(Rge,term,zero_term) in(**>=*)
						Apron.Linexpr1.set_array expr (Array.of_list !cofl)
						(Some (Apron.Coeff.s_of_int (Big_int.int_of_big_int !const_max)))(*constant part*)
						;
						let cons = Apron.Lincons1.make expr Apron.Lincons1.SUPEQ in
						Apron.Lincons1.array_set tab 0 cons;
					
						let pnamed = Logic_const.unamed pred in
						let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
					Printf.printf "annota6:";Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
						let root_code_annot_ba = Cil_types.User(code_annotation) in
						Annotations.add kf stmt [Ast.self] root_code_annot_ba;
						if (LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute)==0 then
						begin(*wp cannot prove*)
							Apron.Lincons1.array_set tab 0 cons;(*0-index*)
							transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
							
							let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_max)) ltype in
							let pred = Prel(Rneq,term,zero_term) in(**!=*)
							Apron.Linexpr1.set_array expr (Array.of_list !cofl)
							(Some (Apron.Coeff.s_of_int (Big_int.int_of_big_int !const_max)))(*constant part*)
							;
							let cons = Apron.Lincons1.make expr Apron.Lincons1.DISEQ in
							Apron.Lincons1.array_set tab 0 cons;
						
							let pnamed = Logic_const.unamed pred in
							let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
						Printf.printf "annota2:";Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
							let root_code_annot_ba = Cil_types.User(code_annotation) in
							Annotations.add kf stmt [Ast.self] root_code_annot_ba;
							if (LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute)==0 then
							begin(*wp cannot prove*)
								Apron.Lincons1.array_set tab 0 cons;(*0-index*)
								transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
								
								let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_max)) ltype in
								let pred = Prel(Req,term,zero_term) in(**==*)
								Apron.Linexpr1.set_array expr (Array.of_list !cofl)
								(Some (Apron.Coeff.s_of_int (Big_int.int_of_big_int !const_max)))(*constant part*)
								;
								let cons = Apron.Lincons1.make expr Apron.Lincons1.EQ in
								Apron.Lincons1.array_set tab 0 cons;

								let pnamed = Logic_const.unamed pred in
								let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
								Printf.printf "annota1:";Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
								let root_code_annot_ba = Cil_types.User(code_annotation) in
								Annotations.add kf stmt [Ast.self] root_code_annot_ba;
								if (LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute)==0 then
								begin(*wp cannot prove*)
									Apron.Lincons1.array_set tab 0 cons;(*0-index*)
									transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
								end;
							end;
						end;
					end;
				end;
					
				if (Big_int.eq_big_int !const_min !const_max)==false then
				begin		
					if (Big_int.gt_big_int !const_min (Big_int.big_int_of_int min_int))==true then
					begin
					let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_min)) ltype in
					let pred = Prel(Rgt,term,zero_term) in(**>*)
					Apron.Linexpr1.set_array expr (Array.of_list !cofl)
					(Some (Apron.Coeff.s_of_int (Big_int.int_of_big_int !const_min)))(*constant part*)
					;
					let cons = Apron.Lincons1.make expr Apron.Lincons1.SUP in
					Apron.Lincons1.array_set tab 0 cons;
					
					let pnamed = Logic_const.unamed pred in
					let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
					Printf.printf "annota7:";Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
					let root_code_annot_ba = Cil_types.User(code_annotation) in
					Annotations.add kf stmt [Ast.self] root_code_annot_ba;
					if (LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute)==0 then
					begin(*wp cannot prove*)
						Apron.Lincons1.array_set tab 0 cons;(*0-index*)
						transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
					
						let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_min)) ltype in
						let pred = Prel(Rge,term,zero_term) in(**>=*)
						Apron.Linexpr1.set_array expr (Array.of_list !cofl)
						(Some (Apron.Coeff.s_of_int (Big_int.int_of_big_int !const_min)))(*constant part*)
						;
						let cons = Apron.Lincons1.make expr Apron.Lincons1.SUPEQ in
						Apron.Lincons1.array_set tab 0 cons;
					
						let pnamed = Logic_const.unamed pred in
						let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
					Printf.printf "annota8:";Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
						let root_code_annot_ba = Cil_types.User(code_annotation) in
						Annotations.add kf stmt [Ast.self] root_code_annot_ba;
						if (LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute)==0 then
						begin(*wp cannot prove*)
							Apron.Lincons1.array_set tab 0 cons;(*0-index*)
							transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
							
							let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_min)) ltype in
							let pred = Prel(Rneq,term,zero_term) in(*!=*)
							Apron.Linexpr1.set_array expr (Array.of_list !cofl)
							(Some (Apron.Coeff.s_of_int (Big_int.int_of_big_int !const_min)))(*constant part*)
							;
							let cons = Apron.Lincons1.make expr Apron.Lincons1.EQ in
							Apron.Lincons1.array_set tab 0 cons;
					
							let pnamed = Logic_const.unamed pred in
							let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
							Printf.printf "annota3:";Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
							let root_code_annot_ba = Cil_types.User(code_annotation) in
							Annotations.add kf stmt [Ast.self] root_code_annot_ba;
							if (LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute)==0 then
							begin(*wp cannot prove*)
								Apron.Lincons1.array_set tab 0 cons;(*0-index*)
								transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
						
								(*Rneq*)
								let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_min)) ltype in
								let pred = Prel(Req,term,zero_term) in(*==*)
								Apron.Linexpr1.set_array expr (Array.of_list !cofl)
								(Some (Apron.Coeff.s_of_int (Big_int.int_of_big_int !const_min)))(*constant part*)
								;
								let cons = Apron.Lincons1.make expr Apron.Lincons1.DISEQ in
								Apron.Lincons1.array_set tab 0 cons;
						
								let pnamed = Logic_const.unamed pred in
								let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
							Printf.printf "annota4:";Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
								let root_code_annot_ba = Cil_types.User(code_annotation) in
								Annotations.add kf stmt [Ast.self] root_code_annot_ba;
								if (LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute)==0 then
								begin(*wp cannot prove*)
									Apron.Lincons1.array_set tab 0 cons;(*0-index*)
									transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
								end;
							end;
						end;
					end;
				end;
			end;
			(*| Apron.Lincons1.EQMOD(_)->
					let rterm = Logic_const.term (TBinOp(Mod,!term,zero_term)) (Cil_types.Ctype(Cil.intType)) in
					let pred = Prel(Req,!term,rterm) in(*%=*)
					let cons = Apron.Lincons1.make expr Apron.Lincons1.EQ in(*EQMOD*)
					Apron.Lincons1.array_set tab 0 cons;(pred,cons);*)
			in
			
			
			(*apply typ*)				
			mk_lincons;
			
			end;
			end;
			
			count := !count+1;
		done;
	end;
		
	Printf.printf "generate over\n";
	!transfers;;
