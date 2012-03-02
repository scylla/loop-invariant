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
			(*update [names]??*)
			Hashhe.add avar2cvar avar var;
		| TFloat(_,_)->
			let avar = (Apron.Var.of_string var.vname) in
			lreal := avar::!lreal;
			Hashhe.add avar2cvar avar var;
		| TPtr(tp,attr)->(*pointer,how to?*)
			Cil.d_var Format.std_formatter var;Format.print_flush ();Printf.printf "\n";
			let avar = (Apron.Var.of_string var.vname) in
			lint := avar::!lint;
			Hashhe.add avar2cvar avar var;
		| TArray(tp,eo,size,attr)->
			begin match eo with
			| Some(e)->
				let avar = (Apron.Var.of_string var.vname) in
				lint := avar::!lint;
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
			Cil.d_binop Format.std_formatter op;Format.print_flush ();Printf.printf "\n";
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
			TypePrinter.print_exp_type Format.std_formatter exp;
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
		Printf.printf "Lval in force_exp_to_texp:\n";
		begin match host with
		| Mem(m)->
			Cil.d_exp Format.std_formatter m;Format.print_flush ();Printf.printf "\n";
			TypePrinter.print_exp_type Format.std_formatter m;Format.print_flush ();Printf.printf "\nEnd mem\n";
		| Var(v)->();
		end;
		Apron.Texpr1.Var(Apron.Var.of_string "unknownEnode")
	|_->
		Printf.printf "unknownEnode\n";
		TypePrinter.print_exp_type Format.std_formatter exp;
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
	| Loop(_,b,_,_,_)->
		let con_stmt = List.nth b.bstmts 1 in
		let body_stmt = ref [] in
		for i=2 to ((List.length b.bstmts)-1) do
			body_stmt := !body_stmt@[List.nth b.bstmts i];
		done;
		(match con_stmt.skind with
		| If(con,_,_,_)->
			{Equation.con=con;Equation.body=(!body_stmt)};
		| _->
			let con = Cil.dummy_exp (Cil_types.Const(Cil_types.CStr("dummy_con"))) in
			let body_stmt = Cil.dummyStmt in
			{Equation.con=con;Equation.body = [body_stmt]};
		);
	| _->
		let con = Cil.dummy_exp (Cil_types.Const(Cil_types.CStr("dummy_con"))) in
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
				let l = extract_const_from_exp (Some(lv)) e in
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
	
	(*let vars = dec.sformals@dec.slocals in*)
	let pdg = (!Db.Pdg.get) kf in
	(!Db.Pdg.extract) pdg ("/home/lzh/pdg_"^fname^".dot");
	
	let vlist = LiPdg.find_vnodes vars pdg in
	let blist = LiPdg.find_bnodes dec.sbody pdg in
			
	begin match stmt.skind with
	| Loop(_,b,_,_,_)->
		let llist = LiPdg.find_bnodes b pdg in
			
		List.iter(fun node->
			Printf.printf "pretty_node:";(!Db.Pdg.pretty_node) false fmt node;Format.print_flush ();Printf.printf "\n";
			let nodes = (!Db.Pdg.all_uses) pdg [node] in
			List.iter(fun n->
				if (List.exists (fun n1->n1==n;) llist)==true then
				begin
					let s = PdgTypes.Node.stmt n in
					begin match s with
					| Some(s1)->
						extract_const_from_stmt steps s1;
					| None->();
					end;
				end;
			)nodes;
		)vlist;
	| _->();
	end;
	!steps;;

let rec extract_coeff_from_exp e =
	let ltype = Cil_types.Ctype(Cil.intType) in(*temporary*)
	begin match e.enode with
	| Const(c)->
		begin match c with
		| CInt64(big,_,_)->
			[Apron.Coeff.s_of_int (My_bigint.to_int big)];
		| CReal(f,_,_)->
			[Apron.Coeff.s_of_float f];
		| _->[];(*or 1?*)
		end;
		(*let tnode = Cil_types.TConst(c) in
		Logic_const.term tnode ltype;*)(*can be used as cof.return Cof.t directly?*)
	| Lval((host,offset))->[];
		(*begin match host with
		| Var(v)->
			let lv = Cil.cvar_to_lvar v in
			let tnode = TLval((TVar(lv),TNoOffset)) in
			Logic_const.term tnode ltype;(*can be used as Var*)
		| Mem(e1)->
			extract_term e1;
		end;*)
	| BinOp(op,e1,e2,_)->
		(extract_coeff_from_exp e1)@(extract_coeff_from_exp e2);
	| UnOp(op,e1,_)->
		extract_coeff_from_exp e1;
	| _->[];
		(*let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int 0),Cil_types.IInt,None)) in
		Logic_const.term tnode ltype;*)
	end;;

(*stmt is a [loop] stmt. this deals with array access operations in loop body*)
let generate_array fmt kf (arrayvars:LiType.array_info list) stmt =
	let exps = ref [] in
	
	let rec analysis_exp fmt e =
		(*when access an array element,these should be held*)
		let apply_index fmt base index =
			Printf.printf "arrayvars.len=%d\n" (List.length arrayvars);
			List.iter(fun info->
				Cil.d_var fmt info.LiType.v;Format.print_flush ();Printf.printf "\n";
			)arrayvars;
			Printf.printf "base.name=%s\n" (LiUtils.get_exp_name base);
			try
				let info = List.find (fun info->(String.compare info.LiType.v.vname (LiUtils.get_exp_name base))==0) arrayvars in
				if (List.for_all (fun e->(Cil.compareExp e index)==false) !exps)==true then
				begin
					begin match info.LiType.size.scache with
					| Not_Computed->Printf.printf "Not_Computed\n";
					| Not_Computable(exn)->Printf.printf "Not_Computable\n";
					| Computed(i)->Printf.printf "Computed\n";
					end;
					exps := index::(!exps);
					let zero_term = Cil.lzero () in
					let t = !Db.Properties.Interp.force_exp_to_term index in
					let pnamed = Logic_const.unamed (Prel(Rge,t,zero_term)) in
					let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
					Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
					let root_code_annot_ba = Cil_types.User(code_annotation) in
					Annotations.add kf stmt [Ast.self] root_code_annot_ba;
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

let generate_template fmt kf loop (lvars:Cil_types.varinfo list) (conl:(Cil_types.stmt * Cil_types.exp) list) stmt env (ipl:Property.identified_property list ref) wp_compute : Equation.transfer list =	
	let cond = force_exp2tcons loop.con env in  
	let transfers = ref [] in
	let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int 0),Cil_types.IInt,None)) in
		(*let tvnode = Cil_types.TLval((Cil_types.TVar v),TNoOffset) in*)
	let term_vars = ref (Logic_const.term tnode (Cil_types.Ctype(Cil.intType))) in
	let zero_term = Cil.lzero () in(*Logic_utils.mk_dummy_term tnode Cil.intType in*)
	let mone_term = Cil.lconstant (My_bigint.of_int (-1)) in(*-1*)
	let ltype = Cil_types.Ctype(Cil.intType) in
	
	(*get all vars in conl*)
	let vars = ref [] in
	List.iter(fun (s,e)->
		let evars = !(LiUtils.extract_valEle_from_exp e) in
		List.iter(fun v->
			if (List.exists(fun v1->v1==v) !vars)==false then
			begin
				vars := v::!vars;
			end;
		)evars;
	)conl;

	(*get min and max value of vars after the loop stmt*)
	let most = ref [] in
	let mini = min_int and maxi = max_int in
	Printf.printf "mini=%d,maxi=%d\n" mini maxi;
	Printf.printf "value node len=%d\n" (List.length !vars);
	List.iter(fun v->
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
			let iv = Cvalue.V.project_ival value in(*Ival.t*)
			begin match iv with
			| Ival.Set(set)->Printf.printf "Set\n";
				let min = ref (My_bigint.to_int (Array.get set 0)) and max = ref (My_bigint.to_int (Array.get set 0)) in
				Array.iter(fun i->
					let j = My_bigint.to_int i in
					if j<(!min) then min := j;
					if j>(!max) then max := j;
					Printf.printf "%d," j;
				)set;
				Printf.printf "\n";
				most := (v,!min,!max)::!most;
			| Ival.Float(f)->Printf.printf "Float\n";
			| Ival.Top(to1,to2,t1,t2)->Printf.printf "Top\n";(*interval;to1--min,to2--max*)
				begin match to1,to2 with
				| Some(i1),Some(i2)->Printf.printf "to1=%d,to2=%d\n" (My_bigint.to_int i1) (My_bigint.to_int i2);
					most := (v,(My_bigint.to_int i1),(My_bigint.to_int i2))::!most;
				| Some(i1),None->
					most := (v,(My_bigint.to_int i1),maxi)::!most;
				| None,Some(i2)->
					most := (v,mini,(My_bigint.to_int i2))::!most;
				| None,None->Printf.printf "to1 None\n";
					most := (v,mini,maxi)::!most;
				end;
				Printf.printf "%d," (My_bigint.to_int t1);Printf.printf "%d" (My_bigint.to_int t2);
				Printf.printf "\n";
			end;
		end;
	)!vars;
	
	(*get step of potential step vars*)
	let steps = extract_step kf !vars stmt in	Printf.printf "after extract_step\n";
	let coeffs = ref [] and consts = ref [] in
	
	List.iter(fun (_,e)->
		coeffs := (extract_coeff_from_exp e)@(!coeffs);Printf.printf "after extract_coeff_from_exp\n";
		consts := (extract_const_from_exp None e)@(!consts);
		Printf.printf "after extract_const_from_exp\n";
		let tcons = force_exp2tcons e env in
		Printf.printf "after force_exp2tcons to get tcons\n";
		
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
		if (LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute)==0 then
		begin(*wp cannot prove*)
			transfers := Tcons(cond,tcons,code_annotation,ref true)::!transfers; 
		end;
	)conl;
	
	List.iter2(fun cof (lvo,const)->(*here lvo is None*)
		let lterm = ref [] in
		let const_min = ref 0 and const_max = ref 0 in
		(*the form is sum(cof*var)+const?0,? represents >,<,>=,<=,!=,== etc*)
		(*var and cof part*)
		Printf.printf "lvar.len=%d\n" (List.length lvars);
		List.iter(fun v->
			let lv = Cil.cvar_to_lvar v in
			let tnode = TLval((TVar(lv),TNoOffset)) in
			let tvar = Logic_const.term tnode ltype in
		
			(*now the cofs are all -1*)
			let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int (1)),Cil_types.IInt,None)) in
			let tcof = Logic_const.term tnode ltype in
		
			let tnode = TBinOp(Mult,tcof,tvar) in
			lterm := !lterm@[Logic_const.term tnode ltype];
			
			let lval = Cil.var v in
			let step = List.find_all (fun (lv,c)->
				begin match lv with
				| Some(lv1)->
					Cil.compareLval lval lv1;
				| _->false;
				end;
				) steps
			in
			let mostv = 
				List.find_all (fun (v1,min,max)->
				begin match v1 with
				| LiType.Var(v2)->v2==v
				| LiType.Lval(_)->false
				end;) !most
			in
			
			List.iter(fun (_,c)->
				const_min := !const_min+c;
				const_max := !const_max+c;
			)step;
			List.iter(fun (v,min,max)->
				const_min := !const_min+min;
				const_max := !const_max+max;
				Printf.printf ",min=%d,max=%d\n" min max;
			)mostv;
		)lvars;
	
		(*constant part*)
		let tnode_min = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int (!const_min)),Cil_types.IInt,None)) in
		let tnode_max = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int (!const_max)),Cil_types.IInt,None)) in
		let tcon_min = Logic_const.term tnode_min ltype in
		let tcon_max = Logic_const.term tnode_max ltype in
	
		(*make sum to get the last term being the form above.we can create [code_annotation] with this term*)
		List.iter(fun t->
			term_vars := Logic_const.term (TBinOp(PlusA,!term_vars,t)) ltype;
		)(!lterm);(*(!lterm@[tcon_max]);*)
		
		(*make cons*)
		let vars = ref [||] in
		let cofs = ref [||] in
		List.iter(fun v->
			vars := Array.append !vars [|Apron.Var.of_string v.vname|];
			cofs := Array.append !cofs [|Apron.Var.of_string ((v.vname)^"cof")|];
		)lvars;

		let new_env = Apron.Environment.make (!vars) (!cofs) in
		  
		let cofl = ref [] in
		let len = (Array.length !vars)-1 in
		(*now the cofs are all -1*)
		for i=0 to len do
		 	cofl := (Apron.Coeff.s_of_int (1), !vars.(i))::!cofl;
		done;
		
		let tab = Apron.Lincons1.array_make new_env len in
		let expr = Apron.Linexpr1.make new_env in
		
		
		let mk_lincons typ =
			let result = ref [] in
			begin match typ with
			| Req->(*all two?*)
				let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_max)) ltype in
				let pred = Prel(Req,term,zero_term) in
				Apron.Linexpr1.set_array expr (Array.of_list !cofl)
				(Some (Apron.Coeff.s_of_int (!const_max)))(*constant part*)
				;
				let cons = Apron.Lincons1.make expr Apron.Lincons1.EQ in
				Apron.Lincons1.array_set tab 0 cons;
				result := (pred,cons)::(!result);
				
				let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_min)) ltype in
				let pred = Prel(Req,term,zero_term) in
				Apron.Linexpr1.set_array expr (Array.of_list !cofl)
				(Some (Apron.Coeff.s_of_int (!const_min)))(*constant part*)
				;
				let cons = Apron.Lincons1.make expr Apron.Lincons1.EQ in
				Apron.Lincons1.array_set tab 0 cons;
				result := (pred,cons)::(!result);
				
				!result;
			| Rge->
				let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_max)) ltype in
				let pred = Prel(Rge,term,zero_term) in
				Apron.Linexpr1.set_array expr (Array.of_list !cofl)
				(Some (Apron.Coeff.s_of_int (!const_max)))(*constant part*)
				;
				let cons = Apron.Lincons1.make expr Apron.Lincons1.SUPEQ in
				Apron.Lincons1.array_set tab 0 cons;
				result := (pred,cons)::(!result);
				
				let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_min)) ltype in
				let pred = Prel(Rge,term,zero_term) in
				Apron.Linexpr1.set_array expr (Array.of_list !cofl)
				(Some (Apron.Coeff.s_of_int (!const_min)))(*constant part*)
				;
				let cons = Apron.Lincons1.make expr Apron.Lincons1.SUPEQ in
				Apron.Lincons1.array_set tab 0 cons;
				result := (pred,cons)::(!result);
				
				!result;
			| Rgt->
				let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_max)) ltype in
				let pred = Prel(Rgt,term,zero_term) in
				Apron.Linexpr1.set_array expr (Array.of_list !cofl)
				(Some (Apron.Coeff.s_of_int (!const_max)))(*constant part*)
				;
				let cons = Apron.Lincons1.make expr Apron.Lincons1.SUP in
				Apron.Lincons1.array_set tab 0 cons;
				result := (pred,cons)::(!result);
				
				let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_min)) ltype in
				let pred = Prel(Rgt,term,zero_term) in
				Apron.Linexpr1.set_array expr (Array.of_list !cofl)
				(Some (Apron.Coeff.s_of_int (!const_min)))(*constant part*)
				;
				let cons = Apron.Lincons1.make expr Apron.Lincons1.SUP in
				Apron.Lincons1.array_set tab 0 cons;
				result := (pred,cons)::(!result);
				
				!result;
			| Rneq->(*all two?*)
				let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_max)) ltype in
				let pred = Prel(Rneq,term,zero_term) in
				Apron.Linexpr1.set_array expr (Array.of_list !cofl)
				(Some (Apron.Coeff.s_of_int (!const_max)))(*constant part*)
				;
				let cons = Apron.Lincons1.make expr Apron.Lincons1.DISEQ in
				Apron.Lincons1.array_set tab 0 cons;
				result := (pred,cons)::(!result);				
				
				let term = Logic_const.term (TBinOp(PlusA,!term_vars,tcon_min)) ltype in
				let pred = Prel(Rneq,term,zero_term) in
				Apron.Linexpr1.set_array expr (Array.of_list !cofl)
				(Some (Apron.Coeff.s_of_int (!const_min)))(*constant part*)
				;
				let cons = Apron.Lincons1.make expr Apron.Lincons1.DISEQ in
				Apron.Lincons1.array_set tab 0 cons;
				result := (pred,cons)::(!result);
				
				!result;
			| Rle->(*neg term*)
				let term = Logic_const.term (TBinOp(MinusA,!term_vars,tcon_max)) ltype in
				let pred = Prel(Rle,term,zero_term) in
				Apron.Linexpr1.set_array expr (Array.of_list !cofl)
				(Some (Apron.Coeff.s_of_int (-(!const_max))))(*constant part*)
				;
				let cons = Apron.Lincons1.make (negate_linexpr expr) Apron.Lincons1.SUPEQ in
				Apron.Lincons1.array_set tab 0 cons;
				result := (pred,cons)::(!result);
				
				let term = Logic_const.term (TBinOp(MinusA,!term_vars,tcon_min)) ltype in
				let pred = Prel(Rle,term,zero_term) in
				Apron.Linexpr1.set_array expr (Array.of_list !cofl)
				(Some (Apron.Coeff.s_of_int (-(!const_min))))(*constant part*)
				;
				let cons = Apron.Lincons1.make (negate_linexpr expr) Apron.Lincons1.SUPEQ in
				Apron.Lincons1.array_set tab 0 cons;
				result := (pred,cons)::(!result);
				
				!result;
			| Rlt->
				let term = Logic_const.term (TBinOp(MinusA,!term_vars,tcon_max)) ltype in
				let pred = Prel(Rlt,term,zero_term) in
				Apron.Linexpr1.set_array expr (Array.of_list !cofl)
				(Some (Apron.Coeff.s_of_int (-(!const_max))))(*constant part*)
				;
				let cons = Apron.Lincons1.make (negate_linexpr expr) Apron.Lincons1.SUP in
				Apron.Lincons1.array_set tab 0 cons;
				result := (pred,cons)::(!result);
				
				let term = Logic_const.term (TBinOp(MinusA,!term_vars,tcon_min)) ltype in
				let pred = Prel(Rlt,term,zero_term) in
				Apron.Linexpr1.set_array expr (Array.of_list !cofl)
				(Some (Apron.Coeff.s_of_int (-(!const_min))))(*constant part*)
				;
				let cons = Apron.Lincons1.make (negate_linexpr expr) Apron.Lincons1.SUP in
				Apron.Lincons1.array_set tab 0 cons;
				result := (pred,cons)::(!result);
				
				!result;
			(*| Apron.Lincons1.EQMOD(_)->
				let rterm = Logic_const.term (TBinOp(Mod,!term,zero_term)) (Cil_types.Ctype(Cil.intType)) in
				let pred = Prel(Req,!term,rterm) in(*%=*)
				let cons = Apron.Lincons1.make expr Apron.Lincons1.EQ in(*EQMOD*)
				Apron.Lincons1.array_set tab 0 cons;(pred,cons);*)
			end
		in
				
    List.iter(fun typ->
    	let result = mk_lincons typ in
    	List.iter(fun (pred,cons)->
				let pnamed = Logic_const.unamed pred in
				let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
				let root_code_annot_ba = Cil_types.User(code_annotation) in
				Annotations.add kf stmt [Ast.self] root_code_annot_ba;
				if (LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute)==0 then
				begin(*wp cannot prove*)
					Apron.Lincons1.array_set tab 0 cons;(*0-index*)
					transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
				end;
			)result;
		)[Req;Rge;Rgt;Rneq;Rle;Rlt];
	)!coeffs !consts;
	Printf.printf "generate over\n";
	!transfers;;
