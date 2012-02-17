open Cil
open Cil_types
open LiVisitor
open LiAnnot
open Li_utils
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
		if (List.for_all (fun vn->vn==var.vname;) !names)==true then
		(
		match var.vtype with
		| TInt(_,_)->
			let avar = (Apron.Var.of_string var.vname) in
			lint := avar::!lint;
			Hashhe.add avar2cvar avar var;
		| TFloat(_,_)->
			let avar = (Apron.Var.of_string var.vname) in
			lreal := avar::!lreal;
			Hashhe.add avar2cvar avar var;
		| _->();
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
      
let rec force_exp_to_texp (exp:Cil_types.exp) :Apron.Texpr1.expr =
	match exp.enode with
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
		| Le->
			Apron.Texpr1.Binop(Apron.Texpr1.Sub,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		| Eq->
			Apron.Texpr1.Binop(Apron.Texpr1.Sub,te1,te2,Apron.Texpr1.Real,Apron.Texpr1.Down)
		|_->
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
			(*Printf.printf "unknownUnOp\n";
			TypePrinter.print_exp_type Format.std_formatter exp;
			Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";*)
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
	| Lval((host,offset))->
		(match host with
		| Var(v)->
			Apron.Texpr1.Var(Apron.Var.of_string v.vname);
		| Mem(e)->
			force_exp_to_texp e;
		);
	| CastE(ty,e)->
		force_exp_to_texp e;(*not exactly right*)
	|_->
		(*Printf.printf "unknownEnode\n";
		TypePrinter.print_exp_type Format.std_formatter exp;
		Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";*)
		Apron.Texpr1.Var(Apron.Var.of_string "unknownEnode")
		  

let force_exp2tcons (e:Cil_types.exp) env: Apron.Tcons1.t =
	let texpr = force_exp_to_texp e in
	let vars = Li_utils.extract_varinfos_from_exp e in
	let lvars = Cil_datatype.Varinfo.Set.elements vars in
	(*let env = add_env env lvars in*)
	let texpr = Apron.Texpr1.of_expr env texpr in
	(match e.enode with
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
	| _->Apron.Tcons1.make texpr Apron.Tcons1.EQ;)
	
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
	
let generate_template fmt kf loop (lvars:Cil_types.varinfo list) (conl:Cil_types.exp list) stmt env (ipl:Property.identified_property list ref) wp_compute =
	
	let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int 0),Cil_types.IInt,None)) in
		(*let tvnode = Cil_types.TLval((Cil_types.TVar v),TNoOffset) in*)
	let term = ref (Logic_utils.mk_dummy_term tnode Cil.intType) in
	let lterm = ref [] in
	let zero_term = Logic_utils.mk_dummy_term tnode Cil.intType in
	let ltype = Cil_types.Ctype(Cil.intType) in
	
	List.iter(fun e->
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
		();Annotations.add kf stmt [Ast.self] root_code_annot_ba;
		LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute;
	)conl;
	
	List.iter(fun v->
		let lv = Cil.cvar_to_lvar v in
		let tnode = TLval((TVar(lv),TNoOffset)) in
		let tvar = Logic_const.term tnode ltype in
		
		let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int (-1)),Cil_types.IInt,None)) in
		let tcof = Logic_const.term tnode ltype in
		
		let tnode = TBinOp(Mult,tcof,tvar) in
		lterm := !lterm@[Logic_const.term tnode ltype];
	)lvars;
	
	let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int 30),Cil_types.IInt,None)) in
	let tcon = Logic_const.term tnode ltype in
	lterm := !lterm@[tcon];
	
	List.iter(fun t->
		term := Logic_const.term (TBinOp(PlusA,!term,t)) ltype;
	)!lterm;
	
	let pred = Prel(Rge,!term,zero_term) in
	(*let pred = ref Ptrue in
		(match tp with(*cannot be all zero_term*)
		| Apron.Lincons1.EQ->
			pred := Prel(Req,!term,zero_term);
		| Apron.Lincons1.SUPEQ->
			pred := Prel(Rge,!term,zero_term);
		| Apron.Lincons1.SUP->
			pred := Prel(Rgt,!term,zero_term);
		| Apron.Lincons1.DISEQ->
			pred := Prel(Rneq,!term,zero_term);
		| Apron.Lincons1.EQMOD(_)->
			let rterm = Logic_utils.mk_dummy_term (TBinOp(Mod,!term,zero_term)) Cil.intType in
			pred := Prel(Req,!term,rterm);(*%=*)
		);*)
    
	let pnamed = Logic_const.unamed pred in
	let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
  
	let cond = force_exp2tcons loop.con env in  
          
	let vars = ref [||] in
	let cofs = ref [||] in
	List.iter(fun v->
		Cil.d_type fmt v.vtype;Format.print_flush ();Printf.printf "\n";
		vars := Array.append !vars [|Apron.Var.of_string v.vname|];
		cofs := Array.append !cofs [|Apron.Var.of_string ((v.vname)^"cof")|];
	)lvars;

		let new_env = Apron.Environment.make (!vars) (!cofs) in
    
    let cofl = ref [] in
    let len = (Array.length !vars)-1 in
    for i=0 to len do
    	cofl := (Apron.Coeff.s_of_int (-1), !vars.(i))::!cofl;
    done;
    
    let tab = Apron.Lincons1.array_make new_env len in
    let expr = Apron.Linexpr1.make new_env in
    Apron.Linexpr1.set_array expr (Array.of_list !cofl)
    (Some (Apron.Coeff.s_of_int 30))(*must be a valid argument*)
    ;
    let cons = Apron.Lincons1.make expr Apron.Lincons1.SUP in
  	Apron.Lincons1.array_set tab 0 cons;(*0-index*)
		Lcons(cond,cons,code_annotation,ref true);;
