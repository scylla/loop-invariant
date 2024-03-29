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

let extract_coeff_from_funspec coeffs kf =
	let strfmt = Format.str_formatter in
	let funspec = Kernel_function.get_spec kf in
	let rec get_coeff_from_term t =
		begin match t.term_node with
		| TConst(_)->();
		| TLval(_)->();
		| TBinOp(op,t3,t4)->
			begin match op with
			| Mult->
				begin match t3.term_node,t4.term_node with
				| TConst(cons),TLval(tl)|TLval(tl),TConst(cons)->
					Cil.d_term_lval strfmt tl;
					let name = Format.flush_str_formatter () in
								
					begin match cons with
					| CInt64(big,_,_)->
						begin try
							let res = Hashtbl.find coeffs name in
							if (List.for_all(fun c->(Apron.Coeff.cmp c 
								(Apron.Coeff.s_of_int (My_bigint.to_int big)))!=0) !res)==true then
							res := (Apron.Coeff.s_of_int (My_bigint.to_int big))::(!res);
						with Not_found->
							Hashtbl.add coeffs name (ref [(Apron.Coeff.s_of_int 1);
								(Apron.Coeff.s_of_int 0);
								(Apron.Coeff.s_of_int (-1))]);
						end;
					| CReal(f,_,_)->
						begin try
							let res = Hashtbl.find coeffs name in
							if (List.for_all(fun c->(Apron.Coeff.cmp c (Apron.Coeff.s_of_float f))!=0) !res)==true then
							res := (Apron.Coeff.s_of_float f)::(!res);
						with Not_found->
							Hashtbl.add coeffs name (ref [(Apron.Coeff.s_of_int 1);(*float?*)
								(Apron.Coeff.s_of_int 0);
								(Apron.Coeff.s_of_int (-1))]);
						end;
					| _->();
					end;
					
				| _->();
				end;
				
			| _->();
			end;
		| _->();
		end;
	in
		  
	let rec get_coeff_from_predicate p =
		begin match p with
		 | Prel(_,t1,t2)->
		 	get_coeff_from_term t1;
		 	get_coeff_from_term t2;
		 | _->();
		 end;
	in
		  		
	List.iter(fun b->
	  List.iter(fun ip->
		 	get_coeff_from_predicate ip.ip_content;
		 )b.b_assumes;
		  	
	  List.iter(fun ip->
		 	get_coeff_from_predicate ip.ip_content;
		)b.b_requires;
		  	
		List.iter(fun (_,ip)->
		 get_coeff_from_predicate ip.ip_content;
		)b.b_post_cond;
	)funspec.spec_behavior;;


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
		| TPtr(_,_)->(*pointer,how to?*)
			let name = "*"^var.vname in
			let avar = (Apron.Var.of_string name) in
			lint := avar::!lint;
			names := name::(!names);
			Hashhe.add avar2cvar avar var;
			
			let avar = (Apron.Var.of_string var.vname) in
			lint := avar::!lint;
			names := var.vname::(!names);
			Hashhe.add avar2cvar avar var;
		| TArray(_,eo,_,_)->
			begin match eo with
			| Some(_)->
				let avar = (Apron.Var.of_string var.vname) in
				lint := avar::!lint;
				names := var.vname::(!names);
				Hashhe.add avar2cvar avar var;
			| None->();
			end;
		| _->();
		);
	)lvar;
  Apron.Environment.add env
    (Array.of_list !lint)
    (Array.of_list !lreal)

let add_vars (env:Apron.Environment.t) (lvar:Apron.Var.t list) :Apron.Environment.t =
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
    | Apron.Texpr1.Unop(Apron.Texpr1.Neg,e,_,_) ->
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
	| BinOp(op,e1,e2,_)->
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
	| UnOp(op,e,_)->
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
		| CInt64(i,_,_)->
			if (Big_int.lt_big_int i (Big_int.big_int_of_int max_int))==true then
			begin Apron.Texpr1.Cst(Apron.Coeff.s_of_int (My_bigint.to_int i));end
			else begin Apron.Texpr1.Cst(Apron.Coeff.s_of_int 0);end
		| CReal(f,_,_)->
			Apron.Texpr1.Cst(Apron.Coeff.s_of_float f);
		| _->
			Printf.printf "unknownConst\n";
			TypePrinter.print_exp_type Format.std_formatter exp;
			Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";
			Apron.Texpr1.Var(Apron.Var.of_string "unknownConst");
		)
	| CastE(_,e)->
		force_exp_to_texp e;(*not exactly right*)
	| Lval((host,_))->
		Printf.printf "unknownEnode1 in translate\n";
		begin match host with
		| Mem(_)->
			();(*Cil.d_exp Format.std_formatter m;Format.print_flush ();Printf.printf "\n";*)
		| Var(_)->();
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
			if (Big_int.lt_big_int big (Big_int.big_int_of_int max_int))==true then
			begin	LiType.APScalar(Apron.Scalar.of_int (My_bigint.to_int big));end
			else begin LiType.APScalar(Apron.Scalar.of_int 0);end;
		| CReal(f,_,_)->
			LiType.APScalar(Apron.Scalar.of_float f);
		| _->
			LiType.APScalar(Apron.Scalar.of_float 0.0);
		end;
	| Lval(lval)->
		let (host,_) = lval in
		begin match host with
		| Mem(_)->
			let strfmt = Format.str_formatter in
			Cil.d_lval strfmt lval;
			let name = Format.flush_str_formatter () in
			LiType.APVar(Apron.Var.of_string name);
		| Var(v)->
			LiType.APVar(Apron.Var.of_string (LiUtils.get_vname v));
		end;
	| CastE(_,e)|SizeOfE(e)|AlignOfE(e)|UnOp(_,e,_)->
		force_exp_to_arg env e;
	(*| SizeOf _|SizeOfStr _|AlignOf _->();*)
	| _->
		let expr = force_exp_to_texp exp in
		LiType.APTexpr(Apron.Texpr1.of_expr env expr)
	end


let force_exp2tcons (e:Cil_types.exp) env: Apron.Tcons1.t =
	let texpr = force_exp_to_texp e in
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
		if s.Cil_types.sid> !id then id := s.Cil_types.sid;
		match s.Cil_types.skind with
		| Instr(_)|Cil_types.Return(_,_)|Goto(_,_)|Break(_)|Continue(_)->();
		| If(_,b1,b2,_)->
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
		| Switch(_,b,_,_)->
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
		| Definition(dec,_)->
			let name = Kernel_function.get_name kf in
			dec.sbody.kf_name <- name;
			dec.sbody.bid <- !maxid+1;
			maxid := !maxid+1;
			generate_bpoint maxid name dec.sbody;
		| Declaration _->
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
		let index = ref 0 and flag = ref false in
		(*for i=0 to (List.length b.bstmts)-1 do
			Printf.printf "i=%d,flag=%b\n" i !flag;
			let s = List.nth b.bstmts i in
			if (List.length s.labels)==0 then
			begin if !flag==false then begin index := i; flag := true;Printf.printf "up1\n"; end;end;
			if (List.length s.labels)>0 then
			begin
				List.iter(fun label->
					begin match label with
					| Label(_,_,b)->
						if b==true && !flag==false then begin index := i; flag := true; Printf.printf "up2\n";end;
					| _->if !flag==false then begin index := i; flag := true; Printf.printf "up3\n";end;
					end;
				)s.labels;
			end else
			begin
				if !flag==false then begin index := i; flag := true; Printf.printf "up4\n";end;
			end;
		done;
		Cil.d_stmt Format.std_formatter stmt;Format.print_flush ();Printf.printf "\n";
		List.iter(fun s->
			Cil.d_stmt Format.std_formatter s;Format.print_flush ();Printf.printf "\n";
		)b.bstmts;
		Printf.printf "%d,%d\n" !index (List.length b.bstmts);*)
		let con_stmt = List.nth b.bstmts !index in
		let body_stmt = ref [] in
		for i=(!index+1) to ((List.length b.bstmts)-1) do
			body_stmt := !body_stmt@[List.nth b.bstmts i];
		done;
		begin match con_stmt.skind with
		| If(con,_,_,_)->
			{Equation.con=con;Equation.body=(!body_stmt)};
		| _->(*while(1){},so the con should be true*)
			let con = Cil.one ~loc:loc in
			{Equation.con=con;Equation.body = !body_stmt};
		end;
	| _->
		let con = Cil.dummy_exp (Cil_types.Const(Cil_types.CStr("dummy_con2"))) in
		let body_stmt = Cil.dummyStmt in
		{Equation.con=con;Equation.body = [body_stmt]};
	);;

let get_array_vars kf dec fmt =
	let vars = ref [] in
	
	(*get from function specification*)
	let funspec = Kernel_function.get_spec kf in
	List.iter(fun b->
		List.iter(fun ip->
			let rec get predicate =
				begin match predicate with
				| Pvalid_range(t1,_,t3)->
					begin match t1.term_node with
					| TLval((thost,_))->
						begin match thost with
						| TMem(_)->();
						| TVar(lv)->
							begin match lv.lv_origin with
							| Some(v1)->
								let v = {LiType.v=Some v1;LiType.vname=lv.lv_name;typ=Ctype(v1.vtype);size=LiType.CTerm(t3);} in
								vars := v::!vars;
							| None->
								let v = {LiType.v=None;LiType.vname=lv.lv_name;typ=lv.lv_type;size=LiType.CTerm(t3);} in
								vars := v::!vars;
							end;
						| TResult(_)->();
						end;
					| _->();
					end;
				| Pand(pn1,pn2)->
					get pn1.content;get pn2.content;
				| Papp(linfo,labels,tl)->
					begin match linfo.l_body with
					| LBreads(itl)->();
					| LBpred(pn)->
						let var2exp v =
							Cil.new_exp (Lval(Var(v),NoOffset))
						in
									
						let term2exp t =
							begin match t.term_node with
							| TLval((host,_))->
								begin match host with
								| TVar(lv)->
									begin match lv.lv_origin with
									| Some v->
										Some (var2exp v)
									| None->None
									end;
								| _->None
								end;
							| _->None
							end
						in
									
						let rec term2lv t =
							begin match t.term_node with
							| TLval((host,_))->
								begin match host with
								| TVar(lv)->Some lv
								| _->None
								end;
							| TCastE(_,t1)->
								term2lv t1;
							| _->None
								end
						in
									
						let nprofile = ref [] in
						List.iter(fun t->Cil.d_term Format.std_formatter t;Format.print_flush ();Printf.printf "\n";
							begin match term2lv t with
							| Some lv->
								nprofile := lv::(!nprofile);
							| None->();
							end;
						)tl;
						nprofile := List.rev !nprofile;
						let lvtbl = Hashtbl.create 3 in
						List.iter2(fun lv nlv->
							Hashtbl.add lvtbl lv nlv; 
						) linfo.l_profile (!nprofile);
									
						let np = Copy.copy_predicate pn.content in
						LiUtils.apply_predicate np lvtbl;
									
						get np;									
					| _->();
					end;
				| _->();
				end;
			in
						
			get ip.ip_content;
		)b.b_requires;
	)funspec.spec_behavior;
	
	(*get from vars directly*)
	List.iter(fun v->
		begin match v.vtype with
		| TArray(tp,_,size,_)->
			if (List.for_all(fun v1->(String.compare v.vname v1.LiType.vname)!=0) !vars)==true then
			begin
				let v = {LiType.v=Some v;LiType.vname=v.vname;typ=Ctype(tp);size=LiType.CSize(size);} in
				vars := v::!vars;
			end;
		| _->();
		end;
	)(dec.slocals@dec.sformals);
	
	(*get from stmts indirectly, sometimes maybe wrong*)
	let rec analysis_exp fmt e =
		begin match e.enode with
		| Lval((host,offset))->
			begin match (host,offset) with
			| (Mem(e1),NoOffset)->
				begin match e1.enode with
				| BinOp(_,e2,_,_)->
					let vl = Varinfo.Set.elements (LiUtils.extract_varinfos_from_exp e2) in
					List.iter(fun v1->
						if (List.for_all (fun v2->(String.compare v1.vname v2.LiType.vname)!=0) !vars)==true then
						begin
							let v = {LiType.v=Some v1;LiType.vname=v1.vname;typ=Ctype(v1.vtype);size=LiType.CSize({scache = Not_Computed});} in
							vars := v::!vars;
						end;
					)vl;
				| _->();
				end;
			| _->();
			end;
		| BinOp(_,e1,e2,_)->
			analysis_exp fmt e1;analysis_exp fmt e2;
		| UnOp(_,e,_)->
			analysis_exp fmt e;
		| CastE(_,e)->
			analysis_exp fmt e;
		| _->();
		end
	in
	let rec analysis_stmt s =
		begin match s.skind with
		| Instr(ins)->
			begin match ins with
			| Set(_,e,_)->
				analysis_exp fmt e;
			| _->();
			end;
		| Loop(_,_,_,_,_)->
			let loop = extract_loop s in
			analysis_exp fmt loop.Equation.con;
			List.iter(fun s1->
				analysis_stmt s1;
			)loop.Equation.body;
		| Block(b)->
			List.iter(fun s1->
				analysis_stmt s1;
			)b.bstmts;
		| UnspecifiedSequence(seq)->
			let b = Cil.block_from_unspecified_sequence seq in
			List.iter(fun s1->
				analysis_stmt s1;
			)b.bstmts;
		| If(exp,b1,b2,_)->
			analysis_exp fmt exp;
			List.iter(fun s1->
				analysis_stmt s1;
			)b1.bstmts;
			List.iter(fun s1->
				analysis_stmt s1;
			)b2.bstmts;
		| _->();
		end;
	in
				
	List.iter(fun s->
		analysis_stmt s;
	)dec.sbody.bstmts;
	(*get from spec*)
	!vars;;


let rec force_assert_to_annot (e:Cil_types.exp) (kf:Cil_types.kernel_function) (s:Cil_types.stmt) = 
	(match e.enode with
	| BinOp(op,e1,e2,_)->
		force_assert_to_annot e1 kf s;
		force_assert_to_annot e2 kf s;
	| _->
		let code_annot = !Db.Properties.Interp.force_exp_to_assertion e in
    let assert_root_code_annot_ba = Cil_types.User(code_annot) in
    Annotations.add kf s [Ast.self] assert_root_code_annot_ba;
  );;

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
			if (My_bigint.le big (My_bigint.of_int max_int))==true then
			[(lv,My_bigint.to_int big)]
			else [];
		| CReal(f,_,_)->[(lv,int_of_float f)];
		| _->[];
		end;
	| BinOp(_,e1,e2,_)->
		(extract_const_from_exp lv e1)@(extract_const_from_exp lv e2);
	| UnOp(_,e1,_)->
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
				| BinOp(op,_,e2,_)->
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
		| Switch(_,b,_,_)->
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
	
	let pdg = (!Db.Pdg.get) kf in
	(*(!Db.Pdg.extract) pdg ("/home/lzh/pdg_"^fname^".dot");*)
	
	let vlist = LiPdg.find_vnodes vars pdg in
	
	begin match stmt.skind with
	| Loop(_,b,_,_,_)->
		let llist = LiPdg.find_bnodes b pdg in
		let len_llist = List.length vlist in
		
		try
		for i=0 to (len_llist-1) do
			let node = List.nth vlist i in
			let nodes = (!Db.Pdg.direct_uses) pdg node in(*all_uses.if nodes are too many it will be stack overflow*)
			
			let len_nodes = List.length nodes in
			for j=0 to (len_nodes-1) do
				let n = List.nth nodes j in
				(*Printf.printf "pretty_:";(!Db.Pdg.pretty_node) false fmt n;Format.print_flush ();Printf.printf "\n";*)
				
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
						extract_const_from_stmt tmp s1;
						steps := !tmp@(!steps);
					| None->();
					end;
				end;
			done;
			
		done;
		with Stack_overflow->Printf.printf "Stack_overflow\n";
	| _->();
	end;
	let res = Hashtbl.create 3 in
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
	res;;

let rec extract_coeff_from_exp coeffs e varo =
	let strfmt = Format.str_formatter in
	
	begin match varo with
	| Some(e1)->
		Cil.d_exp strfmt e1;
		let name = Format.flush_str_formatter () in
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
		| Lval((_,_))->();
		| BinOp(op,e1,e2,_)->
			begin match op with
			| Mult->
				(extract_coeff_from_exp coeffs e1 (Some(e2)));(extract_coeff_from_exp coeffs e2 (Some(e1)));
			| Gt->
				(extract_coeff_from_exp coeffs e1 None);(extract_coeff_from_exp coeffs e2 None);
			| _->();
			end;
		| UnOp(_,e1,_)->
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
		| UnOp(_,e1,_)->
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
			| Set(_,e,_)->
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
				analysis s1;
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
let generate_array fmt kf (arrayvars:LiType.array_info list) annots stmt =
	let strfmt = Format.str_formatter in
	let exps = ref [] in
	
	let rec analysis_exp fmt e =
		(*when access an array element,these should be held*)
		let apply_index fmt base index = 
			try
				let info = List.find (fun info->(String.compare info.LiType.vname (LiUtils.get_exp_name base))==0) arrayvars in
				
				
				if (List.length !exps)==0 || (List.for_all (fun e->e.eid!=index.eid) !exps)==true then
				begin Printf.printf "get index\n";
					exps := index::(!exps);
					(*i>=0*)
					let zero_term = Cil.lzero () in
					let t = !Db.Properties.Interp.force_exp_to_term index in
					let lnamed = Logic_const.unamed (Prel(Rge,t,zero_term)) in
					
					(*let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
					let root_code_annot_ba = Cil_types.User(code_annotation) in
					Annotations.add kf stmt [Ast.self] root_code_annot_ba;
					i<=n-1*)
					begin match info.LiType.size with
					| LiType.CSize(size)->
						begin match size.scache with
						| Not_Computed->Printf.printf "Not_Computed\n";
						| Not_Computable(_)->Printf.printf "Not_Computable\n";
						| Computed(size)->Printf.printf "Computed:%d\n" (size/32);(*int*)
							let one = Cil.one ~loc:Cil_datatype.Location.unknown in
							let tone = !Db.Properties.Interp.force_exp_to_term one in
							let tlen = Cil.integer ~loc:Cil_datatype.Location.unknown (size/32) in
							let tlen = !Db.Properties.Interp.force_exp_to_term tlen in
							let tlen1 = Logic_const.term (TBinOp(MinusA,tlen,tone)) (Ctype(Cil.intType)) in
							let tindex = !Db.Properties.Interp.force_exp_to_term index in
							
							let rnamed = Logic_const.unamed (Prel(Rle,tindex,tlen1)) in
							let pnamed = Logic_const.pands [lnamed;rnamed] in
							let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
						
							Cil.d_code_annotation strfmt code_annotation;
							let strannot = Format.flush_str_formatter () in
							if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
							begin
								let root_code_annot_ba = Cil_types.User(code_annotation) in
								Annotations.add kf stmt [Ast.self] root_code_annot_ba;
								annots := strannot::!annots;
							end;
						
							let rnamed = Logic_const.unamed (Prel(Rle,tindex,tlen)) in
							let pnamed = Logic_const.pands [lnamed;rnamed] in
							let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
						
							Cil.d_code_annotation strfmt code_annotation;
							let strannot = Format.flush_str_formatter () in
							if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
							begin
								let root_code_annot_ba = Cil_types.User(code_annotation) in
								Annotations.add kf stmt [Ast.self] root_code_annot_ba;
								annots := strannot::!annots;
							end;
						end;
					| LiType.CTerm(t1)->Printf.printf "LiType.CTerm\n";
						let one = Cil.one ~loc:Cil_datatype.Location.unknown in
						let tone = !Db.Properties.Interp.force_exp_to_term one in
						let tlen = Logic_const.term (TBinOp(PlusA,t1,tone)) (Ctype(Cil.intType)) in
						let t = !Db.Properties.Interp.force_exp_to_term index in
						
						let rnamed = Logic_const.unamed (Prel(Rle,t,t1)) in
						let pnamed = Logic_const.pands [lnamed;rnamed] in
						let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
						
						Cil.d_code_annotation strfmt code_annotation;
						let strannot = Format.flush_str_formatter () in
						if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
						begin
							let root_code_annot_ba = Cil_types.User(code_annotation) in
							Annotations.add kf stmt [Ast.self] root_code_annot_ba;
							annots := strannot::!annots;
						end;
						
						let rnamed = Logic_const.unamed (Prel(Rle,t,tlen)) in
						let pnamed = Logic_const.pands [lnamed;rnamed] in
						let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
						
						Cil.d_code_annotation strfmt code_annotation;
						let strannot = Format.flush_str_formatter () in
						if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
						begin
							let root_code_annot_ba = Cil_types.User(code_annotation) in
							Annotations.add kf stmt [Ast.self] root_code_annot_ba;
							annots := strannot::!annots;
						end;
					end;
				end;
			with Not_found->Printf.printf "not find arrv\n";
		in
		
		begin match e.enode with
		| Lval((host,offset))->
			begin match (host,offset) with
			| (Var(v),Index(ie,_))->
				begin match v.vtype with
				| TArray _->Printf.printf "v.vname=%s\n" v.vname;
					let info = List.find (fun info->(String.compare info.LiType.vname v.vname)==0) arrayvars in
					let tindex = !Db.Properties.Interp.force_exp_to_term ie in
					let lnamed = Logic_const.unamed (Prel(Rge,tindex,(Cil.lzero ()))) in
					
					begin match info.LiType.size with
					| LiType.CSize(size)->
						begin match size.scache with
						| Not_Computed->Printf.printf "Not_Computed\n";
						| Not_Computable(_)->Printf.printf "Not_Computable\n";
						| Computed(size)->Printf.printf "Computed:%d\n" (size/32);
							let one = Cil.one ~loc:Cil_datatype.Location.unknown in
							let tone = !Db.Properties.Interp.force_exp_to_term one in
							let tlen = Cil.integer ~loc:Cil_datatype.Location.unknown (size/32) in
							let tlen = !Db.Properties.Interp.force_exp_to_term tlen in
							let tlen1 = Logic_const.term (TBinOp(MinusA,tlen,tone)) (Ctype(Cil.intType)) in
							
							let rnamed = Logic_const.unamed (Prel(Rle,tindex,tlen1)) in
							let pnamed = Logic_const.pands [lnamed;rnamed] in
							let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
						
							Cil.d_code_annotation strfmt code_annotation;
							let strannot = Format.flush_str_formatter () in
							if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
							begin
								let root_code_annot_ba = Cil_types.User(code_annotation) in
								Annotations.add kf stmt [Ast.self] root_code_annot_ba;
								annots := strannot::!annots;
							end;
						
							let rnamed = Logic_const.unamed (Prel(Rle,tindex,tlen)) in
							let pnamed = Logic_const.pands [lnamed;rnamed] in
							let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
						
							Cil.d_code_annotation strfmt code_annotation;
							let strannot = Format.flush_str_formatter () in
							if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
							begin
								let root_code_annot_ba = Cil_types.User(code_annotation) in
								Annotations.add kf stmt [Ast.self] root_code_annot_ba;
								annots := strannot::!annots;
							end;
						end;
					| LiType.CTerm(t1)->
						let one = Cil.one ~loc:Cil_datatype.Location.unknown in
						let tone = !Db.Properties.Interp.force_exp_to_term one in
						let tlen = Logic_const.term (TBinOp(PlusA,t1,tone)) (Ctype(Cil.intType)) in
						
						let rnamed = Logic_const.unamed (Prel(Rle,tindex,t1)) in
						let pnamed = Logic_const.pands [lnamed;rnamed] in
						let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
						
						Cil.d_code_annotation strfmt code_annotation;
						let strannot = Format.flush_str_formatter () in
						if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
						begin
							let root_code_annot_ba = Cil_types.User(code_annotation) in
							Annotations.add kf stmt [Ast.self] root_code_annot_ba;
							annots := strannot::!annots;
						end;
						
						let rnamed = Logic_const.unamed (Prel(Rle,tindex,tlen)) in
						let pnamed = Logic_const.pands [lnamed;rnamed] in
						let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
						
						Cil.d_code_annotation strfmt code_annotation;
						let strannot = Format.flush_str_formatter () in
						if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
						begin
							let root_code_annot_ba = Cil_types.User(code_annotation) in
							Annotations.add kf stmt [Ast.self] root_code_annot_ba;
							annots := strannot::!annots;
						end;
					end;
				| _->();
				end;
			| (Mem(e1),Index(ie,_))->Printf.printf "mem,index\n";
			| (Mem(e1),NoOffset)->Printf.printf "mem,NoOffset\n";
				begin match e1.enode with
				| BinOp(_,e2,e3,_)->
					apply_index fmt e2 e3;
				| _->();
				end;
			| _->();
			end;
		| BinOp(_,e1,e2,_)->
			analysis_exp fmt e1;analysis_exp fmt e2;
		| UnOp(_,e,_)->
			analysis_exp fmt e;
		| CastE(_,e)->
			analysis_exp fmt e;
		| _->();
		end
	in

	let rec analysis_stmt s=
		begin match s.skind with
		| Instr(instr)->
			begin match instr with
			| Set(_,e,_)->
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
		| If(exp,b1,b2,_)->
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

let generate_template fmt procinfo loop (lvars:Cil_types.varinfo list) (conl:(Cil_types.stmt * Cil_types.exp) list) stmt loc env (ipl:Property.identified_property list ref) wp_compute annots unknownout: Equation.transfer list =
	let kf = procinfo.Equation.kf in
	let cond = force_exp2tcons loop.con env in  
	let transfers = ref [] in
	let zero_term = Cil.lzero () in
	let ltype = Cil_types.Ctype(Cil.intType) in
	let strfmt = Format.str_formatter in
	
	(*get all valEles in conl*)
	let vars = ref [] in
	let cond_consts = ref [] in
	List.iter(fun (_,e)->
		let cons = extract_const_from_exp None e in
		List.iter(fun (_,c)->
			if (List.for_all(fun c1->
				if (Big_int.ge_big_int (Big_int.big_int_of_int c) (Big_int.big_int_of_int max_int))==false then
					(Big_int.int_of_big_int c1)!=c
				else false) !cond_consts)==true then
			 cond_consts := (Big_int.big_int_of_int c)::(!cond_consts);
		)cons;
		
		let evars = !(LiUtils.extract_valEle_from_exp e) in
		List.iter(fun v->
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
		| Cvalue.V.Map(_)->
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
				| Ival.Float(_)->Printf.printf "Float\n";
				| Ival.Top(to1,to2,_,_)->Printf.printf "Top\n";(*interval;to1--min,to2--max*)
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
	let coeffs = procinfo.Equation.var2coeff in (*Hashtbl.create 3 in*)
	List.iter(fun v->
		begin match v.vtype with
		| TPtr _|TArray _|TFun _|TNamed _|TComp _|TEnum _|TBuiltin_va_list _->();
		| _ ->
			let name = LiUtils.get_vname v in
			try
				Hashtbl.find coeffs name;();
			with Not_found->
				Hashtbl.add coeffs name (ref [(Apron.Coeff.s_of_int 1);
				(Apron.Coeff.s_of_int 0);
				(Apron.Coeff.s_of_int (-1))]);
		end;
	)lvars;
	extract_coeff_from_loop coeffs stmt;
	
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
		
		Cil.d_code_annotation strfmt code_annotation;
		let strannot = Format.flush_str_formatter () in
		if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
		begin
			let root_code_annot_ba = Cil_types.User(code_annotation) in
			Annotations.add kf stmt [Ast.self] root_code_annot_ba;
			annots := strannot::!annots;
		end;
		(*if (LiAnnot.prove_code_annot kf stmt code_annotation ipl wp_compute unknownout)==0 then
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
		| LiType.Lval(lv)->
			let (host,_) = lv in
			begin match host with
			| Var(v)->
				if (List.for_all(fun v1->v.vid!=v1.vid) !avars)==true then
				begin
					avars := v::(!avars);
				end;
			| Mem(_)->();
			end;
		end;
	)(!vars);
		
	List.iter(fun v->Cil.d_var Format.std_formatter v;Format.print_flush ();Printf.printf "\n";
		begin match v.vtype with
		| TPtr(_,_)->
			let lv = Cil.new_exp ~loc:loc (Lval(Mem((Cil.evar ~loc:loc v)),NoOffset)) in
			Cil.d_exp strfmt lv;
			let name = Format.flush_str_formatter () in
			Hashtbl.add varhash name v;
		| _->
			Hashtbl.add varhash v.vname v;
		end;
	)(!avars);
		
	let coeffl = ref [] in
	
	
	let rec pick a s e len =
		let v = ref [] in
		if e-s+1>=len&&len>0 then
		begin
			let len0 = len in
			let res1 = pick a (s+1) e (len-1) in
			let len = List.length !res1 in
			let ele = List.nth a s in
			if len>0 then
			begin
				List.iter(fun r->
					r := ele::!r;
				)!res1;
			end else
			begin
				res1 := [ref [ele]];
			end;
		
			let res2 = pick a (s+1) e len0 in
			List.iter(fun r->
				res1 := r::!res1;
			)!res2;
			
			v := !res1;
		end;
		
		v
	in
	
	
	Hashtbl.iter(fun name l->
		try
			Hashtbl.find varhash name;
			coeffl := ((ref 0),name,!l)::(!coeffl);(*current index,name,coeff list*)
		with Not_found->();
	)coeffs;
	
	let template_size = ref 3  in
	let len = List.length !coeffl in
	Printf.printf "tvar len=%d\n" len;
	if len<(!template_size) then template_size := len;
	
	if len>0 then
	begin
		let comb = pick !coeffl 0 (len-1) !template_size in(*all combination of coeff list,at most template_size*)

		List.iter(fun r->
			let total = ref 1 and count = ref 0 in
			let com_coeffl = ref [] in
			
			List.iter(fun (_,name,l)->
				total := !total*(List.length l);
				com_coeffl := ((ref 0),name,l)::(!com_coeffl);
			)!r;
			
			
			let cof_to_int c =(*maybe exist problem*)
				Apron.Coeff.print strfmt c;
				int_of_string (Format.flush_str_formatter ());
			in		
		
			while !count<(!total) do
				let com = ref [] in
				let len1 = List.length !r in
				
				for i=0 to (len1-1) do
					let (indexi,name,li) = List.nth !com_coeffl i in
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
							if j<len1 then begin
								let (indexj,_,lj) = List.nth !com_coeffl j in
								indexj := !indexj+1;
								if !indexj==(List.length lj) then
								begin indexj := 0;inc (j+1);end;
							end;
						in
				
						inc (i+1);
					end;				
				done;

			
				(*make cons*)
				let lterm = ref [] in
				let vars = ref [||] in
				let cofs = ref [||] in
				let cofl = ref [] in
				let term_vars = ref zero_term in
				let const_min = ref Big_int.zero_big_int and const_max = ref Big_int.zero_big_int in
			
				
				List.iter(fun (name,c)->
					let v = Hashtbl.find varhash name in
					let get_tvar =
						begin match v.vtype with
						| TArray _->zero_term(*donnot care about array*)
						| TPtr _->
							let lv = Cil.cvar_to_lvar v in
							let tnode = TLval((TVar(lv),TNoOffset)) in
							let tnode = TLval((TMem(Logic_const.term tnode ltype),TNoOffset)) in
							Logic_const.term tnode ltype
						| _->
							let lv = Cil.cvar_to_lvar v in
							let tnode = TLval((TVar(lv),TNoOffset)) in
							Logic_const.term tnode ltype
						end;
					in
					
					let tvar = get_tvar in
					if (cof_to_int c)!=0 then
					begin
						if (cof_to_int c)!=1 then
						begin
							let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int (cof_to_int c)),Cil_types.IInt,None)) in
							let tcof = Logic_const.term tnode ltype in				
				
							let tnode = TBinOp(Mult,tcof,tvar) in
							lterm := !lterm@[Logic_const.term tnode ltype];
						end else 
						begin lterm := !lterm@[tvar];
						end;
					
			
						(*sum of steps of var v.vname??*)
						try
							let step = Hashtbl.find steps name in	
							List.iter(fun c->
								const_min := Big_int.add_big_int !const_min (Big_int.big_int_of_int c);
								const_max := Big_int.add_big_int !const_max (Big_int.big_int_of_int c);
							)(!step); 
							
							let mostv = 
								List.find_all (fun (v1,_,_)->
								begin match v1 with
								| LiType.Var(v2)->v2==v
								| LiType.Lval(_)->false
								end;) !most
							in
						
							List.iter(fun (_,min,max)->
								const_min := Big_int.add_big_int !const_min min;
								const_max := Big_int.add_big_int !const_max max;
							)mostv;
						
							let av = Apron.Var.of_string name in
							vars := Array.append !vars [|av|];
							cofs := Array.append !cofs [|Apron.Var.of_string (name^"cof")|];

							cofl := (c,av)::!cofl;
						
						with Not_found->Printf.printf "not found [%s]\n" name;
					end;			
				)(!com);
			
				let com_consts = ref [] in
				List.iter(fun c->
					com_consts := c::(!com_consts);
				)(!cond_consts);
				if (List.for_all(fun c1->Big_int.eq_big_int !const_max c1) !com_consts)==true then 
				com_consts := !const_max::(!com_consts);
				if (List.for_all(fun c1->Big_int.eq_big_int !const_min c1) !com_consts)==true then 
				com_consts := !const_min::(!com_consts);
				
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
					
					let new_env = Apron.Environment.make (!vars) (!cofs) in
					let tab = Apron.Lincons1.array_make new_env len in
					let expr = Apron.Linexpr1.make new_env in			
			
					let mk_lincons =
						List.iter(fun const->
							if (Big_int.ge_big_int const (Big_int.big_int_of_int max_int))==false then
							begin
								let tnode_const = Cil_types.TConst(Cil_types.CInt64(const,Cil_types.IInt,None)) in
								let tnode_const = Logic_const.term tnode_const ltype in
								
								let tmax =
									if (Big_int.eq_big_int const Big_int.zero_big_int)==false then
										Logic_const.term (TBinOp(PlusA,!term_vars,tnode_const)) ltype
									else
										!term_vars
								in
								
								let pred = Prel(Rgt,tmax,zero_term) in(**>*)
								Apron.Linexpr1.set_array expr (Array.of_list !cofl)
								(Some (Apron.Coeff.s_of_int (Big_int.int_of_big_int const)))(*constant part*)
								;
								let cons = Apron.Lincons1.make expr Apron.Lincons1.SUP in
								Apron.Lincons1.array_set tab 0 cons;
			
								let pnamed = Logic_const.unamed pred in
								let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
								Cil.d_code_annotation strfmt code_annotation;
								let strannot = Format.flush_str_formatter () in
								if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
								begin
									let root_code_annot_ba = Cil_types.User(code_annotation) in
									Annotations.add kf stmt [Ast.self] root_code_annot_ba;
									Apron.Lincons1.array_set tab 0 cons;(*0-index*)
									transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
									annots := strannot::!annots;
								end;
						
									let pred = Prel(Rge,tmax,zero_term) in(**>=*)
									Apron.Linexpr1.set_array expr (Array.of_list !cofl)
									(Some (Apron.Coeff.s_of_int (Big_int.int_of_big_int const)))(*constant part*)
									;
									let cons = Apron.Lincons1.make expr Apron.Lincons1.SUPEQ in
									Apron.Lincons1.array_set tab 0 cons;
					
									let pnamed = Logic_const.unamed pred in
									let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
									Cil.d_code_annotation strfmt code_annotation;
									let strannot = Format.flush_str_formatter () in
									if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
									begin
										let root_code_annot_ba = Cil_types.User(code_annotation) in
										Annotations.add kf stmt [Ast.self] root_code_annot_ba;
										Apron.Lincons1.array_set tab 0 cons;(*0-index*)
										transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
										annots := strannot::!annots;
									end;
							
										let pred = Prel(Rneq,tmax,zero_term) in(**!=*)
										Apron.Linexpr1.set_array expr (Array.of_list !cofl)
										(Some (Apron.Coeff.s_of_int (Big_int.int_of_big_int const)))(*constant part*)
										;
										let cons = Apron.Lincons1.make expr Apron.Lincons1.DISEQ in
										Apron.Lincons1.array_set tab 0 cons;
						
										let pnamed = Logic_const.unamed pred in
										let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
										Cil.d_code_annotation strfmt code_annotation;
										let strannot = Format.flush_str_formatter () in
										if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
										begin
											let root_code_annot_ba = Cil_types.User(code_annotation) in
											Annotations.add kf stmt [Ast.self] root_code_annot_ba;
											Apron.Lincons1.array_set tab 0 cons;(*0-index*)
											transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
											annots := strannot::!annots;
										end;
								
											let pred = Prel(Req,tmax,zero_term) in(**==*)
											Apron.Linexpr1.set_array expr (Array.of_list !cofl)
											(Some (Apron.Coeff.s_of_int (Big_int.int_of_big_int const)))(*constant part*)
											;
											let cons = Apron.Lincons1.make expr Apron.Lincons1.EQ in
											Apron.Lincons1.array_set tab 0 cons;

											let pnamed = Logic_const.unamed pred in
											let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
											Cil.d_code_annotation strfmt code_annotation;
											let strannot = Format.flush_str_formatter () in
											if (List.for_all(fun annot1->(String.compare annot1 strannot)!=0) !annots)==true then
											begin
												let root_code_annot_ba = Cil_types.User(code_annotation) in
												Annotations.add kf stmt [Ast.self] root_code_annot_ba;
												Apron.Lincons1.array_set tab 0 cons;(*0-index*)
												transfers := Lcons(cond,cons,code_annotation,ref true)::!transfers;
												annots := strannot::!annots;
											end;
							end;								
						)(!com_consts);
						
					in
			
					mk_lincons;
				end;
			
				count := !count+1;
			done;
		)(!comb);
	end;
		
	Printf.printf "generate over\n";
	!transfers;;
