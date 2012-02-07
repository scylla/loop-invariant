open Cil
open Cil_types
open LiVisitor
open LiAnnot
open Li_utils

(*get max sid in block*)
let rec get_block_maxid id b =
	List.iter(fun s->
		let fmt = Format.std_formatter in
		if s.sid> !id then id := s.sid;
		match s.skind with
		| Instr(_)|Return(_,_)|Goto(_,_)|Break(_)|Continue(_)->();
		| If(e,b1,b2,_)->
			get_block_maxid id b1;
			get_block_maxid id b2;
		| TryFinally(b1,b2,_)->
			get_block_maxid id b1;
			get_block_maxid id b2;
		| Switch(_,b,sl,_)->
			List.iter(fun s->
				if s.sid> !id then id := s.sid;
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
let rec generate_bpoint id name b =
	id := !id+1;
	b.bid <- !id;
	b.kf_name <- name;
	List.iter(fun s->
		match s.skind with
		| Instr(_)|Return(_,_)|Goto(_,_)|Break(_)|Continue(_)->();
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
	
let generate_template fmt kf loop env (vars:Apron.Var.t array) (cofs:Apron.Var.t array)=
		let new_env = Apron.Environment.make vars cofs in
    
    let cofl = ref [] in
    let len = (Array.length vars)-1 in
    for i=0 to len do
    	cofl := (Apron.Coeff.s_of_int (-1), vars.(i))::!cofl;
    done;
    let tab = Apron.Lincons1.array_make new_env len in
    let expr = Apron.Linexpr1.make new_env in
    Apron.Linexpr1.set_array expr (Array.of_list !cofl)
    (Some (Apron.Coeff.s_of_int 30))(*must be a valid argument*)
    ;
    let cons = Apron.Lincons1.make expr Apron.Lincons1.SUP in
  	Apron.Lincons1.array_set tab 0 cons;(*0-index*)
		cons;;
