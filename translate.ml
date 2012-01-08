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
	

let extract_loop stmt :Equation.loop =
	let fmt = Format.std_formatter in
	Cil.d_stmt fmt stmt;Format.print_flush ();Printf.printf "\n";
	Printf.printf "id=%d\n" stmt.sid;
	(match stmt.skind with
	| Loop(_,b,_,_,_)->
		List.iter(fun s->
			Cil.d_stmt fmt s;Format.print_flush ();Printf.printf "\n";Printf.printf "id=%d\n" s.sid;
		)b.bstmts;
		let con_stmt = List.nth b.bstmts 1 in
		let body_stmt = List.nth b.bstmts 2 in
		(match con_stmt.skind with
		| If(con,_,_,_)->
			{Equation.con=con;Equation.body=body_stmt};
		| _->
			let con = Cil.dummy_exp (Cil_types.Const(Cil_types.CStr("dummy_con"))) in
			let body_stmt = Cil.dummyStmt in
			{Equation.con=con;Equation.body = body_stmt};
		);
	| _->
		let con = Cil.dummy_exp (Cil_types.Const(Cil_types.CStr("dummy_con"))) in
		let body_stmt = Cil.dummyStmt in
		{Equation.con=con;Equation.body = body_stmt};
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
