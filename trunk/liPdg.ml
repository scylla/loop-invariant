open Cil_types
open Db

let find_vnodes vars pdg =	
	let l = ref [] in
	List.iter(fun v->
		begin match v with
		| LiType.Lval(li)->();
		| LiType.Var(v)->
			let node = (!Db.Pdg.find_decl_var_node) pdg v in
			l := !l@[node];
		end;
	)vars;
	!l
	
let find_bnodes b pdg =
	let l = ref [] in
	
	let rec find s =		
		begin match s.skind with
		| Instr(ins)->
			begin match ins with
			| Call _->();
			| _->Printf.printf "find_bnodes:";Cil.d_stmt Format.std_formatter s;Format.print_flush ();Printf.printf "\n";
				try
				let node = (!Db.Pdg.find_stmt_node) pdg s in
				l := !l@[node];
				with Not_found->Printf.printf "the stmt is unreachable.\n";
			end;
		| Cil_types.Return(_,_)|Goto(_,_)|Break(_)|Continue(_)->		
			let node = (!Db.Pdg.find_stmt_node) pdg s in
			l := !l@[node];
		| If(_,b1,b2,_)|TryFinally(b1,b2,_)->	
			let node = (!Db.Pdg.find_stmt_node) pdg s in
			l := !l@[node];
			List.iter(fun s1->
				find s1;
			)b1.bstmts;
			List.iter(fun s1->
				find s1;
			)b2.bstmts;
		| Switch(_,b,_,_)->	
			let node = (!Db.Pdg.find_stmt_node) pdg s in
			l := !l@[node];
			List.iter(fun s1->
				find s1;
			)b.bstmts;
		| Loop(_,b,_,_,_)|Block(b)->	
			let node = (!Db.Pdg.find_stmt_node) pdg s in
			l := !l@[node];
			List.iter(fun s1->
				find s1;
			)b.bstmts;
		| UnspecifiedSequence(seq)->	
			let node = (!Db.Pdg.find_stmt_node) pdg s in
			l := !l@[node];
			let b = Cil.block_from_unspecified_sequence seq in
			List.iter(fun s1->
				find s1;
			)b.bstmts;
		| TryExcept(b1,_,b2,_)->	
			let node = (!Db.Pdg.find_stmt_node) pdg s in
			l := !l@[node];
			List.iter(fun s1->
				find s1;
			)b1.bstmts;
			List.iter(fun s1->
				find s1;
			)b2.bstmts;
		end
	in
	
	List.iter(fun s->
		find s;
	)b.bstmts;
	
	!l
