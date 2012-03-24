open Cil_types
open Db

let find_vnodes vars pdg =	
	let l = ref [] in
	List.iter(fun v->
		begin match v with
		| LiType.Lval(li)->();
		| LiType.Var(v)->
			try
				Printf.printf "v:%s,vgenerated=%b\n" v.vname v.vgenerated;
				if v.vgenerated==false then
				begin
					let node = (!Db.Pdg.find_decl_var_node) pdg v in
					l := !l@[node];
				end;
			with Not_found|PdgTypes.Pdg.Bottom|PdgTypes.Pdg.Top->();
		end;
	)vars;
	!l
	
let find_bnodes b pdg =
	let l = ref [] in
	
	let rec find s =		
		begin match s.skind with
		| Instr(ins)->			
			begin match ins with
			| Set _->
				begin try
					let node = (!Db.Pdg.find_stmt_node) pdg s in
					l := !l@[node];
				with Not_found|PdgTypes.Pdg.Bottom|PdgTypes.Pdg.Top->();
				end;
			| _->();
			end;
		| Cil_types.Return(_,_)|Goto(_,_)|Break(_)|Continue(_)->
			(*begin try
				let node = (!Db.Pdg.find_stmt_node) pdg s in
				l := !l@[node];
			with Not_found|PdgTypes.Pdg.Bottom|PdgTypes.Pdg.Top->(); 
			end;*)();
		| If(_,b1,b2,_)|TryFinally(b1,b2,_)->	
			(*begin try
				let node = (!Db.Pdg.find_stmt_node) pdg s in
				l := !l@[node];
			with Not_found|PdgTypes.Pdg.Bottom|PdgTypes.Pdg.Top->(); 
			end;*)
			List.iter(fun s1->
				find s1;
			)b1.bstmts;
			List.iter(fun s1->
				find s1;
			)b2.bstmts;
		| Switch(_,b,_,_)->
			(*begin try
				let node = (!Db.Pdg.find_stmt_node) pdg s in
				l := !l@[node];
			with Not_found|PdgTypes.Pdg.Bottom|PdgTypes.Pdg.Top->();
			end;*)
			List.iter(fun s1->
				find s1;
			)b.bstmts;
		| Loop(_,b,_,_,_)|Block(b)->	
			(*begin try
				let node = (!Db.Pdg.find_stmt_node) pdg s in
				l := !l@[node];
			with Not_found|PdgTypes.Pdg.Bottom|PdgTypes.Pdg.Top->();
			end;*)
			List.iter(fun s1->
				find s1;
			)b.bstmts;
		| UnspecifiedSequence(seq)->	
			(*begin try
				let node = (!Db.Pdg.find_stmt_node) pdg s in
				l := !l@[node];
			with Not_found|PdgTypes.Pdg.Bottom|PdgTypes.Pdg.Top->();
			end;*)
			let b = Cil.block_from_unspecified_sequence seq in
			List.iter(fun s1->
				find s1;
			)b.bstmts;
		| TryExcept(b1,_,b2,_)->	
			(*begin try
				let node = (!Db.Pdg.find_stmt_node) pdg s in
				l := !l@[node];
			with Not_found|PdgTypes.Pdg.Bottom|PdgTypes.Pdg.Top->();
			end;*)
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
