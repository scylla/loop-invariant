open Cil_types
open Apron
open Equation

let apply_lincons1 fmt (procinfo:Equation.procinfo) stmt lincons1 =
	let tp = Apron.Lincons1.get_typ lincons1 in
		
		let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int 0),Cil_types.IInt,None)) in
		let term = ref (Logic_const.term tnode (Cil_types.Ctype(Cil.intType))) in
		let lterm = ref [] in
		let zero_term = Cil.lzero () in(*Logic_const.term tnode (Cil_types.Ctype(Cil.intType)) in*)
		let llvar = ref [] in
		let count = ref 0 in
		
		Apron.Lincons1.iter(fun cof v->
			let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int 0),Cil_types.IInt,None)) in
			let tcof = ref (Logic_const.term tnode (Cil_types.Ctype(Cil.intType))) in
			
			let ltype = Cil_types.Ctype(Cil.intType) in
			let v = Hashhe.find procinfo.avar2cvar v in
			let lv = Cil.cvar_to_lvar v in
			let tnode = TLval((TVar(lv),TNoOffset)) in
			let tvar = Logic_const.term tnode ltype in
			
			(match cof with
			| Apron.Coeff.Scalar(sca)->
				(match sca with
				| Apron.Scalar.Float(f)->
					let ltype = Cil_types.Ctype(Cil.intType) in
					let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_float f),Cil_types.IInt,None)) in
					tcof := Logic_const.term tnode ltype;
				| Apron.Scalar.Mpqf(q)->
					let ltype = Cil_types.Ctype(Cil.intType) in
					let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_string (Mpqf.to_string q)),Cil_types.IInt,None)) in
					tcof := Logic_const.term tnode ltype;
				| _->();
				);
			| Apron.Coeff.Interval(_)->();
			);
			
			let ltype = Cil_types.Ctype(Cil.intType) in
			let tnode = TBinOp(Mult,!tcof,tvar) in
			lterm := !lterm@[Logic_const.term tnode ltype];
		)lincons1;
		
		let ltype = Cil_types.Ctype(Cil.intType) in
		let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int 0),Cil_types.IInt,None)) in
		let cst = Apron.Lincons1.get_cst lincons1 in
		let tcof = ref (Logic_const.term tnode (Cil_types.Ctype(Cil.intType))) in
		(match cst with
			| Apron.Coeff.Scalar(sca)->
				(match sca with
				| Apron.Scalar.Float(f)->
					let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_float f),Cil_types.IInt,None)) in
					tcof := Logic_const.term tnode ltype;
				| Apron.Scalar.Mpqf(q)->
					let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_string (Mpqf.to_string q)),Cil_types.IInt,None)) in
					tcof :=Logic_const.term tnode ltype;
				| _->();
				);
			| Apron.Coeff.Interval(_)->();
		);
		lterm := !lterm@[!tcof];
		
		List.iter(fun t->
			term := Logic_const.term (TBinOp(PlusA,!term,t)) ltype;
		)!lterm;
		let pred = ref Ptrue in
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
			let rterm = Logic_const.term (TBinOp(Mod,!term,zero_term)) (Cil_types.Ctype(Cil.intType)) in
			pred := Prel(Req,!term,rterm);(*%=*)
		);
    
		let pnamed = Logic_const.unamed !pred in
		let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
		Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
		code_annotation
(*
let apply_cons fmt procinfo stmt cons ipl wp_compute =
	let code_annotation = apply_lincons1 fmt procinfo stmt cons in
	let root_code_annot_ba = Cil_types.User(code_annotation) in
	Annotations.add procinfo.kf stmt [Ast.self] root_code_annot_ba;
	LiAnnot.prove_code_annot procinfo.kf stmt code_annotation ipl wp_compute
*)	
let apply_abstract1 fmt procinfo stmt abs ipl wp_compute =
	let man = Apron.Abstract1.manager abs in
	let lconsarray = Apron.Abstract1.to_lincons_array man abs in
	Array.iter(fun cons->
		let lincons1 = {Apron.Lincons1.lincons0=cons;Apron.Lincons1.env=lconsarray.Apron.Lincons1.array_env} in
		let code_annotation = apply_lincons1 fmt procinfo stmt lincons1 in
		let root_code_annot_ba = Cil_types.User(code_annotation) in
		Annotations.add procinfo.kf stmt [Ast.self] root_code_annot_ba;
		LiAnnot.prove_code_annot procinfo.kf stmt code_annotation ipl wp_compute;
	)lconsarray.Apron.Lincons1.lincons0_array
	

let apply_result (prog:Equation.info) fmt fp ipl wp_compute=
	Globals.Functions.iter(fun kf ->
		try
			let name = Kernel_function.get_name kf in
			let procinfo = Hashhe.find prog.Equation.procinfo name in
			let fundec = Kernel_function.get_definition kf in
			List.iter(fun stmt->
				try
					let rec apply_stmt s =
						match s.skind with
						| Instr(_)|Cil_types.Return(_,_)|Goto(_,_)|Break(_)|Continue(_)->();
						| If(_,b1,b2,_)|TryFinally(b1,b2,_)->
							List.iter(fun s->
								apply_stmt s;
							)b1.bstmts;
							List.iter(fun s->
								apply_stmt s;
							)b2.bstmts;
						| Switch(_,b,sl,_)->
							List.iter(fun s->
								apply_stmt s;
							)b.bstmts;
						| Loop(_,_,_,_,_)->
							let loop = Translate.extract_loop s in
      				let first_stmt = List.nth loop.Equation.body 0 in
							let end_stmt = Li_utils.get_stmt_end (List.nth loop.Equation.body ((List.length loop.Equation.body)-1)) in
							
							let abs = PSHGraph.attrvertex fp {Equation.fname=name;Equation.sid=first_stmt.Cil_types.sid} in
							apply_abstract1 fmt procinfo s abs ipl wp_compute;
							
							let edges1 = PSHGraph.predhedge fp {Equation.fname=name;Equation.sid=first_stmt.Cil_types.sid} in
							let edges2 = PSHGraph.succhedge fp {Equation.fname=name;Equation.sid=end_stmt.Cil_types.sid} in
							let edges = ref [] in
							PSette.iter(fun edge->
								edges := edge::!edges;
							)edges1;
							PSette.iter(fun edge->
								if (PSette.for_all (fun e->e==edge) edges1)==true then edges := edge::!edges;
							)edges2;
							
							List.iter(fun edge->
								let transfer = PSHGraph.attrhedge fp edge in
								match transfer with
								| Equation.Lcons(cond,cons,code_annotation,sat)->
									if !sat==true then
									(
										let abs = PSHGraph.attrvertex fp {Equation.fname=name;Equation.sid=first_stmt.Cil_types.sid} in
										let root_code_annot_ba = Cil_types.User(code_annotation) in
										
										Annotations.add kf s [Ast.self] root_code_annot_ba;
										LiAnnot.prove_code_annot kf s code_annotation ipl wp_compute;
									)
								| Equation.Tcons(cond,tcons,code_annotation,sat)->
									if !sat==true then
									(
										let abs = PSHGraph.attrvertex fp {Equation.fname=name;Equation.sid=first_stmt.Cil_types.sid} in
										let root_code_annot_ba = Cil_types.User(code_annotation) in
										
										Annotations.add kf s [Ast.self] root_code_annot_ba;
									);
								| _->()
							)!edges;
									
							List.iter(fun s->
								apply_stmt s;
							)loop.Equation.body;
						| Block(b)->
							List.iter(fun s->
								apply_stmt s;
							)b.bstmts;
						| UnspecifiedSequence(seq)->
							let b = Cil.block_from_unspecified_sequence seq in
							List.iter(fun s->
								apply_stmt s;
							)b.bstmts;
						| TryExcept(b1,_,b2,_)->
							List.iter(fun s->
								apply_stmt s;
							)b1.bstmts;
							List.iter(fun s->
								apply_stmt s;
							)b2.bstmts;
					in
				apply_stmt stmt;
				with Not_found->Printf.printf "Not_found\n";
			)fundec.sallstmts;
		with Kernel_function.No_Definition -> Printf.printf "exception No_Definition\n";
	)
