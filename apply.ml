open Cil_types
open Apron

let apply_lincons1 fmt kf stmt lincons1 =
	let tp = Apron.Lincons1.get_typ lincons1 in
		
		let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int 0),Cil_types.IInt,None)) in
		(*let tvnode = Cil_types.TLval((Cil_types.TVar v),TNoOffset) in*)
		let term = ref (Logic_utils.mk_dummy_term tnode Cil.intType) in
		let lterm = ref [] in
		let zero_term = Logic_utils.mk_dummy_term tnode Cil.intType in
		let llvar = ref [] in
		let count = ref 0 in
		
		Apron.Lincons1.iter(fun cof v->(*Printf.printf "iter\n";Coeff.print fmt cof;Var.print fmt v;Format.print_flush ();Printf.printf "\n";*)
			let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int 0),Cil_types.IInt,None)) in
			let tvar = ref (Logic_utils.mk_dummy_term tnode Cil.intType) in
			let tcof = ref (Logic_utils.mk_dummy_term tnode Cil.intType) in
			
			let tpvar = Apron.Environment.typ_of_var lincons1.Apron.Lincons1.env v in
			(match tpvar with
			| Apron.Environment.INT->
				Printf.printf "INT\n";
				let ltype = Cil_types.Ctype(Cil.intType) in
				let logic_var = Translate.avar_to_lvar v in
				llvar := !llvar@[logic_var];
				let tnode = TLval((TVar(logic_var),TNoOffset)) in
				Cil.d_logic_type fmt logic_var.lv_type;
				tvar := Logic_const.term tnode ltype;Format.print_flush ();Printf.printf "\n";
			| Apron.Environment.REAL->
				Printf.printf "REAL\n";
				let ltype = Cil_types.Ctype(Cil.doubleType) in
				let logic_var = Cil.make_temp_logic_var ltype in
				logic_var.lv_name <- (Apron.Var.to_string v);
				llvar := !llvar@[logic_var];
				let tnode = TLval((TVar(logic_var),TNoOffset)) in
				tvar := Logic_const.term tnode ltype;
			);
			(*Cil.d_term fmt !tvar;Format.print_flush ();Printf.printf "-->";
			TypePrinter.print_tnode_type fmt (!tvar).term_node;Format.print_flush ();*)
			
			(match cof with
			| Apron.Coeff.Scalar(sca)->
				(match sca with
				| Apron.Scalar.Float(f)->
					Printf.printf "f\n";
					let ltype = Cil_types.Ctype(Cil.intType) in
					let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_float f),Cil_types.IInt,None)) in
					tcof := Logic_const.term tnode ltype;
				| Apron.Scalar.Mpqf(q)->
					Printf.printf "q\n";
					let ltype = Cil_types.Ctype(Cil.intType) in
					let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_string (Mpqf.to_string q)),Cil_types.IInt,None)) in
					tcof := Logic_const.term tnode ltype;
				| _->();
				);
			| Apron.Coeff.Interval(_)->();
			);
			(*Cil.d_term fmt !tcof;Format.print_flush ();Printf.printf "-->";
			TypePrinter.print_tnode_type fmt (!tcof).term_node;Format.print_flush ();*)
			
			let ltype = Cil_types.Ctype(Cil.intType) in
			let tnode = TBinOp(Mult,!tcof,!tvar) in
			lterm := !lterm@[Logic_const.term tnode ltype];
			(*if !count == 0 then
			(term := Logic_utils.mk_dummy_term tnode Cil.intType;count := !count+1;)
			else
			(
			let term2 = Logic_utils.mk_dummy_term tnode Cil.intType in
			term := Logic_utils.mk_dummy_term (TBinOp(PlusA,!term,term2)) Cil.intType;
			);
			Cil.d_term fmt !term;Format.print_flush ();Printf.printf "-->";
			TypePrinter.print_tnode_type fmt (!term).term_node;Format.print_flush ();*)
		)lincons1;
		
		let ltype = Cil_types.Ctype(Cil.intType) in
		let tnode = Cil_types.TConst(Cil_types.CInt64((My_bigint.of_int 0),Cil_types.IInt,None)) in
		let cst = Apron.Lincons1.get_cst lincons1 in
		let tcof = ref (Logic_utils.mk_dummy_term tnode Cil.intType) in
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
		lterm := !lterm@[!tcof];(*Logic_utils.mk_dummy_term (TBinOp(PlusA,!term,!tcof)) Cil.intType;*)
		
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
			let rterm = Logic_utils.mk_dummy_term (TBinOp(Mod,!term,zero_term)) Cil.intType in
			pred := Prel(Req,!term,rterm);(*%=*)
		);
		(*let code_annotation = Logic_const.new_code_annotation(AAssigns([],WritesAny)) in
		let root_code_annot_ba = Cil_types.User(code_annotation) in
    Annotations.add kf stmt [Ast.self] root_code_annot_ba;*)
    
		let pnamed = Logic_const.unamed !pred in
		let code_annotation = Logic_const.new_code_annotation(AInvariant([],true,pnamed)) in
		Cil.d_code_annotation fmt code_annotation;Format.print_flush ();Printf.printf "\n";
		code_annotation
		
let apply_abstract1 fmt kf stmt abs ipl =
	let man = Apron.Abstract1.manager abs in
	let lconsarray = Apron.Abstract1.to_lincons_array man abs in
	Array.iter(fun cons->
		let lincons1 = {Apron.Lincons1.lincons0=cons;Apron.Lincons1.env=lconsarray.Apron.Lincons1.array_env} in
		let code_annotation = apply_lincons1 fmt kf stmt lincons1 in
		let root_code_annot_ba = Cil_types.User(code_annotation) in
		Annotations.add kf stmt [Ast.self] root_code_annot_ba;
		LiAnnot.prove_code_annot kf stmt code_annotation ipl;
	)lconsarray.Apron.Lincons1.lincons0_array
	
let apply_cons fmt kf stmt cons ipl =
	let code_annotation = apply_lincons1 fmt kf stmt cons in
	let root_code_annot_ba = Cil_types.User(code_annotation) in
	Annotations.add kf stmt [Ast.self] root_code_annot_ba;
	LiAnnot.prove_code_annot kf stmt code_annotation ipl

let apply_result prog fmt fp ipl=
	Globals.Functions.iter(fun kf ->
		try
			let name = Kernel_function.get_name kf in
			let fundec = Kernel_function.get_definition kf in
			List.iter(fun stmt->
				try
					let rec apply_stmt s =
						match s.skind with
						| Instr(_)|Return(_,_)|Goto(_,_)|Break(_)|Continue(_)->();
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
							let loop = Translate.extract_loop stmt in
      				let first_stmt = List.nth loop.Equation.body 0 in
							let end_stmt = Li_utils.get_stmt_end (List.nth loop.Equation.body ((List.length loop.Equation.body)-1)) in
							
							let abs = PSHGraph.attrvertex fp {Equation.fname=name;Equation.sid=first_stmt.Cil_types.sid} in
							apply_abstract1 fmt kf s abs;
							
							(*let b = (Translate.force_stmt2block loop.Equation.body) in*)
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
									(	Printf.printf "sat==true\n";
										Equation.print_transfer fmt transfer;Format.print_flush ();Printf.printf "\n";
										let abs = PSHGraph.attrvertex fp {Equation.fname=name;Equation.sid=first_stmt.Cil_types.sid} in
										(*apply_cons fmt kf s cons;*)
										let root_code_annot_ba = Cil_types.User(code_annotation) in
										
										Cil.d_stmt fmt s;Format.print_flush ();Printf.printf "\n";
										Annotations.add kf s [Ast.self] root_code_annot_ba;
										let annots = Annotations.get_all_annotations s in
										Printf.printf "annots.len=%d\n" (List.length annots);
										List.iter(fun r->
											match r with
											| User(code_annot)->Cil.d_code_annotation fmt code_annot;Format.print_flush ();Printf.printf "\n";
											| AI(_,code_annot)->Cil.d_code_annotation fmt code_annot;Format.print_flush ();Printf.printf "\n";
										)annots;
										LiAnnot.prove_code_annot kf s code_annotation ipl;
									)
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
