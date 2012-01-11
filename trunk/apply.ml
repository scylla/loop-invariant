open Cil_types

let apply_lincons1 fmt kf stmt lincons1 =
	let tp = Apron.Lincons1.get_typ lincons1 in
		
		let tnode = Cil_types.TConst(Cil_types.CReal(0.0,Cil_types.FDouble,None)) in
		let term = ref (Logic_utils.mk_dummy_term tnode Cil.doubleType) in
		let zero_term = Logic_utils.mk_dummy_term tnode Cil.doubleType in
		let llvar = ref [] in
		let count = ref 0 in
		
		Apron.Lincons1.iter(fun cof v->
			let tvar = ref (Logic_utils.mk_dummy_term tnode Cil.doubleType) in
			let tcof = ref (Logic_utils.mk_dummy_term tnode Cil.doubleType) in
				
			let tpvar = Apron.Environment.typ_of_var lincons1.Apron.Lincons1.env v in
			(match tpvar with
			| Apron.Environment.INT->
				let ltype = Cil_types.Ctype(Cil.intType) in
				let logic_var = Cil.make_temp_logic_var ltype in
				logic_var.lv_name <- (Apron.Var.to_string v);
				llvar := !llvar@[logic_var];
				let tnode = TLval((TVar(logic_var),TNoOffset)) in
				tvar := Logic_utils.mk_dummy_term tnode Cil.intType;
			| Apron.Environment.REAL->
				let ltype = Cil_types.Ctype(Cil.doubleType) in
				let logic_var = Cil.make_temp_logic_var ltype in
				logic_var.lv_name <- (Apron.Var.to_string v);
				llvar := !llvar@[logic_var];
				let tnode = TLval((TVar(logic_var),TNoOffset)) in
				tvar := Logic_utils.mk_dummy_term tnode Cil.doubleType;
			);
				
			(match cof with
			| Apron.Coeff.Scalar(sca)->
				(match sca with
				| Apron.Scalar.Float(f)->
					let tnode = Cil_types.TConst(Cil_types.CReal(f,Cil_types.FDouble,None)) in
					tcof := Logic_utils.mk_dummy_term tnode Cil.doubleType;
				| Apron.Scalar.Mpqf(q)->
					let tnode = Cil_types.TConst(Cil_types.CReal((Mpqf.to_float q),Cil_types.FDouble,None)) in
					tcof := Logic_utils.mk_dummy_term tnode Cil.doubleType;
				| _->();
				);
			| Apron.Coeff.Interval(_)->();
			);
				
			let tnode = TBinOp(Mult,!tcof,!tvar) in
			if !count == 0 then
			(term := Logic_utils.mk_dummy_term tnode Cil.doubleType;count := !count+1;)
			else
			(
			let term2 = Logic_utils.mk_dummy_term tnode Cil.doubleType in
			term := Logic_utils.mk_dummy_term (TBinOp(PlusA,!term,term2)) Cil.doubleType;
			);
		)lincons1;
		
		let cst = Apron.Lincons1.get_cst lincons1 in
		let tcof = ref (Logic_utils.mk_dummy_term tnode Cil.doubleType) in
		(match cst with
			| Apron.Coeff.Scalar(sca)->
				(match sca with
				| Apron.Scalar.Float(f)->
					let tnode = Cil_types.TConst(Cil_types.CReal(f,Cil_types.FDouble,None)) in
					tcof := Logic_utils.mk_dummy_term tnode Cil.doubleType;
				| Apron.Scalar.Mpqf(q)->
					let tnode = Cil_types.TConst(Cil_types.CReal((Mpqf.to_float q),Cil_types.FDouble,None)) in
					tcof := Logic_utils.mk_dummy_term tnode Cil.doubleType;
				| _->();
				);
			| Apron.Coeff.Interval(_)->();
		);
		term := Logic_utils.mk_dummy_term (TBinOp(PlusA,!term,!tcof)) Cil.doubleType;
			
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
			let rterm = Logic_utils.mk_dummy_term (TBinOp(Mod,!term,zero_term)) Cil.doubleType in
			pred := Prel(Req,!term,rterm);(*%=*)
		);
		let pnamed = Logic_const.unamed !pred in
		let pnamed = Logic_const.unamed (Pforall(!llvar,pnamed)) in
		let code_annotation = Logic_const.new_code_annotation(AAssert([],pnamed)) in
		code_annotation
		
let apply_abstract1 fmt kf stmt abs =
	let man = Apron.Abstract1.manager abs in
	let lconsarray = Apron.Abstract1.to_lincons_array man abs in
	Array.iter(fun cons->
		let lincons1 = {Apron.Lincons1.lincons0=cons;Apron.Lincons1.env=lconsarray.Apron.Lincons1.array_env} in
		let code_annotation = apply_lincons1 fmt kf stmt lincons1 in
		let root_code_annot_ba = Cil_types.User(code_annotation) in
		Annotations.add kf stmt [Ast.self] root_code_annot_ba;
	)lconsarray.Apron.Lincons1.lincons0_array
	
let apply_result prog fmt fp =
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
							let b = (Translate.force_stmt2block loop.Equation.body) in
							let abs = PSHGraph.attrvertex fp {Equation.fname=name;Equation.sid=loop.Equation.body.Cil_types.sid} in
							apply_abstract1 fmt kf s abs;
							List.iter(fun s->
								apply_stmt s;
							)b.bstmts;
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
