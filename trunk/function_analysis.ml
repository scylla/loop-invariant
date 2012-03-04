open Cil
open Cil_types
open Cil_datatype
	
let  generate_loop_annotations (kf:Cil_types.kernel_function) (loop_stmt:stmt) (loop_block:Cil_types.block) (linfo_list:logic_info list) (assumes:predicate named list) (funsigs:(string,Loop_parameters.procsignature) Hashtbl.t) (visitor:LiVisitor.liVisitor)=
	
	let lt = ref [] in
	let total_lt = ref [] in
	let rec generate_block_predicate (b:block) =
	List.iter(fun s->
	
	match s.skind with
	| Instr(instr)->
		(
		match instr with
		| Set(lval,exp,location)->(*An assignment.i=i+1;lval:i;exp:i+1*)
			(*let texp = constFold true (stripCasts exp) in*)
			let tlval = !Db.Properties.Interp.force_lval_to_term_lval lval in
			let tr = !Db.Properties.Interp.force_exp_to_term exp in
			let tnode = TLval(tlval) in
			
			
			let lvars = Cil.extract_varinfos_from_lval lval in
			let evars = Cil.extract_varinfos_from_exp exp in
			let levars = List.append (Varinfo.Set.elements lvars) (Varinfo.Set.elements evars) in
			let alvars = ref [] in
			let llvars = ref [] in
			let elvars = ref [] in
			let lelvars = ref [] in
			
			
			List.iter(fun cv->
				let lv = Cil.cvar_to_lvar cv in
				if (List.for_all (fun lv1->(lv.lv_name==lv1.lv_name)==false) s.free_lv_list)==true then	lelvars := lv::!lelvars;
			)levars;
			
			List.iter(fun lv->
				if (List.for_all (fun lv1->(lv.lv_name==lv1.lv_name)==false) !lelvars)==true then alvars := lv::!alvars;
			)s.free_lv_list;
			
			List.iter(fun cv->
				if (List.for_all (fun lv1->(cv.vname==lv1.lv_name)==false) s.free_lv_list)==true then llvars := (Cil.cvar_to_lvar cv)::!llvars;
			)(Varinfo.Set.elements lvars);
			
			List.iter(fun cv->
				if (List.for_all (fun lv1->(cv.vname==lv1.lv_name)==false) s.free_lv_list)==true then elvars := (Cil.cvar_to_lvar cv)::!elvars;
			)(Varinfo.Set.elements evars);
			
			let tl = Logic_utils.mk_dummy_term tnode (Cil.typeOfLval lval) in
			
			(*
			List.iter(fun linfo->
				visitor#add_pn kf linfo loop_stmt (List.append (Varinfo.Set.elements evars) (Varinfo.Set.elements evars));
			)linfo_list;*)
		
			let id_pre = Logic_const.new_predicate (Logic_const.prel (Req,tl,tr)) in(*only Req now*)
			let t_named = ref (Logic_const.unamed ~loc:location id_pre.ip_content) in			
			
			let con_named = Logic_const.pands (List.rev s.predicate_list) in
			if (List.length !alvars)!=0 then(*!llvars*)
			begin
				(*t_named := Logic_const.unamed (Pexists (!llvars,(Logic_const.unamed (Pimplies (con_named,!t_named)))));
				t_named := Logic_const.unamed (Pforall (s.free_lv_list@(!elvars),!t_named));*)
				(*t_named := Logic_const.unamed (Pexists (!lelvars,(Logic_const.unamed (Pimplies (con_named,!t_named)))));
				t_named := Logic_const.unamed (Pforall (!alvars,!t_named));
				t_named := Logic_const.unamed (Pforall (s.free_lv_list@(!elvars),(Logic_const.unamed (Pimplies (con_named,!t_named)))));*)
				t_named := Logic_const.unamed (Pimplies (con_named,!t_named));
			end
			else
			begin
				(*t_named := Logic_const.unamed (Pforall (s.free_lv_list@(!elvars),(Logic_const.unamed (Pimplies (con_named,!t_named)))));*)
				t_named := Logic_const.unamed (Pimplies (con_named,!t_named));
			end;
			
			lt := !t_named::!lt;
			total_lt := !lt::!total_lt;
			lt := [];
			();
		(*Set End*)
		| Call(lo,e1,el,loc)->
			Printf.printf "Call in loop\n";
			let name = LiUtils.get_exp_name e1 in
			(try
				let (fsig:Loop_parameters.procsignature) = Hashtbl.find funsigs name in
								
				(match fsig.Loop_parameters.formals with
				| Some(fvars)->
					let behave = fsig.Loop_parameters.spec.spec_behavior in
					List.iter(fun b->
						List.iter(fun (tkind,p)->
							let copy_visitor = new Visitor.frama_c_copy (Project.current ()) in
							let np = Copy.copy_predicate p.ip_content in
							LiUtils.replace_predicate_var np fvars el;
							
							let np = Logic_const.unamed np in
							(*total_lt := [np]::!total_lt;*)
							let annot = Logic_const.new_code_annotation(AInvariant([],true,np)) in
							let root_code_annot_ba = Cil_types.User(annot) in
							Annotations.add kf loop_stmt [Ast.self] root_code_annot_ba;
						)b.b_post_cond;
					)behave;
				| None->();
				);
			with Not_found->Printf.printf "Not_found in Call in loop\n";
			);
		| _->
			();(*match instr End*)
		);
		total_lt := !lt::!total_lt;lt := [];();
	(*Instr End*)
	| If(exp_temp,b1,b2,l)->
		lt := [];
		let b1_break = ref false in
		let b2_break = ref false in
		List.iter(fun bs->(
			match bs.skind with
			| Break(_)->(
				b1_break := true;
			)
			| _->(
			);
		)
		)b1.bstmts;
		List.iter(fun bs->(
			match bs.skind with
			| Break(_)->(
				b2_break := true;
			)
			| _->(
			);
		)
		)b2.bstmts;
		
		
		let texp_temp = constFold true (stripCasts exp_temp) in
		let texp_vars = Cil.extract_varinfos_from_exp texp_temp in
		(*List.iter(fun linfo->
			visitor#add_pn kf linfo loop_stmt (Varinfo.Set.elements texp_vars);
		)linfo_list;*)
		let tlv_vars = ref [] in
		List.iter(fun cv->(
			tlv_vars := (Cil.cvar_to_lvar cv)::!tlv_vars;
		)
		)(Varinfo.Set.elements texp_vars);
		
		let f_lv = ref [] in
		List.iter(fun lv->
			if (List.for_all (fun lv1->(lv.lv_id==lv1.lv_id)==false) s.free_lv_list)==true then f_lv := lv::!f_lv;
		)!tlv_vars;
		
		(*Logic_const.unamed (Pforall (!v_vars,con_named))*)
		let cp_named_temp = !Db.Properties.Interp.force_exp_to_predicate texp_temp in(*condition predicate named*)
		(*let cp_named_temp = Logic_const.unamed (Pforall (!f_lv,cp_named_temp)) in*)
		List.iter(fun succs->(
			succs.predicate_list <- cp_named_temp::s.predicate_list;
			succs.free_lv_list <- !f_lv@s.free_lv_list;
		)
		)b1.bstmts;
		
		List.iter(fun succs->(
			succs.predicate_list <- (Logic_const.pnot ~loc:l cp_named_temp)::s.predicate_list;
			succs.free_lv_list <- !f_lv@s.free_lv_list;
		)
		)b2.bstmts;
		
		(*succs of If? not in b1,b2*)
		let is_in_block (s:stmt) (b:block) = 
			let flag = ref false in
			List.iter(fun s0->
				if s.sid==s0.sid then flag := true;
			)b.bstmts;
			flag;
		in
		
		if !b1_break=true then
		(
			List.iter(fun if_succs->(
				if (!(is_in_block if_succs b1)=false)&&(!(is_in_block if_succs b2)=false) then
				begin
					if_succs.predicate_list <- (Logic_const.pnot ~loc:l cp_named_temp)::if_succs.predicate_list@s.predicate_list;
					if_succs.free_lv_list <- !f_lv@s.free_lv_list;
				end;
			
			)
			)s.succs;
		);
		if !b2_break=true then
		(
			List.iter(fun if_succs->(
				if (!(is_in_block if_succs b1)=false)&&(!(is_in_block if_succs b2)=false) then
				begin
					if_succs.predicate_list <- cp_named_temp::if_succs.predicate_list@s.predicate_list;
					if_succs.free_lv_list <- !f_lv@s.free_lv_list;
				end;
			)
			)s.succs;
		);
		
		generate_block_predicate b1;
		generate_block_predicate b2;
		();
	(*If End*)
	| Break(_)|Continue(_)->
		();
	(*Break End*)
	| Block(b2)->
		(*if (List.length s.predicate_list)>0 then*)	
		List.iter(fun bs->(
			bs.predicate_list <- s.predicate_list;
			bs.free_lv_list <- s.free_lv_list;
		)
		)b2.bstmts;
		
		generate_block_predicate b2;
		();
	(*Block End*)
	| UnspecifiedSequence(seq)->
		let seq_block = Cil.block_from_unspecified_sequence seq in
		(*if (List.length s.predicate_list)>0 then*)
		List.iter(fun bs->(
			bs.predicate_list <- s.predicate_list;
			bs.free_lv_list <- s.free_lv_list;
		)
		)seq_block.bstmts;
		
		generate_block_predicate seq_block;
		();
	(*UnspecifiedSequence End*)
	| _->
		();
	(*match s.skind End*)
	)b.Cil_types.bstmts;(*List.iter End*)
	!lt;
	in
	
	generate_block_predicate loop_block;
	total_lt
	
let analysis_kf (kf:Cil_types.kernel_function) (manager:'a Apron.Manager.t) (linfo_list:logic_info list) (assumes:predicate named list) (funsigs:(string,Loop_parameters.procsignature) Hashtbl.t) (visitor:LiVisitor.liVisitor) (ipl:Property.identified_property list ref) wp_compute=
	let fmt = Format.std_formatter in
	try
	let fundec = Kernel_function.get_definition kf in
	List.iter( fun stmt ->
		(
		match stmt.skind with
		| If(exp,block1,block2,location)->
		  	let texp = constFold true (stripCasts exp) in
		  	(
		  	match texp.enode with
		  	| BinOp((Div|Mod|Mult|PlusA|MinusA),_,_,_)->
		  		();
		  	| BinOp((Lt|Gt|Le|Ge),exp1,exp2,typ)->
		  		let lexpr = Logic_utils.expr_to_term ~cast:true exp2 in
		  		let pre_named = !Db.Properties.Interp.force_exp_to_predicate texp in
		  		
		  		let free_vars = Cil.extract_free_logicvars_from_predicate pre_named in
		  		
		  		let add_code_annot (free_vars:Cil_datatype.Logic_var.Set.t) =
		  			let annotation =
				      Logic_const.new_code_annotation
				      (AAssert ([],Logic_const.unamed (Prel (Rneq,lexpr, lzero()))))
		       		in
		       		let assert_root_code_annot_ba = Cil_types.User(annotation) in
		       		(*Annotations.add kf stmt [Ast.self] assert_root_code_annot_ba;
		       		prove_code_annot kf stmt annotation;*)();
		  		in
		  		
		  		if (Logic_var.Set.is_empty free_vars)=false
		  		then add_code_annot free_vars;
		  		(*else begin
				(*let annotation =
				      Logic_const.new_code_annotation
				      (AInvariant ([],true,Logic_const.unamed (Pforall ((Logic_var.Set.elements free_vars),pre_named))
				      ))
           		in
           		let root_code_annot_ba = Db_types.Before(Db_types.User(annotation)) in
           		Annotations.add stmt [Ast.self] root_code_annot_ba;*)
           		add_code_annot free_vars; end*)
		  		(*let term = !Db.Properties.Interp.force_exp_to_term texp in
		  		let new_code_annot = Logic_const.new_code_annotation (term,*)
		  	| _->();
		  	);
		  	(*Cil.d_exp Format.std_formatter texp;
		  	Format.print_flush ();
		  	Printf.printf "\n";
		  	
		  	let assert_code_annot = !Db.Properties.Interp.force_exp_to_assertion texp in
		  	Cil.d_code_annotation Format.std_formatter assert_code_annot;
		  	Format.print_flush ();
		  	Printf.printf "\n";
		  	
		  	let pre = !Db.Properties.Interp.force_exp_to_predicate texp in
		  	Cil.d_predicate_named Format.std_formatter pre;
		  	Format.print_flush ();
		  	Printf.printf "\n";*)
		  	(*Annotations.add_assert stmt [Ast.self] ~before:true pre;*)
		  	
		  	(*let term = !Db.Properties.Interp.force_exp_to_term texp in
		  	Cil.d_term Format.std_formatter term;
		  	Format.print_flush ();
		  	Printf.printf "\n";*)
		 (*end If*)
		 | Instr(instr) ->
		  	(
		  	match instr with
		  	| Set(lval,exp,_)->
		  		();
			  	(*let lexp = constFold true (stripCasts exp) in
				let tlval = !Db.Properties.Interp.force_lval_to_term_lval lval in
				let tr = !Db.Properties.Interp.force_exp_to_term lexp in
				let tnode = TLval(tlval) in	
				let tl = Logic_utils.mk_dummy_term tnode (Cil.typeOfLval lval) in			
				let id_pre = Logic_const.new_predicate (Logic_const.prel (Req,tl,tr)) in(*only Req now*)
				let t_named = Logic_const.unamed ~loc:location id_pre.ip_content in
				
				let annotation = Logic_const.new_code_annotation (AStmtSpec((tr,id_pre,(Logic_const.new_identified_term tr) spec))) in
           		let root_code_annot_ba = Db_types.Before(Db_types.User(annotation)) in
           		Annotations.add stmt [Ast.self] root_code_annot_ba;*)
			| _->
				();
			(*match instr End*)
			);
		  	Format.print_flush ();
		 | Loop(code_annot_list,block,location,stmto1,stmto2) ->
		 		Printf.printf "Enter Loop Now.\n";
		 		let vars = LiUtils.extract_varinfos_from_stmt stmt in
		 		let lvars = Varinfo.Set.elements vars in
		
		 		List.iter(fun linfo->
					visitor#add_pn kf linfo stmt (Varinfo.Set.elements vars);
				)linfo_list;
			 	Printf.printf "Analysis loop body now.\n";
			 	let total_lt = generate_loop_annotations kf stmt block linfo_list assumes funsigs visitor in
			 	total_lt := List.rev !total_lt;
			 	Printf.printf "total_lt.len=%d\n" (List.length !total_lt);
			 	List.iter(fun tl->
					if (List.length tl)>0 then
					(
						let t_named = Logic_const.pands tl in
				
						let annot = Logic_const.new_code_annotation(AInvariant([],true,t_named)) in
						let root_code_annot_ba = Cil_types.User(annot) in
						Annotations.add kf stmt [Ast.self] root_code_annot_ba;
						Cil.d_code_annotation Format.std_formatter annot;Format.print_flush ();Printf.printf "\n";
						LiAnnot.prove_code_annot kf stmt annot ipl wp_compute;();
					);
				)!total_lt;
			 	Printf.printf "Analysis loop body over.\n";
				List.iter(fun pn->
					let annot = Logic_const.new_code_annotation(AInvariant([],true,pn)) in
					let root_code_annot_ba = Cil_types.User(annot) in
					Annotations.add kf stmt [Ast.self] root_code_annot_ba;
					LiAnnot.prove_code_annot kf stmt annot ipl wp_compute;();
				)assumes;
			 	Printf.printf "Leave Loop Now.\n";
		 | Block(_) ->
		  	();
		 | Return(_,_) ->
		  	();
		 | _ ->
		  	Printf.printf "\n";
		 );
		Printf.printf "\n";
	)fundec.sallstmts(*List.iter end*)
	with Kernel_function.No_Definition->Printf.printf "The given function [%s] is not a definition.\n" (Kernel_function.get_name kf)

let analysis_assert (kf:Cil_types.kernel_function) =
	match kf.fundec with
	| Declaration(spec,var,varl,_)->
		Cil.d_funspec Format.std_formatter spec;Format.print_flush ();Printf.printf "\n";
		Cil.d_var Format.std_formatter var;Format.print_flush ();Printf.printf "\n";
		(match varl with
		| Some(l)->
			List.iter(fun v->
				Cil.d_var Format.std_formatter v;Format.print_flush ();Printf.printf ",";
			)l;
			Printf.printf "\n";
		| None->();
		)
	| _->()
