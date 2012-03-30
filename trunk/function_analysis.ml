open Cil
open Cil_types
open Cil_datatype
	
let generate_loop_annotations (kf:Cil_types.kernel_function) (loop_stmt:stmt) (loop_block:Cil_types.block) (linfo_list:logic_info list) (funsigs:(string,Loop_parameters.procsignature) Hashtbl.t) =	
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
				let levars = ref (Varinfo.Set.elements lvars) in
				List.iter(fun v->
					if (List.for_all(fun v1->(v1.vname==v.vname)==false) !levars)==true then
					levars := v::(!levars);
				)(Varinfo.Set.elements evars);
				
				let lelvars = ref [] in
			
			
				List.iter(fun cv->
					let lv = Cil.cvar_to_lvar cv in
					if (List.for_all (fun lv1->(lv.lv_name==lv1.lv_name)==false) s.free_lv_list)==true then	lelvars := lv::!lelvars;
				)!levars;
			
				let tl = Logic_const.term ~loc:location tnode (Cil.typeOfTermLval tlval) in
				
				(*
				TypePrinter.print_tnode_type Format.std_formatter tl.term_node;Format.print_flush ();
				TypePrinter.print_tnode_type Format.std_formatter tr.term_node;Format.print_flush ();*)
				let id_pre = Logic_const.new_predicate (Logic_const.prel (Req,tl,tr)) in(*only Req now*)
				let t_named = ref (Logic_const.unamed ~loc:location id_pre.ip_content) in			
			
				let con_named = Logic_const.pands (List.rev s.predicate_list) in
			
				total_lt := (!levars,[],con_named,!t_named)::!total_lt;
				
				(*array.wrong*)
				let (host,offset) = lval in
				begin match (host,offset) with
				| (Mem(e1),NoOffset)->
					begin match e1.enode with
					| BinOp(op,e2,e3,tp)->						
						let zero_term = Cil.lzero () in
						let t1 = !Db.Properties.Interp.force_exp_to_term e3 in
						let k = Cil.make_temp_logic_var Linteger in
						let tk = Logic_const.term (TLval(TVar(k),TNoOffset)) Linteger in
						let pnamed1 = Logic_const.unamed (Prel(Rge,tk,zero_term)) in(*>=0*)
						let pnamed2 = Logic_const.unamed (Prel(Rle,tk,t1)) in(*<n*)
						let p = Logic_const.pands [pnamed1;pnamed2] in
						
						let vars3 = Cil.extract_varinfos_from_exp e3 in
						
						let tk = Logic_const.term (TBinOp(op,(!Db.Properties.Interp.force_exp_to_term e2),tk)) (Ctype(Cil.typeOfLval lval)) in
						let tl = Logic_const.term (TLval(TMem(tk),TNoOffset)) (Ctype(tp)) in
						let id_pre = Logic_const.new_predicate (Logic_const.prel (Req,tl,tr)) in
						let id_pre = Copy.copy_predicate id_pre.ip_content in
						let t_named = ref (Logic_const.unamed ~loc:location id_pre) in
						let lvars = Cil.extract_free_logicvars_from_predicate !t_named in
						List.iter(fun lv->							
							List.iter(fun v3->
								if (String.compare lv.lv_name v3.vname)==0 then
								begin
								lv.lv_name <- k.lv_name;
								end;
							)(Varinfo.Set.elements vars3);
							
						)(Logic_var.Set.elements lvars);
						
						total_lt := (!levars,[k],p,!t_named)::!total_lt;
					| _->();
					end;
				| _->();				
				end;
			(*Set End*)
			| Call(_,e1,el,_)->
				let name = LiUtils.get_exp_name e1 in
				(try
					let (fsig:Loop_parameters.procsignature) = Hashtbl.find funsigs name in
								
					(match fsig.Loop_parameters.formals with
					| Some(fvars)->
						let behave = fsig.Loop_parameters.spec.spec_behavior in
						List.iter(fun b->
							List.iter(fun (_,p)->
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
		(*Instr End*)
		| If(exp_temp,b1,b2,l)->
			let b1_break = ref false in
			let b2_break = ref false in
			List.iter(fun bs->(
				match bs.skind with
				| Break(_)->
					b1_break := true;
				| _->();
			)
			)b1.bstmts;
			List.iter(fun bs->(
				match bs.skind with
				| Break(_)->
					b2_break := true;
				| _->();
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
			begin match texp_temp.enode with
			| CastE _ | AddrOf _ | StartOf _ | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ ->Printf.printf "cannot update con\n";TypePrinter.print_exp_type Format.std_formatter texp_temp;Format.print_flush ();
			Cil.d_exp Format.std_formatter texp_temp;Format.print_flush ();Printf.printf "\n";
			| Lval(lv)->
				let (host,_) = lv in
				begin match host with
				| Mem(_)->
					let e = Cil.new_exp ~loc:l (BinOp(Ne,texp_temp,(Cil.zero ~loc:l),(Cil.typeOfLval lv))) in
					let cp_named_temp = !Db.Properties.Interp.force_exp_to_predicate e in
					let cp_named_temp = Logic_const.pnot ~loc:l cp_named_temp in
					
					List.iter(fun succs->
						succs.predicate_list <- cp_named_temp::s.predicate_list;
						succs.free_lv_list <- !f_lv@s.free_lv_list;
					)b1.bstmts;
		
					List.iter(fun succs->
						succs.predicate_list <- (Logic_const.pnot ~loc:l cp_named_temp)::s.predicate_list;
						succs.free_lv_list <- !f_lv@s.free_lv_list;
					)b2.bstmts;
				| _->();
				end;
			| UnOp(op,e,tp)->
				begin match op with
				| LNot->					
					let e = Cil.new_exp ~loc:l (BinOp(Ne,e,(Cil.zero ~loc:l),tp)) in
					let cp_named_temp = !Db.Properties.Interp.force_exp_to_predicate e in
					let cp_named_temp = Logic_const.pnot ~loc:l cp_named_temp in
					
					List.iter(fun succs->
						succs.predicate_list <- cp_named_temp::s.predicate_list;
						succs.free_lv_list <- !f_lv@s.free_lv_list;
					)b1.bstmts;
		
					List.iter(fun succs->
						succs.predicate_list <- (Logic_const.pnot ~loc:l cp_named_temp)::s.predicate_list;
						succs.free_lv_list <- !f_lv@s.free_lv_list;
					)b2.bstmts;
				| _->();
				end;
			| _->
				let cp_named_temp = !Db.Properties.Interp.force_exp_to_predicate texp_temp in(*condition predicate named*)
				(*let cp_named_temp = Logic_const.unamed (Pforall (!f_lv,cp_named_temp)) in*)
				List.iter(fun succs->
					succs.predicate_list <- cp_named_temp::s.predicate_list;
					succs.free_lv_list <- !f_lv@s.free_lv_list;
				)b1.bstmts;
		
				List.iter(fun succs->
					succs.predicate_list <- (Logic_const.pnot ~loc:l cp_named_temp)::s.predicate_list;
					succs.free_lv_list <- !f_lv@s.free_lv_list;
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
					List.iter(fun if_succs->
						if (!(is_in_block if_succs b1)=false)&&(!(is_in_block if_succs b2)=false) then
						begin
							if_succs.predicate_list <- (Logic_const.pnot ~loc:l cp_named_temp)::if_succs.predicate_list@s.predicate_list;
							if_succs.free_lv_list <- !f_lv@s.free_lv_list;
						end;
					)s.succs;
				);
				if !b2_break=true then
				(
					List.iter(fun if_succs->
						if (!(is_in_block if_succs b1)=false)&&(!(is_in_block if_succs b2)=false) then
						begin
							if_succs.predicate_list <- cp_named_temp::if_succs.predicate_list@s.predicate_list;
							if_succs.free_lv_list <- !f_lv@s.free_lv_list;
						end;
					)s.succs;
				);
			end;
		
			generate_block_predicate b1;
			generate_block_predicate b2;
			();
		(*If End*)
		| Break(_)|Continue(_)->
			();
		(*Break End*)
		| Block(b2)->
			(*if (List.length s.predicate_list)>0 then*)
			List.iter(fun bs->
				bs.predicate_list <- s.predicate_list;
				bs.free_lv_list <- s.free_lv_list;
			)b2.bstmts;
		
			generate_block_predicate b2;
			();
		(*Block End*)
		| UnspecifiedSequence(seq)->
			let seq_block = Cil.block_from_unspecified_sequence seq in
			(*if (List.length s.predicate_list)>0 then*)
			List.iter(fun bs->
				bs.predicate_list <- s.predicate_list;
				bs.free_lv_list <- s.free_lv_list;
			)seq_block.bstmts;
		
			generate_block_predicate seq_block;
			();
		(*UnspecifiedSequence End*)
		| _->()
		(*match s.skind End*)
		)b.bstmts;(*List.iter End*)
	in
	
	generate_block_predicate loop_block;
	total_lt
	
let analysis_kf (kf:Cil_types.kernel_function) (linfo_list:logic_info list) (funsigs:(string,Loop_parameters.procsignature) Hashtbl.t) visitor (ipl:Property.identified_property list ref) wp_compute unknownout =
	try
	let fundec = Kernel_function.get_definition kf in
	List.iter(fun stmt ->
		match stmt.skind with
		| Loop(_,block,location,_,_) ->
			let loop = Translate.extract_loop stmt in
			List.iter(fun s->
				begin match loop.Equation.con.enode with
				| Lval _ | CastE _ | AddrOf _ | StartOf _ | UnOp _ | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ ->();
    		| _->
     			s.predicate_list <- (!Db.Properties.Interp.force_exp_to_predicate loop.Equation.con)::s.predicate_list;
     		end;
			)loop.Equation.body;
		 		
			Printf.printf "Enter Loop Now.\n";
			let vars = LiUtils.extract_varinfos_from_stmt stmt in
			let lvars = Varinfo.Set.elements vars in
			(*get value just before this loop stmt*)
			let oriValues = Hashtbl.create 3 and negoriValues = Hashtbl.create 3 in
			List.iter(fun v->
				let lv = Cil.var v in
					
				(*var as a term*)
				let tl = !Db.Properties.Interp.force_lval_to_term_lval lv in
				let tl = TLval(tl) in
				let tl = Logic_const.term ~loc:location tl (Ctype(v.vtype)) in
					
				let value = !Db.Value.access (Kstmt(stmt)) lv in
				begin match value with
				| Cvalue.V.Top(_,_)->
					Printf.printf "Top\n";
				| Cvalue.V.Map(_)->
					try
						let iv = Cvalue.V.project_ival value in(*Ival.t*)
						begin match iv with
						| Ival.Set(set)->Printf.printf "Set\n";
							let pset1 = ref [] and pset2 = ref [] in
						
							Array.iter(fun i->								
								let tr = Logic_const.term ~loc:location (TConst(CInt64(i,IInt,None))) (Ctype(v.vtype)) in
								let id_pre = Logic_const.new_predicate (Logic_const.prel (Req,tl,tr)) in
								let t_named = Logic_const.unamed ~loc:location id_pre.ip_content in
								pset1 := t_named::(!pset1);
								let id_pre = Logic_const.new_predicate (Logic_const.prel (Rneq,tl,tr)) in
								let t_named = Logic_const.unamed ~loc:location id_pre.ip_content in
								pset2 := t_named::(!pset2);
															
							)set;
							Hashtbl.add oriValues v (Logic_const.pands (!pset1));
							Hashtbl.add negoriValues v (Logic_const.pands (!pset2));
						
						| Ival.Float(_)->Printf.printf "Float\n";
						| Ival.Top(_,_,t1,t2)->Printf.printf "Top\n";(*interval;to1--min,to2--max*)							
							Printf.printf "%d," (My_bigint.to_int t1);Printf.printf "%d" (My_bigint.to_int t2);
							Printf.printf "\n";
						end;
					with Cvalue.V.Not_based_on_null->();
				end;
			)lvars;
		
		 	List.iter(fun linfo->
				visitor#add_pn kf linfo stmt (Varinfo.Set.elements vars);
			)linfo_list;
			
			Printf.printf "Analysis loop body now.\n";
			let total_lt = generate_loop_annotations kf stmt block linfo_list funsigs in
			total_lt := List.rev !total_lt;
			
			List.iter(fun (vars,freevar,conds,t_named)->
				let oriConds = ref [] and negoriConds = ref [] in
				(*assert*)
				List.iter(fun v->
					try
					let orinamed = Hashtbl.find oriValues v in
					oriConds := orinamed::(!oriConds);
					let negnamed = Hashtbl.find negoriValues v in
					negoriConds := negnamed::(!negoriConds);
					with Not_found->();
				)vars;
				
				(*condition transition*)
				let trans = Logic_const.unamed ~loc:location (Pimplies(conds,t_named)) in
				if (List.length freevar)==0 then
				begin
					let es = Logic_const.unamed ~loc:location (Pimplies(Logic_const.pands (!oriConds),(Logic_const.pnot ~loc:location trans))) in
					let prev = Logic_const.unamed ~loc:location (Pimplies(Logic_const.pands (!negoriConds),trans)) in
					
					
					let annot = Logic_const.new_code_annotation(AInvariant([],true,(Logic_const.pors [es;prev]))) in
					Cil.d_code_annotation Format.std_formatter annot;Format.print_flush ();Printf.printf "\n";
					let root_code_annot_ba = Cil_types.User(annot) in
					Annotations.add kf stmt [Ast.self] root_code_annot_ba;
					(*LiAnnot.prove_code_annot kf stmt annot ipl wp_compute unknownout;();*)
				end else
				begin
						let trans = Logic_const.unamed (Pforall(freevar,trans)) in
						let es = Logic_const.unamed ~loc:location (Pimplies(Logic_const.pands (!oriConds),(Logic_const.pnot ~loc:location trans))) in
						let prev = Logic_const.unamed ~loc:location (Pimplies(Logic_const.pands (!negoriConds),trans)) in
						
						let annot = Logic_const.new_code_annotation(AInvariant([],true,(Logic_const.pors [es;prev]))) in
						let root_code_annot_ba = Cil_types.User(annot) in
						Annotations.add kf stmt [Ast.self] root_code_annot_ba;
						(*LiAnnot.prove_code_annot kf stmt annot ipl wp_compute unknownout;();*)
				end;
			)!total_lt;
			Printf.printf "Analysis loop body over.\n";
			Printf.printf "Leave Loop Now.\n";
		| _ ->();
	)fundec.sallstmts(*List.iter end*)
	with Kernel_function.No_Definition->Printf.printf "The given function [%s] is not a definition.\n" (Kernel_function.get_name kf)
