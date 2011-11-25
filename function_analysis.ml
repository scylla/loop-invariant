open Cil
open Cil_types
open Cil_datatype
open File
open Annotations
open Kernel_function
open Logic_typing
open Visitor
open Project
open Callgraph
open Db
open Ast_printer
open Outputs
open Logic_const
open LiVisitor
open LiAnnot

(*
let locUnknown = ({Lexing.position.pos_fname="";},{Lexing.position.pos_fname="";})
	*)
(**统计函数中有多少个循环*)
(*let loop_number = ref 0;
let count_loop_number (funDec:Cil_types.fundec) = 
    List.iter (fun stmt ->
		match stmt.skind with
		| Loop(code_annotation , block , location , stmt1 , stmt2) -> 
			loop_number := !loop_number + 1;
		| _ -> loop_number := !loop_number;
	)funDec.sallstmts;
	!loop_number;
	
let d_stmt_option stmt = 
	match stmt with
	| None -> Printf.printf "%s" "None";
	| Some s ->Cil.d_stmt Format.std_formatter s;
	| _ -> Printf.printf "%s" "i donnot konw";

let p_stmt_succs stmt =
	match stmt with
	| None -> Printf.printf "\n";
	| Some s -> 
		List.iter(fun succe ->
			Cil.d_stmt Format.std_formatter succe;
		)s.succs;
		Printf.printf "\n";
	| _ -> Printf.printf "\n";

let p_stmt_preds stmt =
	match stmt with
	| None -> Printf.printf "\n";
	| Some s -> 
		List.iter(fun succe ->
			Cil.d_stmt Format.std_formatter succe;
		)s.preds;
		Printf.printf "\n";
	| _ -> Printf.printf "\n";

let p_stmt_value kinstr visitor =
	match kinstr with
	| Kstmt (stmt) -> 
		(
		match stmt.skind with
		| Instr (instr) ->
			(
			match instr with
			| Set(lval,exp,location) ->
				let lval2 = visitFramacLval visitor lval in
				!Ast_printer.d_lval Format.std_formatter lval2;
				let v1 = !Db.Value.access (Kstmt stmt) lval in
				let v2 = !Db.Value.access_after kinstr lval in
				Db.Value.pretty Format.std_formatter v1;
				Db.Value.pretty Format.std_formatter v2;
			| _ ->
				Printf.printf "not Set\n";
			);
		| _ ->
			Printf.printf "not Instr\n";
		);		
	| Kglobal ->
		Printf.printf "Kglobal\n";
			
let p_visitor visitor = 
	let kinstr=visitor#current_kinstr in
	p_stmt_value kinstr visitor;*)
		  	 
let generate_predicate_list_from_block pre_list (block:Cil_types.block) =
	()(*if (List.length block.bstmts)=0 then pre_list
	else
	(
	List.iter(fun stmt ->
		(
		match stmt.skind with
		| Instr(instr)->
			(
			match instr with
			| Set(lval,exp,location)->(*An assignment*)
				let lexpr = constFold true (stripCasts exp) in
				(
				match lexpr.enode with
				| UnOp(unop,exp,typ)->
					();
				| BinOp(binop,exp1,exp2,typ)->
				
					let tlval = !Db.Properties.Interp.force_lval_to_term_lval lval in
					let tr = !Db.Properties.Interp.force_exp_to_term exp in
					let tnode = TLval(tlval) in
					let tl = Logic_utils.mk_dummy_term tnode (Cil.typeOfLval lval) in
					let id_pre = Logic_const.new_predicate (Logic_const.prel (Req,tl,tr)) in
					let p_named = Logic_const.unamed ~loc:location id_pre.ip_content in
					let pre_list = p_named::pre_list in
					Printf.printf "pre_list.length1=%d\n" (List.length pre_list);
				| _->
					();
				);(*match lexpr.enode End*)
			| _->
				();
			);(*match instr End*)
		(*Instr End*)
		| Break(location)->
			();(*Break End*)
		| _->
			();(*match stmt.skind End*)
		);
	)block.bstmts;(*List.iter End*)
	Printf.printf "pre_list.length2=%d\n" (List.length pre_list);
	pre_list;
	);*)
	
let  generate_loop_annotations (kf:Cil_types.kernel_function) (loop_stmt:stmt) (loop_block:block) (linfo_list:logic_info list)  (assumes:predicate named list)  (visitor:liVisitor)=
	
	let lt = ref [] in
	let total_lt = ref [] in
	let count = ref 0 in
	let rec generate_block_predicate (b:block) =
	List.iter(fun s->
	
	match s.skind with
	| Instr(instr)->
		(
		match instr with
		| Set(lval,exp,location)->(*An assignment.i=i+1;lval:i;exp:i+1*)
			let texp = constFold true (stripCasts exp) in
			let tlval = !Db.Properties.Interp.force_lval_to_term_lval lval in
			let tr = !Db.Properties.Interp.force_exp_to_term exp in
			let tnode = TLval(tlval) in
			
			let is_in_lv_list (lv:logic_var) (l:logic_var list) = 
				let flag = ref false in
				List.iter(fun v->(
					if lv.lv_name=v.lv_name then flag := true;(*id?*)
				)
				)l;
				!flag;
			in
			
			let lvars = Cil.extract_varinfos_from_lval lval in
			let evars = Cil.extract_varinfos_from_exp exp in
			let levars = List.append (Varinfo.Set.elements lvars) (Varinfo.Set.elements evars) in
			let alvars = ref [] in
			let llvars = ref [] in
			let elvars = ref [] in
			let lelvars = ref [] in
			
			List.iter(fun cv->
				let lv = Cil.cvar_to_lvar cv in
				if (is_in_lv_list lv s.free_lv_list)=false then	lelvars := lv::!lelvars;
			)levars;
			
			List.iter(fun lv->
				if (is_in_lv_list lv !lelvars)=false then alvars := lv::!alvars;
			)s.free_lv_list;
			
			List.iter(fun cv->
				if (is_in_lv_list (Cil.cvar_to_lvar cv) s.free_lv_list)=false then llvars := (Cil.cvar_to_lvar cv)::!llvars;
			)(Varinfo.Set.elements lvars);
			
			List.iter(fun cv->
				if (is_in_lv_list (Cil.cvar_to_lvar cv) s.free_lv_list)=false then elvars := (Cil.cvar_to_lvar cv)::!elvars;
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
				Printf.printf "alvars.len=%d\n" (List.length !alvars);
				(*t_named := Logic_const.unamed (Pexists (!llvars,(Logic_const.unamed (Pimplies (con_named,!t_named)))));
				t_named := Logic_const.unamed (Pforall (s.free_lv_list@(!elvars),!t_named));*)
				t_named := Logic_const.unamed (Pexists (!lelvars,(Logic_const.unamed (Pimplies (con_named,!t_named)))));
				t_named := Logic_const.unamed (Pforall (!alvars,!t_named));
				(*t_named := Logic_const.unamed (Pforall (s.free_lv_list@(!elvars),(Logic_const.unamed (Pimplies (con_named,!t_named)))));*)
			end
			else
			begin
				Printf.printf "alvars.len==0\n";
				t_named := Logic_const.unamed (Pforall (s.free_lv_list@(!elvars),(Logic_const.unamed (Pimplies (con_named,!t_named)))));
			end;
			
			lt := !t_named::!lt;
			total_lt := !lt::!total_lt;
			lt := [];
			();
		(*Set End*)
		| _->
			();(*match instr End*)
		);
		total_lt := !lt::!total_lt;lt := [];();
	(*Instr End*)
	| If(exp_temp,b1,b2,l)->
		Printf.printf "if con:\n";Cil.d_exp Format.std_formatter exp_temp;Format.print_flush ();Printf.printf "\n";			
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
		
		let is_in_lv_list (lv:logic_var) (l:logic_var list) = 
			let flag = ref false in
			List.iter(fun v->(
				if lv.lv_id=v.lv_id then flag := true;
			)
			)l;
			flag;
		in
		
		let f_lv = ref [] in
		List.iter(fun lv->(
			if !(is_in_lv_list lv s.free_lv_list)=false then f_lv := lv::!f_lv;
		)
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
			List.iter(fun s0->(
				if s.sid=s0.sid then flag := true;
			)
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
	| Break(location)|Continue(location)->
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
	)b.bstmts;(*List.iter End*)
	!lt;
	in
	
	generate_block_predicate loop_block;
	total_lt
	
let extract_varinfos_from_stmt (s:stmt) =
  let visitor = object
    inherit nopCilVisitor
    val mutable varinfos = Varinfo.Set.empty;
    method varinfos = varinfos
    method vvrbl (symb:varinfo) =
      varinfos <- Varinfo.Set.add symb varinfos;
      SkipChildren
  end
  in ignore (visitCilStmt (visitor :> nopCilVisitor) s) ;
    visitor#varinfos
    
let analysis_kf (kf:Cil_types.kernel_function) (linfo_list:logic_info list) (assumes:predicate named list) (visitor:liVisitor)= 
	try
	let fundec = Kernel_function.get_definition kf in
	List.iter( fun stmt ->
		(
		match stmt.skind with
		| If(exp,block1,block2,location)->
			Printf.printf "if con:\n";Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";
		  	let texp = constFold true (stripCasts exp) in
		  	(
		  	match texp.enode with
		  	| BinOp((Div|Mod|Mult|PlusA|MinusA),exp1,exp2,typ)->
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
		  	| _->
		  		Printf.printf "\n";
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
		  	| Set(lval,exp,location)->
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
		 	List.iter(fun s->
		 		Cil.d_stmt Format.std_formatter s;Format.print_flush ();Printf.printf "\n";
		 	)stmt.succs;
		 	let vars = extract_varinfos_from_stmt stmt in
		 	List.iter(fun linfo->
				visitor#add_pn kf linfo stmt (Varinfo.Set.elements vars);
			)linfo_list;
		 	(
		 	match stmto1 with(*continue*)
		 	| Some(s)->
		 		let con = List.nth s.succs 0 in
		 		let ocon = Cil.get_original_stmt (Cil.inplace_visit ()) con in
		 		Printf.printf "continue:\n";Cil.d_stmt Format.std_formatter con;Format.print_flush ();Printf.printf "\n";
			  	(
			  	match con.skind with
			  	| If(exp,b1,b2,l)->
			  		Printf.printf "if con:\n";Cil.d_exp Format.std_formatter exp;Format.print_flush ();Printf.printf "\n";
					let vars = Cil.extract_varinfos_from_exp exp in
					();
					(*List.iter(fun linfo->
						visitor#add_pn kf linfo stmt (Varinfo.Set.elements vars);
					)linfo_list;*)
			  	| _->();
			  	);
		 	| None->();
		 	);
		 	(
		 	match stmto2 with(*break*)
		 	| Some(s)->
		 		Cil.d_stmt Format.std_formatter s;
			  	Format.print_flush ();
			  	Printf.printf "\n";
		 	| None->();
		 	);
		 	Printf.printf "Analysis loop body now.\n";
		 	let total_lt = generate_loop_annotations kf stmt block linfo_list assumes visitor in
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
					prove_code_annot kf stmt annot;();
				);
			)!total_lt;
		 	Printf.printf "Analysis loop body over.\n";
			List.iter(fun pn->
				let annot = Logic_const.new_code_annotation(AInvariant([],true,pn)) in
				let root_code_annot_ba = Cil_types.User(annot) in
				Annotations.add kf stmt [Ast.self] root_code_annot_ba;
				prove_code_annot kf stmt annot;
			)assumes;
		 	Printf.printf "Leave Loop Now.\n";
		 | Block(block) ->
		  	();
		 | Return(expo,location) ->
		  	();
		 | _ ->
		  	Printf.printf "\n";
		 );
		Printf.printf "\n";
	)fundec.sallstmts(*List.iter end*)
	with No_Definition->Printf.printf "The given function [%s] is not a definition.\n" (Kernel_function.get_name kf)

let analysis_assert (kf:Cil_types.kernel_function) =
	match kf.fundec with
	| Declaration(spec,var,varl,l)->
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
(**语句类型*)
(*let print_function_stmt_kind stmt visitor= 
	(*let loop_visitor = new Visitor.frama_c_inplace in
	Format.print_string "begin visit stmt\n";
	Visitor.visitFramacStmt loop_visitor stmt;
	Format.print_string "end visit stmt\n";*)
	match stmt.skind with
	| ( Instr ( instr ) ) ->
		Format.print_string "instr\n";
			(*Visitor.visitFramacInstr loop_visitor instr;
			Format.print_string "\n";*)
	| ( Return ( exp , location ) )->
		Cil.d_loc Format.std_formatter location;
		Format.print_string "return\n";
	| ( Goto ( stmt , location) ) ->
		Format.print_string "goto\n";
	| ( Break ( location ) ) ->
		Format.print_string "break\n";
	| ( Continue ( location ) ) ->
		Format.print_string "continue\n";
	| ( If ( expr , block1 , block2 , location ) ) ->
		Format.print_string "if\n";
		(
		match expr.enode with
		| Lval (lval) ->
			let value = !Db.Value.access visitor#current_kinstr lval in
			Db.Value.pretty Format.std_formatter value;
			Printf.printf "%s\n" "Lval";
		| _ ->
			Printf.printf "%s\n" "i donnot konw";
		);
	| ( Switch ( expr , block , stmtl , location ) ) ->
		Format.print_string "switch\n";
	| ( Loop ( code_annotation , block , location , stmt1 , stmt2 ) ) ->
			(*Printf.printf "new_loc.loc_plnum=%d\n" (fst location).Lexing.pos_lnum;
			let new_loc = location in
			let lnum = (fst location).Lexing.pos_lnum in
			(fst new_loc).Lexing.pos_lnum := !lnum+1;
			let exp = Cil.mkString new_loc "mkString" in*)
		Format.print_string "loop\n";
		let (p1,p2) = location in
		let mkPosition location : Lexing.position (*pos_fname pos_lnum pos_bol pos_cnum*) =
			{Lexing.pos_fname=(location).Lexing.pos_fname;
			pos_lnum=(location).Lexing.pos_lnum+2;
			pos_bol=(location).Lexing.pos_bol;
			pos_cnum=(location).Lexing.pos_cnum;} in
				
		let new_loc = mkPosition (fst location) in
			
		Printf.printf "new_loc.pos_fname=%s\n" (p1).Lexing.pos_fname;
		(p1).Lexing.pos_lnum=(p1).Lexing.pos_lnum+1;
		Printf.printf "new_loc.loc_lnum=%d\n" (new_loc).Lexing.pos_lnum;
		let guard = Cil.mkString (new_loc,p2) "mkString op" in
			
		let mystmt = mkStmt ~ghost:false ~valid_sid:true (Break (new_loc,p2)) in
		let myifstmt=mkStmt ~ghost:false ~valid_sid:false (If (guard,block,block,(new_loc,p2))) in
			(**停不了了*)
			
		Printf.printf "%s\n" "mystmt begin";
		Cil.d_stmt Format.std_formatter myifstmt;
		Printf.printf "\n%s\n" "mystmt end";
		let stmtl=[mystmt;] in
		let mywhilestmt = Cil.mkWhile guard stmtl in
		Printf.printf "%s\n" "我的语句begin";
		List.iter(fun sm -> 
			Cil.d_stmt Format.std_formatter sm;
		)mywhilestmt;
		Printf.printf "\n%s\n" "我的语句end";
	| ( Block ( block ) ) ->
		Format.print_string "block\n";
			(*Visitor.visitFramacBlock loop_visitor block;
			Format.print_string "\n";*)
	| ( UnspecifiedSequence (_) ) ->
		Format.print_string "unspecifiedSequence\n";
	| ( TryFinally ( block1 , block2 , location ) ) ->
		Format.print_string "TryFinally\n";
	| ( TryExcept ( block1 , ( instr , exp ) , block2 , location ) ) ->
		Format.print_string "TryExcept\n";
	| ( _ ) ->
		Format.print_string "other\n";
			
(**打印所有语句*)
let print_function_stmts fundec visitor= 
	List.iter (fun stmt ->
		p_visitor visitor;
		Printf.printf "\n";
	)fundec.sallstmts;

let rec print_block block visitor = 
	List.iter(fun stmt ->
		(
		match stmt.skind with
		| Instr (instr) ->
			(
			match instr with
			| Set(lval,exp,location) ->
							
				let texp = constFold true (stripCasts exp) in							
				Printf.printf "--------add_alarm\n";
				Cil.d_exp Format.std_formatter texp;
				let annot = !Db.Properties.Interp.force_exp_to_assertion texp in
				Cil.d_code_annotation Format.std_formatter annot;
				Printf.printf "++++++++add_alarm\n";
			| Call(lvalo,exp,expl,loc) ->
				visitor#vexpr exp;
				match lvalo with
				| Some l ->
					let v1 = !Db.Value.access (Kstmt stmt) l in
					Printf.printf "----call v1\n";
					Db.Value.pretty Format.std_formatter v1;
					Printf.printf "\n";
					Printf.printf "++++call v1\n";
										
				| _ ->
					Printf.printf "lvalo\n";
			| Code_annot(code_annotation,location) ->
				Printf.printf "Code_annot\n";
			| Skip(location) ->
				Printf.printf "Skip\n";
			| _ ->
				Printf.printf "Asm\n";(*end match instr*)
			);
		| Loop (code_annotation , subblock , location , stmt1 , stmt2) ->
			Printf.printf "print_block:loop\n";
			print_block subblock visitor;
			Printf.printf "\n";
		| Block (subblock) ->
			Printf.printf "print_block:block\n";
			print_block subblock visitor;
			Printf.printf "\n";
		| _ ->
			Printf.printf "not Instr\n";
		);
	)block.bstmts;
	
let print_function_body (fundec:fundec) visitor= 
	print_block fundec.sbody visitor;
	
let visit_cilfile file = 
	let loop_visitor = new Visitor.frama_c_inplace in
	Printf.printf "%s\n" "before visit";
	Visitor.visitFramacFile loop_visitor file;
	
let print_proj_info = 
	Printf.printf "Project.name:%s\n" Project.name;

(**get loop information*)
let get_loop_infor fundec = 
	List.iter (fun stmt ->
		(
		match stmt.skind with
		| Loop (code_annotation , block , location , stmt1 , stmt2) ->
			Printf.printf "loop info\n";
			(*
					let (p1,p2) = location in
					let mkPosition location : Lexing.position (*pos_fname pos_lnum pos_bol pos_cnum*) =
						{Lexing.pos_fname=(location).Lexing.pos_fname;
						pos_lnum=(location).Lexing.pos_lnum+2;
						pos_bol=(location).Lexing.pos_bol;
						pos_cnum=(location).Lexing.pos_cnum;} in
					
					let new_loc = mkPosition (fst location) in
				
					Printf.printf "new_loc.pos_fname=%s\n" (p1).Lexing.pos_fname;
					(p1).Lexing.pos_lnum=(p1).Lexing.pos_lnum+1;
					Printf.printf "new_loc.loc_lnum=%d\n" (new_loc).Lexing.pos_lnum;
					let guard = Cil.mkString (new_loc,p2) "mkString op" in
				
					let mystmt = mkStmt ~ghost:false ~valid_sid:true (Break (new_loc,p2)) in
					let myifstmt=mkStmt ~ghost:false ~valid_sid:false (If (guard,block,block,(new_loc,p2))) in
					(**停不了了*)
				
					Printf.printf "%s\n" "mystmt begin";
					Cil.d_stmt Format.std_formatter myifstmt;
					Printf.printf "\n%s\n" "mystmt end";
					let stmtl=[mystmt;] in
					let mywhilestmt = Cil.mkWhile guard stmtl in
					Printf.printf "%s\n" "我的语句begin";
					List.iter(fun sm -> 
						Cil.d_stmt Format.std_formatter sm;
					) mywhilestmt;
					Printf.printf "\n%s\n" "我的语句end";*)
		| _ -> 
			Printf.printf "other info\n";
		);
	)fundec.sallstmts;*)
