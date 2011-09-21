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
open Db_types
open Db
open Ast_printer
open Outputs
open Logic_const

type sequence = stmt * lval list * lval list * lval list * stmt ref list

let loop_number = ref 0
(*
let locUnknown = ({Lexing.position.pos_fname="";},{Lexing.position.pos_fname="";})
	*)		
(**统计函数中有多少个循环*)
let count_loop_number (funDec:Cil_types.fundec) = 
    List.iter (fun stmt ->
       match stmt.skind with
			| Loop(code_annotation , block , location , stmt1 , stmt2) -> 
				loop_number := !loop_number + 1;
			| _ -> loop_number := !loop_number;
		) funDec.sallstmts;
		!loop_number
		
let d_stmt_option stmt = 
		match stmt with
			| None -> Printf.printf "%s" "None"
			| Some s ->Cil.d_stmt Format.std_formatter s
			| _ -> Printf.printf "%s" "i donnot konw"

let p_stmt_succs stmt =
	match stmt with
		| None -> Printf.printf "\n"
		| Some s -> List.iter(fun succe ->
			Cil.d_stmt Format.std_formatter succe;
			)s.succs;
			Printf.printf "\n"
		| _ -> Printf.printf "\s"

let p_stmt_preds stmt =
	match stmt with
		| None -> Printf.printf "\n"
		| Some s -> List.iter(fun succe ->
			Cil.d_stmt Format.std_formatter succe;
			)s.preds;
			Printf.printf "\n"
		| _ -> Printf.printf "\s"

let p_stmt_value kinstr visitor =
	match kinstr with
		| Kstmt (stmt) -> 
			(match stmt.skind with
				| Instr (instr) ->
					(match instr with
						| Set(lval,exp,location) ->
							let lval2 = visitFramacLval visitor lval in
							!Ast_printer.d_lval Format.std_formatter lval2;
							let v1 = !Db.Value.access (Kstmt stmt) lval in
							let v2 = !Db.Value.access_after kinstr lval in
							Db.Value.pretty Format.std_formatter v1;
							Db.Value.pretty Format.std_formatter v2
						| _ ->
							Printf.printf "not Set\n"
					)
				| _ ->
					Printf.printf "not Instr\n"
			)			
		| Kglobal ->
			Printf.printf "Kglobal\n"
			
let p_visitor visitor = 
	let kinstr=visitor#current_kinstr in
	p_stmt_value kinstr visitor

let rec generate_predicate_list_from_block pre_list block =
	if (List.length block.bstmts)=0 then pre_list
	else
	begin
	List.iter(fun stmt ->
	match stmt.skind with
	| Instr(instr)->(
		match instr with
		| Set(lval,exp,location)->((*An assignment*)
			let lexpr = constFold true (stripCasts exp) in
			match lexpr.enode with
			| UnOp(unop,exp,typ)->(
				Printf.printf "UnOp\n";
				Cil.d_exp Format.std_formatter exp;
				Format.print_flush ();
				Printf.printf "\n";
			
				Cil.d_lval Format.std_formatter lval;
				Format.print_flush ();
				Printf.printf "\n";
			
				Cil.d_exp Format.std_formatter lexpr;
				Format.print_flush ();
				Printf.printf "\n";
			)
			| BinOp(binop,exp1,exp2,typ)->(
				Printf.printf "BinOp\n";
				
				let tlval = !Db.Properties.Interp.force_lval_to_term_lval lval in
				let tr = !Db.Properties.Interp.force_exp_to_term exp in
				let tnode = TLval(tlval) in
				let tl = Logic_utils.mk_dummy_term tnode (Cil.typeOfLval lval) in
				let id_pre = Logic_const.new_predicate (Logic_const.prel (Req,tl,tr)) in
				let p_named = Logic_const.unamed ~loc:location id_pre.ip_content in
				let pre_list = p_named::pre_list in
				Printf.printf "pre_list.length1=%d\n" (List.length pre_list);
				()
			)
			| _->(
			);(*match lexpr.enode End*)
			()
		)
		| _->(
		);(*match instr End*)
		
	)(*Instr End*)
	| Break(location)->(
	)(*Break End*)
	| _->(
	);(*match stmt.skind End*)	
	)block.bstmts;(*List.iter End*)
	Printf.printf "pre_list.length2=%d\n" (List.length pre_list);
	pre_list
	end
	
let rec generate_loop_annotations (loop_stmt:stmt) (loop_block:block)=
	(*match loop_stmt.skind with
	| Loop(code_annot_list,block,location,stmto1,stmto2)->*)
	(*Printf.printf "generate_predicate_list_from_block---\n";	
	let p_list = generate_predicate_list_from_block [] loop_block in
	Printf.printf "p_list.length=%d\n" (List.length p_list);
	List.iter(fun p->
	Cil.d_predicate_named Format.std_formatter p;
	Format.print_flush ();
	)p_list;
	Printf.printf "generate_predicate_list_from_block+++\n";*)	
	
	let lt = ref [] in
	let total_lt = ref [] in
	let count = ref 0 in
		
	let rec generate_block_predicate (b:block) =
	List.iter(fun s->
	(*Printf.printf "count=%d\n" !count;
	Cil.d_stmt Format.std_formatter s;
	Format.print_flush ();
	Printf.printf "\n\n";
	count := !count+1;*)
	
	match s.skind with
	| Instr(instr)->(
		match instr with
		| Set(lval,exp,location)->((*An assignment*)
			let texp = constFold true (stripCasts exp) in
			let tlval = !Db.Properties.Interp.force_lval_to_term_lval lval in
			let tr = !Db.Properties.Interp.force_exp_to_term exp in
			let tnode = TLval(tlval) in
			
			let is_in_lv_list (lv:logic_var) (l:logic_var list) = 
				let flag = ref false in
				List.iter(fun v->(
					if lv.lv_id=v.lv_id then flag := true;
				)
				)l;
				!flag;
			in
			let lvars = Cil.extract_varinfos_from_lval lval in
			let evars = Cil.extract_varinfos_from_exp texp in
			let llvars = ref [] in
			let elvars = ref [] in
			List.iter(fun cv->(
				if (is_in_lv_list (Cil.cvar_to_lvar cv) s.free_lv_list)=false then llvars := (Cil.cvar_to_lvar cv)::!llvars;
			)
			)(Varinfo.Set.elements lvars);
			List.iter(fun cv->(
				if (is_in_lv_list (Cil.cvar_to_lvar cv) s.free_lv_list)=false then elvars := (Cil.cvar_to_lvar cv)::!elvars;
			)
			)(Varinfo.Set.elements evars);
			
			let tl = Logic_utils.mk_dummy_term tnode (Cil.typeOfLval lval) in
			
			
			let id_pre = Logic_const.new_predicate (Logic_const.prel (Req,tl,tr)) in(*only Req now*)
			let t_named = ref (Logic_const.unamed ~loc:location id_pre.ip_content) in			
			let con_named = Logic_const.pands (List.rev s.predicate_list) in
			if (List.length !llvars)!=0 then
			begin
				t_named := Logic_const.unamed (Pexists (!llvars,(Logic_const.unamed (Pimplies (con_named,!t_named)))));
				t_named := Logic_const.unamed (Pforall (s.free_lv_list@(!elvars),!t_named));
			end
			else
			begin
				t_named := Logic_const.unamed (Pforall (s.free_lv_list@(!elvars),(Logic_const.unamed (Pimplies (con_named,!t_named)))));
			end;
			
			lt := !t_named::!lt;
			total_lt := !lt::!total_lt;
			lt := [];
			();
		)(*Set End*)
		| _->(
		);(*match instr End*)
		total_lt := !lt::!total_lt;lt := [];
	)(*Instr End*)
	| If(exp_temp,b1,b2,l)->(
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
	)(*If End*)
	| Break(location)|Continue(location)->(
		();
	)(*Break End*)
	| Block(b2)->(
		(*if (List.length s.predicate_list)>0 then*)	
		List.iter(fun bs->(
			bs.predicate_list <- s.predicate_list;
			bs.free_lv_list <- s.free_lv_list;
		)
		)b2.bstmts;
		
		generate_block_predicate b2;();
	)(*Block End*)
	| UnspecifiedSequence(seq)->(
		let seq_block = Cil.block_from_unspecified_sequence seq in
		(*if (List.length s.predicate_list)>0 then*)
		List.iter(fun bs->(
			bs.predicate_list <- s.predicate_list;
			bs.free_lv_list <- s.free_lv_list;
		)
		)seq_block.bstmts;
		
		generate_block_predicate seq_block;
		();
	)(*UnspecifiedSequence End*)
	| _->(
	);(*match s.skind End*)
	)b.bstmts;(*List.iter End*)
	!lt;
	in
	
	generate_block_predicate loop_block;
	total_lt

let prove_kf (kf:Db_types.kernel_function) = 
	Printf.printf "prove_kf\n";
	List.iter(fun bhv->
	Printf.printf "%s\n" bhv;
	)(Kernel_function.all_function_behaviors kf);
	
	(*let fundec = Kernel_function.get_definition kf in
	List.iter(fun stmt->
	)fundec.sallstmts;*)
	
	let annot_list = Kernel_function.code_annotations kf in
	List.iter(fun (stmt,root_code_annot_ba) ->
	match root_code_annot_ba with
	| Before(annot)|After(annot) ->
		match annot with
		| User(code_annot)|AI(_,code_annot) ->
			let ip_list = Property.ip_of_code_annot kf stmt code_annot in
			List.iter(fun ip->
				Prove.prove_predicate kf (Some(Kernel_function.all_function_behaviors kf)) (Some(ip));
				Format.print_flush ();
				let result = Properties_status.get_all  ip in
				List.iter(fun status->
					match status with
					| Unknown->
						Printf.printf "unknown\n";
					| Checked(checked_status)->
						if checked_status.valid=True then
							(Printf.printf "true\n";)
						else if checked_status.valid=False then
							(Printf.printf "False\n";)
						else if checked_status.valid=Maybe then
							(Printf.printf "Maybe\n";)
					;
					Format.print_flush ();				
				)result;
			)ip_list;
	)annot_list;
	()

let print_kf_global (global:global) =
	match global with
	| GType(typeinfo,location) -> (
		  Printf.printf "GType\n";
	)
	| GCompTag(compinfo,location) -> (
		  Printf.printf "GCompTag\n";
	)
	| GCompTagDecl(compinfo,location) -> (
		  Printf.printf "GCompTagDecl\n";
	)
	| GEnumTag(enuminfo,location) -> (
		  Printf.printf "GEnumTag\n";
	)
	| GEnumTagDecl(enuminfo,location) -> (
		  Printf.printf "GEnumTagDecl\n";
	)
	| GVarDecl(funspec,varinfo,location) -> (
		  Cil.d_funspec Format.std_formatter funspec;
	)
	| GVar(varinfo,initinfo,location) -> (
		 Printf.printf "GVar\n";
	)
	| GFun(fundec,location) -> (		
      	(*Cfg.prepareCFG fundec;*)
		List.iter( fun stmt ->		  		
		(
		match stmt.skind with
		| If(exp,block1,block2,location)->(
			
		  	let texp = constFold true (stripCasts exp) in
		  	(
		  	match texp.enode with
		  	| Const(constant)->(
		  		Printf.printf "\n";
		  	)
		  	| Lval(lval)->(
		  		Printf.printf "\n";
		  	)
		  	| SizeOf(typ)->(
		  		Printf.printf "\n";
		  	)
		  	| SizeOfE(exp)->(
		  		Printf.printf "\n";
		  	)
		  	| SizeOfStr(s:string)->(
		  		Printf.printf "\n";
		  	)
		  	| AlignOf(typ)->(
		  		Printf.printf "\n";
		  	)
		  	| AlignOfE(exp)->(
		  		Printf.printf "\n";
		  	)
		  	| UnOp(upop,exp,typ)->(
		  		Printf.printf "\n";
		  	)
		  	| BinOp((Div|Mod|Mult|PlusA|MinusA),exp1,exp2,typ)->(
		  		Cil.d_type Format.std_formatter typ;
		  		Format.print_flush ();
		  		Printf.printf "Div\n";		
		  	)
		  	| BinOp((Lt|Gt|Le|Ge),exp1,exp2,typ)->(
		  		Cil.d_type Format.std_formatter typ;
		  		Format.print_flush ();
		  		Printf.printf "not equal\n";
		  		let lexpr = Logic_utils.expr_to_term ~cast:true exp2 in
		  		let pre_named = !Db.Properties.Interp.force_exp_to_predicate texp in
		  		
		  		(*if while_stmt.skind=Loop(_,_,_,_,_) then*)
		  		let free_vars = Cil.extract_free_logicvars_from_predicate pre_named in
		  		
		  		let add_code_annot (free_vars:Cil_datatype.Logic_var.Set.t) =
		  			let annotation =
				      Logic_const.new_code_annotation
				      (AAssert ([],Logic_const.unamed (Prel (Rneq,lexpr, lzero()))))
		       		in
		       		let assert_root_code_annot_ba = Db_types.Before(Db_types.User(annotation)) in
		       		Annotations.add stmt [Ast.self] assert_root_code_annot_ba;
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
		  		
           		
		  		
		  		Printf.printf "not equal\n";
		  		(*let term = !Db.Properties.Interp.force_exp_to_term texp in
		  		let new_code_annot = Logic_const.new_code_annotation (term,*)	  		
		  	)
		  	| CastE(typ,exp)->(
		  		Printf.printf "\n";
		  	)
		  	| AddrOf(lval)->(
		  		Printf.printf "\n";
		  	)
		  	| StartOf(lval)->(
		  		Printf.printf "\n";
		  	)
		  	| Info(exp,exp_info)->(
		  		Printf.printf "\n";
		  	)
		  	| _->(
		  		Printf.printf "\n";
		  	)
		  	);
		  	Printf.printf "if--:\n";
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
		  	
		  	Printf.printf "if++:\n";
		 )(*end If*)
		 | Instr(instr) ->(
		 	Printf.printf "instr--:\n";	  			
		  	Cil.d_instr Format.std_formatter instr;
		  	Format.print_flush ();
		  	Printf.printf "\n";
		  	match instr with
		  	| Set(lval,exp,location)->(
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
			)
			| _->(
			);(*match instr End*)
		  	Format.print_flush ();
		  	Printf.printf "instr++:\n";
		 )
		 | Loop(code_annot_list,block,location,stmto1,stmto2) ->(
		 	Printf.printf "Enter Loop Now.\n";
		 	
		 	let total_lt = generate_loop_annotations stmt block in
		 	Printf.printf "total_lt.length=%d\n" (List.length !total_lt);
		 	total_lt := List.rev !total_lt;
		 	List.iter(fun tl->(	
				(*let tl = List.rev tl in*)
				let t_named = Logic_const.pands tl in
			
				let annot = Logic_const.new_code_annotation(AInvariant([],true,t_named)) in
				let root_code_annot_ba = Db_types.Before(Db_types.User(annot)) in
				Annotations.add stmt [Ast.self] root_code_annot_ba;
			)
			)!total_lt;
			  	
		 	Printf.printf "Leave Loop Now.\n";
		 )
		 | Block(block) ->(
		  	Printf.printf "block--:\n";
		 )
		 | Return(expo,location) ->(
		  	Printf.printf "return--:\n";
		 )
		 | _ ->(
		  	Printf.printf "\n";
		 )
		 );
		Printf.printf "\n";
		)fundec.sallstmts;(*List.iter end*)	
		)(*CFun end*)
		| GAsm(s,location) -> (
		  	Printf.printf "s\n";
		)
		| GPragma(attribute,location) -> (
		  	Printf.printf "GPragma\n";
		)
		| GText(s) -> (
			Printf.printf "GText\n";
		)
		| GAnnot(global_annotation,location) -> (
		)
		| _ -> (
			Printf.printf "\n";
		)
		  	
(**语句类型*)
let print_function_stmt_kind stmt visitor= 
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
			Format.print_string "return\n"
		| ( Goto ( stmt , location) ) ->
			Format.print_string "goto\n"
		| ( Break ( location ) ) ->
			Format.print_string "break\n"
		| ( Continue ( location ) ) ->
			Format.print_string "continue\n"
		| ( If ( expr , block1 , block2 , location ) ) ->
			Format.print_string "if\n";
			(match expr.enode with
				| Lval (lval) ->
					(
						match lval with
							| (Var (varinfo) , _) ->
								Printf.printf "%s\n" varinfo.vname;
							| (Mem (mem), _) ->
								Printf.printf "%s\n" "mem";
						);
					let value = !Db.Value.access visitor#current_kinstr lval in
					Db.Value.pretty Format.std_formatter value;
					Printf.printf "%s\n" "Lval";
				| _ ->
					Printf.printf "%s\n" "i donnot konw";);
		| ( Switch ( expr , block , stmtl , location ) ) ->
			Format.print_string "switch\n"
		| ( Loop ( code_annotation , block , location , stmt1 , stmt2 ) ) ->
			(*Printf.printf "new_loc.loc_plnum=%d\n" (fst location).Lexing.pos_lnum;
			let new_loc = location in
			let lnum = (fst location).Lexing.pos_lnum in
			(fst new_loc).Lexing.pos_lnum := !lnum+1;
			let exp = Cil.mkString new_loc "mkString" in*)
			Format.print_string "loop\n";
			Printf.printf "%s\n" "----code_annotation";
			List.iter(fun anno ->
				Cil.d_code_annotation Format.std_formatter anno;
				) code_annotation;
			Printf.printf "%s\n" "++++code_annotation";
			Printf.printf "%s\n" "----block";
			Cil.d_block Format.std_formatter block;
			Printf.printf "%s\n" "++++block";
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
			Printf.printf "\n%s\n" "我的语句end";
			
			(*Format.print_string "loop\n";
			Printf.printf "%s" "循环位置:";
			Cil.d_loc Format.std_formatter location;
			List.iter (fun codeAnnot ->
			Cil.d_code_annotation Format.std_formatter codeAnnot;
			) code_annotation;
			Cil.d_block Format.std_formatter block;
			Printf.printf "stmt1:%s" "\n";
			d_stmt_option stmt1;
			Printf.printf "stmt2:%s" "\n";
			d_stmt_option stmt2;
			Printf.printf "%s" "**\n";*)
		| ( Block ( block ) ) ->
			Format.print_string "block\n";
			(*Visitor.visitFramacBlock loop_visitor block;
			Format.print_string "\n";*)
		| ( UnspecifiedSequence (quence : sequence list) ) ->
			Format.print_string "unspecifiedSequence\n"
		| ( TryFinally ( block1 , block2 , location ) ) ->
			Format.print_string "TryFinally\n"
		| ( TryExcept ( block1 , ( instr , exp ) , block2 , location ) ) ->
			Format.print_string "TryExcept\n"
		| ( _ ) ->
			Format.print_string "other\n"
			
			
(**打印所有语句*)
let print_function_stmts fundec visitor= 
	List.iter (fun stmt ->
		(*Format.print_bool stmt.ghost;
		Format.print_int stmt.sid;
		Format.print_string "\n";*)
		(*Printf.printf "%s" "语句类型为:";
		print_function_stmt_kind stmt visitor;
		Printf.printf "%s" "语句的内容为:";
		Cil.d_stmt Format.std_formatter stmt;
		Format.print_string "\n";
		visitor#vstmt stmt; DoChildren;*)
		(*let s2 = Visitor.visitFramacStmt visitor stmt in
		visitor#push_stmt stmt;*)
		p_visitor visitor;
		(*visitor#pop_stmt stmt;*)
		Printf.printf "\n";
		) fundec.sallstmts

let rec print_block block visitor = 
	List.iter(fun stmt ->
		Printf.printf "--------stmt\n";
		Printf.printf "		--------stmt\n		";
		Cil.d_stmt Format.std_formatter stmt;
		Printf.printf "\n		++++++++stmt\n";
		(match stmt.skind with
				| Instr (instr) ->
					(match instr with
						| Set(lval,exp,location) ->(
							
							let texp = constFold true (stripCasts exp) in
							
							Printf.printf "--------add_alarm\n";
							Cil.d_exp Format.std_formatter texp;
							let annot = !Db.Properties.Interp.force_exp_to_assertion texp in
							(*Annotations.add_assert stmt [] ~before:true pre;
							Cil.d_predicate_named Format.std_formatter pre;*)
							Cil.d_code_annotation Format.std_formatter annot;
							Printf.printf "++++++++add_alarm\n";
							
							
							match texp.enode with
							| Lval(l) ->(
								Printf.printf "lval\n"
							)
							| BinOp(op, l, r, tt) ->(
								(*visitor#vexpr texp;
								Printf.printf "\n\n\n\n";*)
								(*Cil.d_exp Format.std_formatter l;
								Cil.d_binop Format.std_formatter op;(*obtaint binary operator*)
								Cil.d_exp Format.std_formatter r;
								Cil.d_type Format.std_formatter tt;*)
								Printf.printf "\nbinop\n"
							)
							| _ ->(
								()
							)(*end match texp.enode*)
							
							(*let host, off = lval in                     
		    				let typ = Cil.unrollType (Cil.typeOfLval lval) in
		    				match typ with
		    				| TInt(k,attr) ->(
		    					match host with
		    					| Var varinfo ->(
		    						match off with
		    						| Index(exp,toff) ->(
		    							Printf.printf "index\n"
		    						)
		    						| NoOffset ->(
		    							Printf.printf "noOffSet\n"
		    						)
		    						| Field (fieldinfo, toff) ->(
		    							Printf.printf "field\n"
		    						)
		    					)
		    					| Mem mexp ->(
		    						Printf.printf "mem\n"
		    					)
		    				)
		    				| TPtr(ttyp, attr) ->(
		    					Printf.printf "TPtr\n"
		    				)
		    				| _ ->()*)
		    			)
							(*let lval2 = visitFramacLval visitor lval in
							!Ast_printer.d_lval Format.std_formatter lval2;*)
							(*Printf.printf "lval=";
							Cil.d_lval Format.std_formatter lval;
							Printf.printf "\n";
							visitor#vexpr exp;
							Printf.printf "\n";*)
							(*let v1 = !Db.Value.access (Kstmt stmt) lval in
							Printf.printf "----set v1v2\n";
							Db.Value.pretty Format.std_formatter v1;
							Printf.printf "\n";
							let v2 = !Db.Value.access_after (Kstmt stmt) lval in
							Db.Value.pretty Format.std_formatter v2;
							Printf.printf "\n";
							Printf.printf "++++set v1v2\n"*)
						| Call(lvalo,exp,expl,loc) ->(
							visitor#vexpr exp;
							match lvalo with
							| Some l ->
								let v1 = !Db.Value.access (Kstmt stmt) l in
								Printf.printf "----call v1\n";
								Db.Value.pretty Format.std_formatter v1;
								Printf.printf "\n";
								Printf.printf "++++call v1\n"
										
							| _ ->
								Printf.printf "lvalo\n"
						)
						| Code_annot(code_annotation,location) ->
							Printf.printf "Code_annot\n"
						| Skip(location) ->
							Printf.printf "Skip\n"
						| _ ->
							Printf.printf "Asm\n"(*end match instr*)
					)
				| Loop (code_annotation , subblock , location , stmt1 , stmt2) ->
					Printf.printf "print_block:loop\n";
					print_block subblock visitor;
					Printf.printf "\n"
				| Block (subblock) ->
					Printf.printf "print_block:block\n";
					print_block subblock visitor;
					Printf.printf "\n"
				| _ ->
					Printf.printf "not Instr\n");
		Printf.printf "++++++++stmt\n";
		)block.bstmts
	
let print_function_body (fundec:fundec) visitor= 
	(*Printf.printf "fundec.sspec\n";
	let kf = Globals.Functions.get fundec.svar in
	let t = Kernel_function.dummy () in
	let name= Kernel_function.get_name t in
	Printf.printf "name=%s\n" name;
	let code_annot = Kernel_function.code_annotations t in
	Printf.printf "length=%d\n" (List.length code_annot);
	!Db.Outputs.display_external Format.std_formatter kf;
	Cil.d_funspec Format.std_formatter (Kernel_function.get_spec t)*)
	print_block fundec.sbody visitor
	(*List.iter(fun var ->
		Printf.printf "%s\nattribute:" var.vname;
			List.iter(fun attr ->
			Cil.d_attr Format.std_formatter attr;
			Printf.printf "\n"
			)var.vattr;
		(
			match var.vtype with
				| TInt (ikind , attributes) ->
					Printf.printf "int var\n"
				| TArray (typ , exp , bitsSizeofTypCache , attributes) ->
					Printf.printf "array var\n"
				| _ -> 
					Printf.printf "other var\n"
		)
		)fundec.slocals*)
	
let visit_cilfile file = 
	let loop_visitor = new Visitor.frama_c_inplace in
	Printf.printf "%s\n" "before visit";
	Visitor.visitFramacFile loop_visitor file
	
let print_proj_info = 
	Printf.printf "Project.name:%s\n" Project.name(*
	Printf.printf "uname=%s\n" (Project.get_unique_name (Project.current()))*)

(**get loop information*)
let get_loop_infor fundec = 
	List.iter (fun stmt ->
		match stmt.skind with
			| Loop (code_annotation , block , location , stmt1 , stmt2) ->
				Printf.printf "%s\n" "loop info";
				(*Printf.printf "%s\n" "----code_annotation";
				List.iter(fun anno ->
					Cil.d_code_annotation Format.std_formatter anno;
					) code_annotation;
				Printf.printf "%s\n" "++++code_annotation";
				Printf.printf "%s\n" "----block";
				Cil.d_block Format.std_formatter block;
				Printf.printf "%s\n" "++++block";*)
				Printf.printf "%s\n" "----block var";
				List.iter( fun varinfo ->
					Printf.printf "%s\n" varinfo.vname;
					) block.blocals;
				Printf.printf "%s\n" "++++block var";
				Printf.printf "%s\n" "----stmt1 succs";
				p_stmt_succs stmt1;
				Printf.printf "%s\n" "++++stmt1 succs";
				Printf.printf "%s\n" "----stmt2 succs";
				p_stmt_succs stmt2;
				Printf.printf "%s\n" "++++stmt2 succs";
				
				Printf.printf "%s\n" "----stmt1 preds";
				p_stmt_preds stmt1;
				Printf.printf "%s\n" "++++stmt1 preds";
				Printf.printf "%s\n" "----stmt2 preds";
				p_stmt_preds stmt2;
				Printf.printf "%s\n" "++++stmt2 preds";
				(*let (p1,p2) = location in
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
			| _ -> Printf.printf "%s\n" "other info";
				(*Printf.printf "%s\n" "----code_annotation";
				List.iter(fun anno ->
					Cil.d_code_annotation Format.std_formatter anno;
					) code_annotation;
				Printf.printf "%s\n" "++++code_annotation";
				Printf.printf "%s\n" "----block";
				Cil.d_block Format.std_formatter block;
				Printf.printf "%s\n" "++++block";*)
				Printf.printf "%s\n" "----stmt succs";
				List.iter(fun succe ->
					Cil.d_stmt Format.std_formatter succe;
					)stmt.succs;
				Printf.printf "\n";
				Printf.printf "%s\n" "++++stmt succs";
				Printf.printf "%s\n" "----stmt preds";
				List.iter(fun preds ->
					Cil.d_stmt Format.std_formatter preds;
					)stmt.preds;
				Printf.printf "\n";
				Printf.printf "%s\n" "++++stmt preds";
				) fundec.sallstmts


class non_zero_divisor prj = object (self)
	inherit Visitor.generic_frama_c_visitor prj (Cil.copy_visit ())
	method vexpr (e:exp) = 
		Printf.printf "non_zero_divisor#vexpr\n";
		Cil.d_exp Format.std_formatter e;
		Printf.printf "\n";
		match e.enode with
		| BinOp((Div|Mod|Mult|PlusA|MinusA) ,_, e2 ,_) ->
			let t = Cil.typeOf e2 in
			let logic_e2 =
				Logic_const.term
					(TCastE(t,Logic_utils.expr_to_term ~cast:true e2 )) (Ctype t)
			in
			let assertion = Logic_const.prel (Rneq , logic_e2 , Cil.lzero()) in
		
			(match self#current_stmt with
			| Some stmt ->
				(*let stmt = Extlib.the self#current_stmt in*)
				Printf.printf "current_stmt:vexpr.stmt\n";
				Cil.d_predicate_named Format.std_formatter assertion;
				Queue.add
				(fun () ->		
					Annotations.add_assert stmt [Ast.self] ~before:true assertion
				);
					self#get_filling_actions;
				DoChildren
			| None ->
				Printf.printf "current_stmt:vexpr.none\n";
				SkipChildren
			)
		| UnOp((Neg) ,e1 ,_) ->
			Printf.printf "vexpr.unop\n";
			DoChildren
		| Const(con) ->
			Printf.printf "vexpr.const\n";
			DoChildren
		| Lval (lval) ->
			Printf.printf "vexpr.lval\n";
			DoChildren
		| _ -> DoChildren
end

(*let create_syntactic_check_project () =
	File.create_project_from_visitor " syntactic check " (new non_zero_divisor )
	
		
let visitor = new non_zero_divisor (Project.current ())*)