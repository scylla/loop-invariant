open Cil
open Visitor
open Project
open Cil_types
open Cil_datatype
open Project
open Annotations
open LiAnnot

let is_type_consistent (linfo:logic_info) (vars:varinfo list) =
	let flag = ref 1 in
	let len = List.length linfo.l_profile in
	for i=0 to len-1 do
		let a = List.nth vars i in
		let f = List.nth linfo.l_profile i in
		(
		match f.lv_type with
		| Ctype(fc)->
			if a.vtype=fc then
			()
			else
			(flag := 0;)
		|_->();
		);
	done;
	!flag;;
	
let rec get_all_combine (kf:Cil_types.kernel_function) (linfo:logic_info) (s:stmt) (vars:varinfo list) (result:varinfo list) (len:int) (tlen:int)=
	if len>=tlen then
	(
		if (is_type_consistent linfo vars)=1 then 
		(
			let tl = ref [] in
			List.iter(fun v->
				tl := (LiUtils.mk_term_from_vi v)::!tl;
			)result;
			List.rev !tl;
			Printf.printf "tl.len=%d\n" (List.length !tl);
			Printf.printf "lables.len=%d\n" (List.length linfo.l_labels);
			if (List.length linfo.l_labels)>0 then
			(
				let len = List.length linfo.l_labels in
				let oldlabels = ref [] in
				let labels1 = ref [] in
				let labels2 = ref [] in
				for i=0 to (len-1) do
				(
					oldlabels := List.append !oldlabels [List.nth linfo.l_labels i];
					labels1 := List.append !labels1 [LogicLabel(None,"Here"),LogicLabel(None,"Here")];
					labels2 := List.append !labels2 [LogicLabel(None,"Here")];
				);
				done;
				List.iter(fun label->
				match label with
				| LogicLabel(_,s)->
					Printf.printf "before sbu;label:%s" s;
				| _->();
				)linfo.l_labels;
				Printf.printf "\n";
				linfo.l_labels <- !labels2;
				List.iter(fun label->
				match label with
				| LogicLabel(_,s)->
					Printf.printf "after sub;label:%s" s;
				| _->();
				)linfo.l_labels;
				Printf.printf "\n";
				let newpn = Logic_const.unamed (Papp(linfo,
				!labels1,!tl)) in
			
				let annot = Logic_const.new_code_annotation(AInvariant([],true,newpn)) in
				let root_code_annot_ba = Cil_types.User(annot) in
				if (isExistCodeAnnot annot s)=false then
				(
				Annotations.add kf s [Ast.self] root_code_annot_ba;
				Printf.printf "just new annot\n";Cil.d_code_annotation Format.std_formatter annot;Format.print_flush ();Printf.printf "\n";
				Printf.printf "logic_var,len>0:\n";Cil.d_logic_var Format.std_formatter linfo.l_var_info;Format.print_flush ();Printf.printf "\n";
				Cil.d_predicate_named Format.std_formatter newpn;Format.print_flush ();Printf.printf "\n";
				prove_code_annot kf s annot;
				Printf.printf "after annot\n";Cil.d_code_annotation Format.std_formatter annot;Format.print_flush ();Printf.printf "\n";
				);
				(*linfo.l_labels <- !oldlabels;*)
				List.iter(fun label->
				match label with
				| LogicLabel(_,s)->
					Printf.printf "sub back;label:%s" s;
				| _->();
				)linfo.l_labels;
				Printf.printf "\n";
			)else
			(
				let newpn = Logic_const.unamed (Papp(linfo,	[],!tl)) in			
				let annot = Logic_const.new_code_annotation(AInvariant([],true,newpn)) in
				let root_code_annot_ba = Cil_types.User(annot) in
				if (isExistCodeAnnot annot s)=false then 
				(
				Annotations.add kf s [Ast.self] root_code_annot_ba;
				Printf.printf "just new annot\n";Cil.d_code_annotation Format.std_formatter annot;Format.print_flush ();Printf.printf "\n";
				
				prove_code_annot kf s annot;
				Printf.printf "after annot\n";Cil.d_code_annotation Format.std_formatter annot;Format.print_flush ();Printf.printf"\n";
				);
			)
		)else
		(
			Printf.printf "type inconsistent\n";
			(*List.iter(fun v->
				Cil.d_var Format.std_formatter v;Format.print_flush ();Printf.printf "\n";
			)vars;*)
		)
	)else
	(
		for i=len to (List.length vars)-1 do
			let li = List.nth vars i in
			let new_result = li::result in
			let nvars = (LiUtils.swap vars i len) in
			get_all_combine kf linfo s nvars new_result (len+1) tlen;
		done;
	)

class liVisitor prj = object (self)
	(*inherit Visitor.frama_c_visitor*)
	inherit Visitor.generic_frama_c_visitor prj (Cil.copy_visit ())
	
	method make_lvar_from_cvar (var:varinfo) = 
		let ltype = Ctype(var.vtype) in
		let logic_var = Cil.make_temp_logic_var ltype in
		logic_var.lv_name <- var.vorig_name;
		Cil.d_logic_var Format.std_formatter logic_var;
		Format.print_flush ();
		logic_var;
			
	method add_pn (kf:Cil_types.kernel_function) (linfo:logic_info) (s:stmt) (vars:varinfo list)= 
		match linfo.l_body with
		| LBpred(pn)->(
			let flen = (List.length linfo.l_profile) in
			let alen = List.length vars in
			if alen>=flen then
			(
				get_all_combine kf linfo s vars [] 0 flen;
				();
			);
		);
		| _->
      		Printf.printf "other\n";
      	;
		
	method vstmt (s:stmt) = 
		Cil.d_stmt Format.std_formatter s;
		Format.print_flush ();
		DoChildren
		
	method vlogic_info_use (linfo:logic_info) = 
		
		match linfo.l_body with
		| LBpred(pn)->(
			(*let stmt = Extlib.the (self#current_stmt) in
			Cil.d_stmt Format.std_formatter stmt;
			Format.print_flush ();
			Annotations.add_assert stmt [Ast.self] ~before:true pn;*)
			(match self#current_stmt with
			| Some(s)->
				(*let func = self#current_func in
				Annotations.add_assert s [Ast.self] ~before:true pn;*)();
			| None->();
			);
			SkipChildren
		)
		|_->(
			Printf.printf "no pred\n";
			Format.print_flush ();
			SkipChildren
		)
		
	method vexpr (e:exp) = 
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
					(*Annotations.add_assert stmt [Ast.self] ~before:true assertion*)();
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
