open Cil
open Visitor
open Project
open Cil_types
open Cil_datatype
open Project
open Db_types
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
	
let rec get_all_combine (kf:Db_types.kernel_function) (linfo:logic_info) (s:stmt) (vars:varinfo list) (result:varinfo list) (len:int) (tlen:int)=
	if len>=tlen then
	(
		if (is_type_consistent linfo vars)=1 then 
		(
			let tl = ref [] in
			List.iter(fun v->
				tl := (Li_utils.mk_term_from_vi v)::!tl;
			)result;
			List.rev !tl;
		
			let newpn = Logic_const.unamed (Papp(linfo,
				[],!tl)) in
			
			let annot = Logic_const.new_code_annotation(AInvariant([],true,newpn)) in
			let root_code_annot_ba = Db_types.Before(Db_types.User(annot)) in
			Annotations.add s [Ast.self] root_code_annot_ba;
			prove_code_annot kf s annot;
		)
	)else
	(
		for i=len to (List.length vars)-1 do
			let li = List.nth vars i in
			let new_result = li::result in
			let nvars = (Li_utils.swap vars i len) in
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
			
	method add_pn (kf:Db_types.kernel_function) (linfo:logic_info) (s:stmt) (vars:varinfo list)= 
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
				Cil.d_stmt Format.std_formatter s;
				Format.print_flush ();
				Annotations.add_assert s [Ast.self] ~before:true pn;
			| None->(););
			Cil.d_predicate_named Format.std_formatter pn;
			Format.print_flush ();
			(match pn.content with
      		| Psubtype(t1,t2)->
      			Printf.printf "Psubtype\n";
      		| Pfresh(t)->
      			Printf.printf "Pfresh\n";
      		| Pvalid_range(t1,t2,t3)->
      			Printf.printf "Pvalid_range\n";
      		| Pvalid_index(t1,t2)->
      			Printf.printf "Pvalid_index\n";
      		| Pvalid(t)->
      			Printf.printf "Pvalid\n";
      		| Pat(pn1,label)->
      			Printf.printf "Pat\n";
      		| Pold(pn1)->
      			Printf.printf "Pold\n";
      		| Pexists(q,pn1)->
      			Printf.printf "Pexists\n";
      		| Pforall(q,pn1)->
      			Printf.printf "Pforall\n";
      		| Plet(linfo,pn1)->
      			Printf.printf "Plet\n";
      		| Pfalse->
      			Printf.printf "Pfalse\n";
      		| Ptrue->
      			Printf.printf "Ptrue\n";
      		| Papp(linfo,l1,l2)->
      			Printf.printf "Papp\n";
      		| Pseparated(tl)->
      			Printf.printf "Pseparated\n";
      		| Prel(re,t1,t2)->
      			Printf.printf "Prel\n";
      		| Pand(pn1,pn2)->
      			Printf.printf "Pand\n";
      		| Por(pn1,pn2)->
      			Printf.printf "Por\n";
      		| Pxor(pn1,pn2)->
      			Printf.printf "Pxor\n";
      		| Pimplies(pn1,pn2)->
      			Printf.printf "Pimplies\n";
      		| Piff(pn1,pn2)->
      			Printf.printf "Piff\n";
      		| Pnot(pn1)->
      			Printf.printf "Pnot\n";
      		| Pif(t,pn1,pn2)->
      			Printf.printf "Pif\n";
      		| _->
      			Printf.printf "other\n";
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
