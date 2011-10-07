open Cil
open Visitor
open Project
open Cil_types
open Cil_datatype
open Project
open Db_types

class liVisitor prj = object (self)
	inherit Visitor.generic_frama_c_visitor prj (Cil.copy_visit ())
	method vlogic_info_use (linfo:logic_info) = 
		
		match linfo.l_body with
		| LBpred(pn)->(
			Cil.d_predicate_named Format.std_formatter pn;
			Printf.printf "LBpred\n";
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
