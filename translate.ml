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
open Li_utils
	
let rec force_assert_to_annot (e:Cil_types.exp) (kf:Cil_types.kernel_function) (s:Cil_types.stmt) = 
	match e.enode with
	| BinOp(op,e1,e2,_)->
		Cil.d_binop Format.std_formatter op;Format.print_flush ();Printf.printf "\n";
		force_assert_to_annot e1 kf s;
		force_assert_to_annot e2 kf s
	| _->
		let code_annot = !Db.Properties.Interp.force_exp_to_assertion e in
        let assert_root_code_annot_ba = Cil_types.User(code_annot) in
        Annotations.add kf s [Ast.self] assert_root_code_annot_ba
           			
let translate_kf (kf:Cil_types.kernel_function) =
	try
	let fundec = Kernel_function.get_definition kf in
	List.iter( fun stmt ->
		(match stmt.skind with
		| Instr(instr) ->
		  	(match instr with
		  	| Call(lo,e,el,l)->
           		List.iter(fun e1->
           			let code_annot = !Db.Properties.Interp.force_exp_to_assertion e1 in
        			let assert_root_code_annot_ba = Cil_types.User(code_annot) in
        			Annotations.add kf stmt [Ast.self] assert_root_code_annot_ba;
           		)el;
           	| _->();
           	);
        | _->();
        );
	)fundec.sallstmts(*List.iter end*)
	with No_Definition->Printf.printf "The given function [%s] is not a definition.\n" (Kernel_function.get_name kf)
