open Cil
open Cil_types
open Cil_datatype
open Annotations
open Kernel_function
open Prove
open Property_status

let remove_code_annot (stmt:Cil_types.stmt) (kf:Cil_types.kernel_function) (rannot_bf:Cil_types.code_annotation) =
	
	let sl = Some([Ast.self]) in
	let rannot_bf_list = Annotations.get_all_annotations ?who:sl stmt in
	Annotations.reset_stmt false kf stmt;
	List.iter(fun rannot->
		match rannot with
		| User(annot)|AI(_,annot)->
		if annot.annot_id=rannot_bf.annot_id then begin
			Printf.printf "invalid rannot_bf\n";end
		else begin
			(Annotations.add kf stmt [Ast.self] rannot;)end
	)rannot_bf_list;;
	
let prove_code_annot (kf:Cil_types.kernel_function) (stmt:Cil_types.stmt) (code_annot:Cil_types.code_annotation) =
	let flag = ref 1 in
	let ip_list = Property.ip_of_code_annot kf stmt code_annot in
	Printf.printf "ip_list.len=%d\n" (List.length ip_list);
	List.iter(fun ip->
		let status = prove_predicate kf [] ip in
		
		(match status with
		| Never_tried->
			flag :=0;Printf.printf "result Never_tried\n";
		| Best(e_status,erl)->
			Printf.printf "result Best\n";
			(match e_status with
			| True->
				Printf.printf "result True\n";
			| False_if_reachable->
				flag := 0;
				Printf.printf "result False_if_reachable\n";
			| False_and_reachable->
				flag := 0;
				Printf.printf "result False_and_reachable\n";
			| Dont_know->
				flag := 0;
				Printf.printf "result Dont_know\n";
			);
		| Inconsistent(inc)->
			flag := 0;
			Printf.printf "result InConsistent\n";
		);
	)ip_list;
	Printf.printf "in prove_code_annot,flag=%d\n" !flag;
	if !flag=0 then
	(Printf.printf "remove invalid annot\n";remove_code_annot stmt kf code_annot;)else
	(Printf.printf "keep the annot\n";Cil.d_code_annotation Format.std_formatter code_annot;Format.print_flush ();Printf.printf "\n";)
	;;
	
	
let prove_kf (kf:Cil_types.kernel_function) = 
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
		| User(code_annot)|AI(_,code_annot) ->
			let ip_list = Property.ip_of_code_annot kf stmt code_annot in
			List.iter(fun ip->
				Prove.prove_predicate kf (Kernel_function.all_function_behaviors kf) ip;
				Format.print_flush ();
				let status = Property_status.get ip in
				(match status with
				| Never_tried->
					Printf.printf "result Never_tried\n";
				| Best(e_status,erl)->
					Printf.printf "result Best\n";
				| Inconsistent(inc)->
					Printf.printf "result InConsistent\n";
				);
			)ip_list;
	)annot_list;
	();;
