open Cil
open Cil_types
open Cil_datatype
open Annotations
open Kernel_function
open Db_types
open Prove

let remove_code_annot (stmt:Cil_types.stmt) (rannot_bf:Cil_types.code_annotation) =
	Annotations.reset_stmt false stmt;
	
	let sl = Some([Ast.self]) in
	let rannot_bf_list = Annotations.get_all_annotations ?who:sl stmt in
	List.iter(fun rannot->
		match rannot with
		| Before(User(annot)|AI(_,annot))|After(User(annot)|AI(_,annot))->
		if annot.annot_id=rannot_bf.annot_id then begin
			Printf.printf "invalid rannot_bf\n";end
		else begin
			Annotations.add stmt [Ast.self] rannot;end
	)rannot_bf_list;;
	
let prove_code_annot (kf:Db_types.kernel_function) (stmt:Cil_types.stmt) (code_annot:Cil_types.code_annotation) =
	let ip_list = Property.ip_of_code_annot kf stmt code_annot in
	List.iter(fun ip->
		prove_predicate kf None (Some(ip));(*(Some(Kernel_function.all_function_behaviors kf))*)
		let result = Properties_status.get_all ip in
		List.iter(fun status->
			match status with
			| Unknown->(
				Printf.printf "unknown\n";
			)
			| Checked(checked_status)->
				if checked_status.valid=True then
					(Printf.printf "true\n";)					
				else if checked_status.valid=False then
					(remove_code_annot stmt code_annot;
					Printf.printf "False\n";)					
				else if checked_status.valid=Maybe then
					(Printf.printf "Maybe\n";)					
				;
			Format.print_flush ();
		)result;
	)ip_list;;
	
	
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
				let result = Properties_status.get_all ip in
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
	();;
