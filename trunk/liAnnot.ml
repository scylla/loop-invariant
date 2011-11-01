open Cil
open Cil_types
open Cil_datatype
open Annotations
open Kernel_function
open Db_types
open Prove

let remove_code_annot (stmt:Cil_types.stmt) (rannot_bf:Cil_types.code_annotation) =
	
	let sl = Some([Ast.self]) in
	let rannot_bf_list = Annotations.get_all_annotations ?who:sl stmt in
	Annotations.reset_stmt false stmt;
	List.iter(fun rannot->
		match rannot with
		| Before(User(annot)|AI(_,annot))|After(User(annot)|AI(_,annot))->
		if annot.annot_id=rannot_bf.annot_id then begin
			Printf.printf "invalid rannot_bf\n";end
		else begin
			(Printf.printf "id1=%d,id2=%d\n" annot.annot_id rannot_bf.annot_id;
			Annotations.add stmt [Ast.self] rannot;)end
	)rannot_bf_list;;
	
let prove_code_annot (kf:Db_types.kernel_function) (stmt:Cil_types.stmt) (code_annot:Cil_types.code_annotation) =
	let flag = ref 1 in
	Printf.printf "before prove the annot\n";Cil.d_code_annotation Format.std_formatter code_annot;Format.print_flush ();Printf.printf "\n";
	let ip_list = Property.ip_of_code_annot kf stmt code_annot in
	Printf.printf "ip_list.len=%d\n" (List.length ip_list);
	List.iter(fun ip->
		let result = prove_predicate kf None (Some(ip)) in
		Printf.printf "result.len=%d\n" (List.length result);
		
		if (List.length result)>0 then
		(
		List.iter(fun status->
			match status with
			| Unknown->(
				flag := 0;
				Printf.printf "result unknown\n";
			)
			| Checked(checked_status)->
				if checked_status.valid=True then
					(flag:=1;Printf.printf "result True\n";)					
				else if checked_status.valid=False then
					(flag := 0;
					Printf.printf "result False\n";)					
				else if checked_status.valid=Maybe then
					(flag := 0;
					Printf.printf "result Maybe\n";)					
				;
			Format.print_flush ();
		)result;
		)else(flag := 0;);
	)ip_list;
	Printf.printf "in prove_code_annot,flag=%d\n" !flag;
	if !flag=0 then
	(Printf.printf "remove invalid annot\n";remove_code_annot stmt code_annot;)else
	(Printf.printf "keep the annot\n";Cil.d_code_annotation Format.std_formatter code_annot;Format.print_flush ();Printf.printf "\n";)
	;;
	
	
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
