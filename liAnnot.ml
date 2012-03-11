open Cil_types

let compareLogicInfo (linfo1:Cil_types.logic_info) (linfo2:Cil_types.logic_info) : bool =
	let lv1 = linfo1.l_var_info in
	let lp1 = linfo1.l_profile in
	let lv2 = linfo2.l_var_info in
	let lp2 = linfo2.l_profile in
	if lv1.lv_name!=lv2.lv_name then
	(	
		false;
	)
	else
	(
		let len1 = List.length lp1 in
		let len2 = List.length lp2 in
		if len1!=len2 then
		(
			false;
		)
		else
		(
			let flag = ref 1 in
			for i=0 to (len1-1) do
			(
				let v1 = (List.nth lp1 i) in
				let v2 = (List.nth lp2 i) in
				if v1.lv_name!=v2.lv_name then
				(
					flag := 0;
				);
			)
			done;
			if !flag=1 then	(true;) else (false;);
		);
	);;
			
let rec compareCodeAnnot (code_annot1:Cil_types.code_annotation) (code_annot2:Cil_types.code_annotation) : bool =
	match code_annot1.annot_content , code_annot2.annot_content with
	| AInvariant(sl1,b1,p1),AInvariant(sl2,b2,p2)->
		(match p1.content,p2.content with
		| Papp(linfo1,_,tl1),Papp(linfo2,_,tl2)->
			if (compareLogicInfo linfo1 linfo2)=true then
			(
				let len1 = List.length tl1 in
				let len2 = List.length tl2 in
				if len1!=len2 then
				(
					false;
				)
				else
				(
					let flag = ref 1 in
					for i=0 to (len1-1) do
					(
						let t1 = (List.nth tl1 i) in
						let t2 = (List.nth tl2 i) in
						match t1.term_node,t2.term_node with
						| TConst(c1),TConst(c2)->
							Printf.printf "term_node:TConst\n";
						| TLval(l1),TLval(l2)->
							let (host1,offset1) = l1 in
							let (host2,offset2) = l2 in
							(
							match host1,host2 with
							| TVar(lv1),TVar(lv2)->
								if lv1.lv_id!=lv2.lv_id then (Printf.printf "lv1.lv_id!=lv2.lv_id\n";flag := 0;);
							| _,_->();
							);
							Printf.printf "term_node:TLval\n";
						| TUnOp(u1,_),TUnOp(u2,_)->
							Printf.printf "term_node:TUnOp\n";
						| TBinOp(b1,_,_),TBinOp(b2,_,_)->
							Printf.printf "term_node:TBinOp\n";
						| _,_->();
					)
					done;
					if !flag=1 then	(true;) else (false;);
				);
			)
			else (false;);
		| _->false;
		);
	| _->false;;
	
let isExistCodeAnnot (code_annot:Cil_types.code_annotation) (s:stmt) : bool =
	Printf.printf "isExistCodeAnnot\n";Cil.d_code_annotation Format.std_formatter code_annot;Format.print_flush ();Printf.printf "\n";
	let flag = ref 0 in
	let sl = Some([Ast.self]) in
	let rannot_bf_list = Annotations.get_all_annotations ?who:sl s in
	List.iter(fun rannot->
		match rannot with
		| User(a)|AI(_,a)->
			if (compareCodeAnnot code_annot a)=true then (flag := 1;)
	)rannot_bf_list;
	if !flag=1 then	(true;) else (false;);;
				
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
	
let prove_code_annot (kf:Cil_types.kernel_function) (stmt:Cil_types.stmt) (code_annot:Cil_types.code_annotation) (ipl:Property.identified_property list ref) wp_compute =
	let flag = ref 1 and fmt = Format.std_formatter in
	let ip = Property.ip_of_code_annot_single kf stmt code_annot in
	
	flag := Prove.prove_predicate kf [] ip wp_compute;ipl := ip::!ipl;
	Printf.printf "in prove_code_annot,flag=%d\n" !flag;
	if !flag=0 then
	(Printf.printf "remove invalid annot\n";Cil.d_code_annotation fmt code_annot;Format.print_flush ();Printf.printf "\n";remove_code_annot stmt kf code_annot;)
	else
	(Printf.printf "keep the annot\n";Cil.d_code_annotation fmt code_annot;Format.print_flush ();Printf.printf "\n";);
	!flag;;
	
	
let prove_kf (kf:Cil_types.kernel_function) = 
	Printf.printf "prove_kf\n";
	List.iter(fun bhv->
		Printf.printf "%s\n" bhv;
	)(Kernel_function.all_function_behaviors kf);
	
	
	let annot_list = Kernel_function.code_annotations kf in
	List.iter(fun (stmt,root_code_annot_ba) ->
	match root_code_annot_ba with
		| User(code_annot)|AI(_,code_annot) ->
			let ip_list = Property.ip_of_code_annot kf stmt code_annot in
			List.iter(fun ip->
				Prove.prove_predicate kf (Kernel_function.all_function_behaviors kf) ip;
				Format.print_flush ();
				(*let status = Property_status.get ip in
				(match status with
				| Never_tried->
					Printf.printf "result Never_tried\n";
				| Best(e_status,erl)->
					Printf.printf "result Best\n";
				| Inconsistent(inc)->
					Printf.printf "result InConsistent\n";
				);*)
			)ip_list;
	)annot_list;
	();;
