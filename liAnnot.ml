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
	| AInvariant(_,_,p1),AInvariant(_,_,p2)->
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
						| TConst(_),TConst(_)->
							Printf.printf "term_node:TConst\n";
						| TLval(l1),TLval(l2)->
							let (host1,_) = l1 in
							let (host2,_) = l2 in
							(
							match host1,host2 with
							| TVar(lv1),TVar(lv2)->
								if lv1.lv_id!=lv2.lv_id then (Printf.printf "lv1.lv_id!=lv2.lv_id\n";flag := 0;);
							| _,_->();
							);
							Printf.printf "term_node:TLval\n";
						| TUnOp(_,_),TUnOp(_,_)->
							Printf.printf "term_node:TUnOp\n";
						| TBinOp(_,_,_),TBinOp(_,_,_)->
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
			if annot.annot_id==rannot_bf.annot_id then begin
			();end
			else begin
			(Annotations.add kf stmt [Ast.self] rannot;)end
	)rannot_bf_list;;
	
let prove_code_annot (kf:Cil_types.kernel_function) (stmt:Cil_types.stmt) (code_annot:Cil_types.code_annotation)  wp_compute =
	let flag = ref 1 and fmt = Format.std_formatter in
	let ip = Property.ip_of_code_annot_single kf stmt code_annot in
	
	Prove.prove_predicate kf [] ip wp_compute;;
	

let load fpath =
	let file = File.from_filename fpath in
	Printf.printf "fpath:%s\n" (File.get_name file);
	File.init_from_c_files [file];
	file;;
	
let prove_fundec kf wp_compute unknownout=
	let fundec = Kernel_function.get_definition kf in
	let strfmt = Format.str_formatter in
	let count = ref 1 and total = ref 0 and right = ref 0 in
	
	let rec prove s =
		begin match s.skind with
		| Loop(_,b,_,_,_)->
			let roots = Annotations.get_all_annotations s in
			let res = ref [] in
			
			let len = List.length roots in
			total := !total+len;
			count := 1;
			List.iter(fun root->
				Printf.printf "roots.len=%d,current=%d\n" len !count;
				begin match root with
				| User(code)->
					let flag = prove_code_annot kf s code wp_compute in
					res := (flag,root)::!res;
					if flag==1 then
					begin Cil.d_code_annotation Format.std_formatter code;Format.print_flush ();Printf.printf "\n";end;
				| AI(_,_)->();
				end;
				count := !count+1;
			)roots;
			
			Annotations.reset_stmt false kf s;
			List.iter(fun (flag,root)->
				if flag==1 then
				begin Annotations.add kf s [Ast.self] root;right := !right+1;end
				else if flag==2 then
				begin
					begin match root with
					| User(code)|AI(_,code)->
						Cil.d_code_annotation strfmt code;
						output_string unknownout (Format.flush_str_formatter ());
						output_string unknownout "\n====>>\n";
						Cil.d_stmt strfmt s;
						output_string unknownout (Format.flush_str_formatter ());	
						output_string unknownout "\n\n\n";
						flush unknownout;
					end;
				end;
			)!res;
			List.iter(fun s1->
				prove s1;
			)b.bstmts;
		| If(_,b1,b2,_)|TryFinally(b1,b2,_)|TryExcept(b1,_,b2,_)->
			List.iter(fun s1->
				prove s1;
			)b1.bstmts;
			List.iter(fun s1->
				prove s1;
			)b2.bstmts;
		| Switch(_,b,_,_)|Block(b)->
			List.iter(fun s1->
				prove s1;
			)b.bstmts;
		| UnspecifiedSequence(seq)->
			let b = Cil.block_from_unspecified_sequence seq in
			List.iter(fun s1->
				prove s1;
			)b.bstmts;
		| _->();
		end;
	in
	
	List.iter(fun s->
		prove s
	)fundec.sbody.bstmts;
	Printf.printf "total=%d,right=%d\n" !total !right;;
