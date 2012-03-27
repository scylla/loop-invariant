open Cil_types
open Cil_datatype
open Cil
open File
open LiVisitor
open Translate

(** Register the new plug-in "Loop Invariant" and provide access to some plug-in
    dedicated features. *)
module Self =
  Plugin.Register
    (struct
       let name = "loop invariant"
       let shortname = "loopInv"
       let help = "Loop Invariant plugin. Add some new ACSL annotations about loop structure to get better effect of Jessie."
     end)

(** Register the new Frama-C option "-loop-invariant". *)
module Enabled =
  Self.False
    (struct
       let option_name = "-loop-invariant"
       let help = "my loop invariant plugin. by Henry Liu"
       let kind = `Correctness
     end)

class loopInvariant = object (self)

  inherit Visitor.generic_frama_c_visitor
    (Project.current ()) (Cil.inplace_visit ()) as super

  initializer !Db.Value.compute ();

	val mutable decls = [];

  method private current_ki =
    match self#current_stmt with None -> Cil_types.Kglobal; | Some s -> Cil_types.Kstmt s;

  method vvdec vi =
    let ki = self#current_ki in
    if Db.Value.is_accessible ki then begin
      let z =
	!Db.Value.lval_to_zone
	  ki ~with_alarms:CilE.warn_none_mode (Cil_types.Var vi, Cil_types.NoOffset)
      in
      decls <-  (vi, z) :: decls;
    end;
    Cil.DoChildren
    

  method vstmt_aux s =
    !Db.progress ();
    super#vstmt_aux s;
   
  method vcode_annot (c:code_annotation) = 
  	Cil.d_code_annotation Format.std_formatter c;
  	DoChildren
end
	
	 
let loopInvariantAnalysis (cil: Cil_types.file) =
	let fmt = Format.std_formatter in
	let unknownout = open_out_gen [Open_wronly;Open_append;Open_creat;Open_trunc] 766 "/home/lzh/unknown.c" in
	
	let manpk = Polka.manager_alloc_strict() in
	let manbox = Box.manager_alloc() in
	(*Template.ex1 manpk;*)
	let linfo_list = ref [] in(*logic_info list*)
	let gannot_list = Globals.Annotations.get_all () in
	List.iter(fun (g,_) ->
		match g with
		| Dfun_or_pred(logic_info,_)->
			(match logic_info.l_body with
			| LBpred(_)->
					linfo_list := logic_info::!linfo_list;
			| _->
					();
			);
			Format.print_flush ();
		| _->
			Format.print_flush ();
	)gannot_list;
  
	(*before compute, must clear first. set clear_id to be false*)
  Cfg.clearFileCFG ~clear_id:false cil;
	Cfg.computeFileCFG cil;
	
	(*get array vars in every function*)
	let arrayvars = Hashtbl.create 2 in
	Globals.Functions.iter(fun kf ->
		let name = Kernel_function.get_name kf in
		match kf.fundec with
		| Definition(dec,_)->
			Cfg.printCfgFilename ("/home/lzh/"^name^".dot") dec;
			let get_array_vars =
				let vars = ref [] in
				(*get from function specification*)
				let funspec = Kernel_function.get_spec kf in
				List.iter(fun b->
					List.iter(fun ip->
						begin match ip.ip_content with
						| Pvalid_range(t1,_,t3)->
							begin match t1.term_node with
							| TLval((thost,_))->
								begin match thost with
								| TMem(_)->();
								| TVar(lv)->
									begin match lv.lv_origin with
									| Some(v1)->
										let v = {LiType.v=v1;typ=v1.vtype;size=LiType.CTerm(t3);} in
										vars := v::!vars;
									| None->();
									end;
								| TResult(_)->();
								end;
							| _->();
							end;
						| _->();
						end;
					)b.b_requires;
				)funspec.spec_behavior;
				(*get from vars directly*)
				List.iter(fun v->
					begin match v.vtype with
					| TArray(tp,_,size,_)->
						let v = {LiType.v=v;typ=tp;size=LiType.CSize(size);} in
						vars := v::!vars;
					| _->();
					end;
				)(dec.slocals@dec.sformals);
				(*get from stmts indirectly, sometimes maybe wrong*)
				let rec analysis_exp fmt e =
					begin match e.enode with
					| Lval((host,offset))->
						begin match (host,offset) with
						| (Mem(e1),NoOffset)->
							begin match e1.enode with
							| BinOp(_,e2,_,_)->
								let vl = Varinfo.Set.elements (LiUtils.extract_varinfos_from_exp e2) in
								List.iter(fun v1->
									if (List.for_all (fun v2->(String.compare v1.vname v2.LiType.v.vname)!=0) !vars)==true then
									begin
										let v = {LiType.v=v1;typ=v1.vtype;size=LiType.CSize({scache = Not_Computed});} in
										vars := v::!vars;
									end;
								)vl;
							| _->();
							end;
						| _->();
						end;
					| BinOp(_,e1,e2,_)->
						analysis_exp fmt e1;analysis_exp fmt e2;
					| UnOp(_,e,_)->
						analysis_exp fmt e;
					| CastE(_,e)->
						analysis_exp fmt e;
					| _->();
					end
				in
				let rec analysis_stmt s =
					begin match s.skind with
					| Instr(ins)->
						begin match ins with
						| Set(_,e,_)->
							analysis_exp fmt e;
						| _->();
						end;
					| Loop(_,_,_,_,_)->
						let loop = extract_loop s in
						analysis_exp fmt loop.Equation.con;
						List.iter(fun s1->
							analysis_stmt s1;
						)loop.Equation.body;
					| Block(b)->
						List.iter(fun s1->
							analysis_stmt s1;
						)b.bstmts;
					| UnspecifiedSequence(seq)->
						let b = Cil.block_from_unspecified_sequence seq in
						List.iter(fun s1->
							analysis_stmt s1;
						)b.bstmts;
					| If(exp,b1,b2,_)->
						analysis_exp fmt exp;
						List.iter(fun s1->
							analysis_stmt s1;
						)b1.bstmts;
						List.iter(fun s1->
							analysis_stmt s1;
						)b2.bstmts;
					| _->();
					end;
				in
				
				List.iter(fun s->
					analysis_stmt s;
				)dec.sbody.bstmts;
				(*get from spec*)
				!vars
			in
			
			Hashtbl.add arrayvars (Kernel_function.get_id kf) get_array_vars;(*fundec-->arrayvars*)
		| Declaration(_,_,_,_)->
		  ();
	);
	
	(*assign bid to [block] in program*)
	let maxid = ref 0 in
	Globals.Functions.iter(fun kf ->
		match kf.fundec with
		| Definition(dec,_)->
			Translate.get_block_maxid maxid dec.sbody;
		| Declaration(_,_,_,_)->
		  ();
	);
	Translate.preprocess_bpoint maxid;
	
	
	(*instance of wp plugin*)
	let ipl = ref [] in
	let module OLS = Datatype.List(Datatype.String) in(*Datatype.Option*)
	let module OKF = Datatype.Option(Kernel_function) in
	let module OP = Datatype.Option(Property) in
	Dynamic.Parameter.Int.set "-wp-timeout" 10;
	Dynamic.Parameter.Int.set "-wp-par" 6;
	Dynamic.Parameter.String.set "-wp-out" "/home/lzh/why-out";
	let wp_compute = Dynamic.get ~plugin:"Wp" "wp_compute" (Datatype.func3 OKF.ty OLS.ty OP.ty Datatype.unit) in
	
	
	let funsigs =
		let funsig = Hashtbl.create 2 in
		Globals.Functions.iter(fun kf ->
			let name = Kernel_function.get_name kf in
			match kf.fundec with
			| Definition(dec,_)->
			  Hashtbl.add funsig name {Loop_parameters.spec=dec.sspec;Loop_parameters.formals=Some dec.sformals;}
		  | Declaration(spec,_,vlo,_)->
		    Hashtbl.add funsig name {Loop_parameters.spec=spec;Loop_parameters.formals=vlo;}
		);
		funsig;
	in
	
	let visitor = new liVisitor (Project.current ()) in
	
  Globals.Functions.iter(fun kf ->
  	let fname = Kernel_function.get_name kf in
    if fname="assert" then
    (
      Self.result "This is an Assert clause.\n";
    )else
    (
      Self.result "Enter function [%s].\n" fname;
		  begin match kf.fundec with
		  | Definition(_,_)->
	    	Function_analysis.analysis_kf kf !linfo_list funsigs visitor ipl wp_compute unknownout;
      | Declaration(_,_,_,_)->
      	();
      end;
      Self.result "Leave function [%s].\n" fname;
    );
  );
  
  
	let info = C2equation.make_info cil in
	let (fgraph,bgraph) = Frontend.build_graphs fmt info arrayvars ipl wp_compute unknownout in
	(*Printf.printf "Frontend.compute_and_display begin\n";
	Frontend.compute_and_display fmt info fgraph bgraph manbox;
	Printf.printf "Frontend.compute_and_display over\n";*)
	
	
  let logic_info_list = Logic_env.find_all_logic_functions cil.fileName in
  Printf.printf "logic_info_list.length=%d\n" (List.length logic_info_list);(*0?*)
  List.iter (fun (node:logic_info) ->
    Cil.d_logic_var Format.std_formatter node.l_var_info;
  )logic_info_list;
      	
    
   (*let logic_var = Logic_typing.Make.find_var cil.fileName in
     Cil.d_logic_var Format.std_formatter logic_var;
     let logic_type_info = Logic_env.find_logic_type cil.fileName in
     Printf.printf "logic_type_info.name=%s\n" logic_type_info.lt_name;*)
      	
      	
		
		(*let fundec = Cil.getGlobInit cil in*)
		(*Printf.printf "length=fundec.sallstmts=%d\n" (List.length fundec.sallstmts);
		
		Cfg.clearCFGinfo  fundec;*)
		
		(*Cfg.prepareCFG fundec;
		Cfg.computeCFGInfo fundec true;*)
		(*
		Printf.printf "before cil.globals fundec.name=%s\n" fundec.svar.vname;
		Printf.printf "cil.globinitcalled=%b\n" cil.globinitcalled;
		Printf.printf "length=fundec.sallstmts=%d\n" (List.length fundec.sallstmts);
		Printf.printf "fundec.smaxid=%d\n" fundec.smaxid;*)
		
	(*get CallGraph and print*)
	let graph = Callgraph.computeGraph cil in
	Callgraph.printGraph Pervasives.stdout graph;
	
	
	let fpath = "/home/lzh/tmp.c" in
	LiUtils.save fpath cil;
	Project.clear_all ();
	
	LiAnnot.load fpath;
	let cil = Ast.get () in
	Ast.set_file cil;
	
	Globals.Functions.iter(fun kf->
		begin match kf.fundec with
		| Definition(_,_)->
			LiAnnot.prove_fundec kf wp_compute unknownout;
		| Declaration _->();
		end;
  );
  
  let fpath = "/home/lzh/result.c" in
  LiUtils.save fpath cil;
	close_out unknownout
  
let theMain () =	
	Ast.get ();	
	Self.result "Begin to execute Value Analysis.\n"; 
	(*Printf.printf "Db.Value.is_computed=%b\n" (Db.Value.is_computed ());
	if not (Db.Value.is_computed ()) then !Db.Value.compute ();
	Self.result "Value Analysis Over.\n";*)
	Self.result "Begin to execute LoopInvariant Analysis.\n"; 
	loopInvariantAnalysis (Ast.get ());
	Self.result "LoopInvariant Analysis Over.\n"
    
let compute_loop_invariant () = 
	Ast.compute ();
	(*Unroll_loops.compute 1 (Ast.get ());don't unroll loops now or locations in fixpoint is wrong. maybe need to modify those codes*)
  Globals.Functions.iter (fun kf ->
   (match kf.fundec with
   	| Definition(dec,_)->
      Cfg.clearCFGinfo ~clear_id:true dec;
      Cfg.prepareCFG dec;
			Cfg.computeCFGInfo dec true;
		| _->();
	);
  );
	ignore (Visitor.visitFramacFile (new loopInvariant) (Ast.get ()));
	theMain ()
	
	
let run () =  if Enabled.get () then compute_loop_invariant ()

let () = Db.Main.extend run
