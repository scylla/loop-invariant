open LoopInvariant
open Project
open Cil_types
open Cil_datatype
open Cil
open Visitor
open Function_analysis
open Db
open Db_types
open Ast_printer
open Globals
open Db.LoopInvariant
open Logic_typing
open Kernel_function
open Annotations
open State_builder
open Extlib

(** Register the new plug-in "Loop Invariant" and provide access to some plug-in
    dedicated features. *)
module Self =
  Plugin.Register
    (struct
       let name = "loop invariant"
       let shortname = "loopInv"
       let help = "'Loop Invariant' plugin. Add some new ACSL annotations about loop structure to get better effect of Jessie."
     end)

(** Register the new Frama-C option "-loop-invariant". *)
module Enabled =
  Self.False
    (struct
       let option_name = "-loop-invariant"
       let help = "my loop invariant plugin. by Liu"
       let kind = `Correctness
     end)

class loopInvariant = object (self)

  inherit Visitor.generic_frama_c_visitor
    (Project.current ()) (inplace_visit ()) as super

  initializer !Db.Value.compute ()

	val mutable decls = []

  method private current_ki =
    match self#current_stmt with None -> Kglobal | Some s -> Kstmt s

  method vvdec vi =
    let ki = self#current_ki in
    if Db.Value.is_accessible ki then begin
      let z =
	!Db.Value.lval_to_zone
	  ki ~with_alarms:CilE.warn_none_mode (Var vi, NoOffset)
      in
      decls <-  (vi, z) :: decls
    end;
    DoChildren
    
    method vterm_lval tlv =
    (try
       let lv = !Db.Properties.Interp.term_lval_to_lval ~result:None tlv in
       ignore (self#vlval lv)
     with Invalid_argument msg ->
       error "%s@." msg);
    DoChildren

  method vstmt_aux s =
    !Db.progress ();
    super#vstmt_aux s
   
  method vcode_annot (c:code_annotation) = 
  	Cil.d_code_annotation Format.std_formatter c;
  	DoChildren
end

  
let rec loopInvariantAnalysis (cil: Cil_types.file) =
  begin	
      	Globals.Functions.iter (fun kf ->
      		Self.result "enter function %s.\n" (Kernel_function.get_name kf);
      		Printf.printf "the funspec is as follow:\n";
		  	let funspec = Kernel_function.get_spec kf in(*structure   (term, identified_predicate, identified_term) spec*)
		  	Cil.d_funspec Format.std_formatter funspec;
		  	Printf.printf "\n";
		  	
		  	Printf.printf "the precondition is as follow:\n";
		  	let pre = Kernel_function.precondition kf in
		  	Cil.d_predicate_named Format.std_formatter pre;
		  	Printf.printf "\n";
		  	
		  	Printf.printf "the postcondition is as follow:\n";
		  	let post = Kernel_function.postcondition kf Cil_types.Normal in
		  	Cil.d_predicate_named Format.std_formatter post;
		  	Printf.printf "\n";
		  	
		  	Printf.printf "the global annotations are as follow:\n";
		  	let gannot_list = Globals.Annotations.get_all () in
		  	List.iter(fun (g,b) ->
		  	Printf.printf "%b\n" b;
		  	Cil.d_annotation Format.std_formatter g;
		  	)gannot_list;
		  	Printf.printf "\n";
		  	
		  	Printf.printf "the code annotations are as follow:\n";
		  	(*let c_annot_list = Annotations.get_annotations () in(*only this works*)
		  	List.iter(fun (g_annot,(ba:bool)) ->(
		  	Cil.d_annotation Format.std_formatter g_annot;
		  	(*(match r_code_annot with
		  	| User(code_annotation) -> (
				Cil.d_code_annotation Format.std_formatter code_annotation;
		  	)
		  	| _ -> (
		  		Printf.printf "\n";
		  	)
		  	);*)
		  	))c_annot_list;
		  	Printf.printf "\n";*)
		  	
		  	let global = Kernel_function.get_global kf in
		  	match global with
		  	| GType(typeinfo,location) -> (
		  		Printf.printf "GType\n";
		  	)
		  	| GCompTag(compinfo,location) -> (
		  		Printf.printf "GCompTag\n";
		  	)
		  	| GCompTagDecl(compinfo,location) -> (
		  		Printf.printf "GCompTagDecl\n";
		  	)
		  	| GEnumTag(enuminfo,location) -> (
		  		Printf.printf "GEnumTag\n";
		  	)
		  	| GEnumTagDecl(enuminfo,location) -> (
		  		Printf.printf "GEnumTagDecl\n";
		  	)
		  	| GVarDecl(funspec,varinfo,location) -> (
		  		Cil.d_funspec Format.std_formatter funspec;
		  	)
		  	| GVar(varinfo,initinfo,location) -> (
		  		Printf.printf "GVar\n";
		  	)
		  	| GFun(fundec,location) -> (
		  		List.iter( fun stmt ->
		  		Cil.d_stmt Format.std_formatter stmt;
		  		Printf.printf "\n";
		  		let annot =  Annotations.get_annotations stmt <> [] in
		  		let c_annot = !Db.Properties.Interp.code_annot kf stmt ~before:true "abc" in
		  		Cil.d_code_annotation Format.std_formatter c_annot;
		  		(*let v = new loopInvariant in
		  		v#vcode_annot;
		  		let annot = Annotations.get_annotations in
		  		let state = Cil.selfMachine in
			  	(*Printf.printf "%s" (State.get_name state);
				let state = Cil.selfFormalsDecl in
				Printf.printf "%s" (State.get_name state);*)
				let annotList = Annotations.get_all () in
				List.iter(fun (annot,ba) ->
					Cil.d_annotation Format.std_formatter annot;
					(*match annot with
					| User(code_anno) -> (
					Cil.d_code_annotation Format.std_formatter code_anno;
					)
					| _ -> (
					Printf.printf "\n";
					)*)
				)annotList;*)
					Printf.printf "\n";
		  		)fundec.sallstmts;
		  	)
		  	| GAsm(s,location) -> (
		  		Printf.printf "s\n";
		  	)
		  	| GPragma(attribute,location) -> (
		  		Printf.printf "GPragma\n";
		  	)
		  	| GText(s) -> (
		  		Printf.printf "GText\n";
		  	)
		  	| GAnnot(global_annotation,location) -> (
		  	)
		  	| _ -> (
		  		Printf.printf "\n";
		  	);
		  	
		  	(*Cil.d_global Format.std_formatter global;		  	
		  	let first_stmt = Kernel_function.find_first_stmt kf in
		  	let first_block = Kernel_function.find_enclosing_block first_stmt in
		  	
		  	let rec print_stmt (sl:stmt list) =
		  	if (List.length sl)>0
		  	then
		  	List.iter (fun (s_succs:stmt) ->
		  	Cil.d_stmt Format.std_formatter s_succs;
		  	print_stmt s_succs.succs;
		  	
		  	let state = Cil.selfMachine in
		  	(*Printf.printf "%s" (State.get_name state);
			let state = Cil.selfFormalsDecl in
			Printf.printf "%s" (State.get_name state);*)
			let annotList = Annotations.get_all () in
			List.iter(fun (annot,ba) ->
			Cil.d_annotation Format.std_formatter annot;
			(*match annot with
			| User(code_anno) -> (
			Cil.d_code_annotation Format.std_formatter code_anno;
			)
			| _ -> (
			Printf.printf "\n";
			)*)
			)annotList;
		  	
		  	Printf.printf "\n";
			
		  	) sl;
		  	in
		  	Cil.d_stmt Format.std_formatter first_stmt;
		  	print_stmt first_stmt.succs;*)
		  	Printf.printf "\n";
		  	
		  	Self.result "leave function %s.\n" (Kernel_function.get_name kf);
      	);
      	
      	
      	
		!Db.Properties.Interp.from_range_to_comprehension  (Cil.inplace_visit ()) (Project.current ()) cil;
		
      	let logic_info_list = Logic_env.find_all_logic_functions cil.fileName in
      	Printf.printf "logic_info_list.length=%d\n" (List.length logic_info_list);(*0?*)
      	List.iter (fun (node:logic_info) ->
      		Cil.d_logic_var Format.std_formatter node.l_var_info;
      	) logic_info_list;
      	
    
      	(*let logic_var = Logic_typing.Make.find_var cil.fileName in
      	Cil.d_logic_var Format.std_formatter logic_var;
      	let logic_type_info = Logic_env.find_logic_type cil.fileName in
      	Printf.printf "logic_type_info.name=%s\n" logic_type_info.lt_name;*)
      	
      	
		(*create_syntactic_check_project ();*)
		let visitor = new non_zero_divisor (Project.current ()) in
		
		Printf.printf "Ast.is_computed=%b\n" (Ast.is_computed ());
		Printf.printf "anno.length=%d\n" (List.length (Globals.Annotations.get_all ()));
		List.iter(fun (annot,gene) ->
			Cil.d_annotation Format.std_formatter annot;
		)(Globals.Annotations.get_all ()); 
		
		Printf.printf "length=cil.globals=%d\n" (List.length cil.globals);
		
		(*let fundec = Cil.getGlobInit cil in*)
		(*Printf.printf "length=fundec.sallstmts=%d\n" (List.length fundec.sallstmts);
		
		Cfg.clearCFGinfo  fundec;*)
		(**before compute, must clear first. set clear_id to be false*)
		Cfg.clearFileCFG ~clear_id:false cil;
		Cfg.computeFileCFG cil;
		
		(*Cfg.prepareCFG fundec;
		Cfg.computeCFGInfo fundec true;*)
		(**
		Printf.printf "before cil.globals fundec.name=%s\n" fundec.svar.vname;
		Printf.printf "cil.globinitcalled=%b\n" cil.globinitcalled;
		Printf.printf "length=fundec.sallstmts=%d\n" (List.length fundec.sallstmts);
		Printf.printf "fundec.smaxid=%d\n" fundec.smaxid;*)
		
		
		Printf.printf "%s\n" "----cil.globals";
		
					(**let get_loc_str location=
						let loc=Cil.d_loc Format.std_formatter location in
						Pretty.sprint 80 doc;
					in*)
		
		(*!Db.Value.compute ();
		let visitor = new File.check_file cil.fileName in*)
		Printf.printf "%b\n" (Ast.is_computed ());
		let globs = Globals.Annotations.get_all () in
		Printf.printf "globs.length=";
		List.length globs;
		Printf.printf "\n";
		Globals.Annotations.iter (fun (anno:global_annotation) (isGene:bool) ->
			Printf.printf "anno\n";
			(*Cil.d_global Format.std_formatter anno;*)
		) ;
		
		List.iter (function g ->
			match g with
				|	(GText text) ->	
					Printf.printf "location.file=%s\n" text;
				| (GVarDecl (funspec,varinfo,location)) -> 
					(*Printf.printf "GVarDecl:location.file=%s\n" (get_loc_str location);*)
					Cil.d_var Format.err_formatter varinfo;
					Cil.d_loc Format.str_formatter location;
					Printf.printf "GVarDecl:varinfo.vname=%s\n" varinfo.vname;
					(*Cil.printType plainCilPrinter () varinfo.vtype;
					Format.print_string "\n";*)
				| (GType (typeinfo,location)) -> 
					Printf.printf "GType:typeinfo.tname=%s\n" typeinfo.tname;
					(*Printf.printf "GType:location.file=%s\n" (get_loc_str location);*)
				| (GCompTag (compinfo,location)) -> 
					Printf.printf "GCompTag:compinfo.cname=%s\n" compinfo.cname;
					(*Printf.printf "GCompTag:location.file=%s\n" (get_loc_str location);*)
				| (GCompTagDecl (compinfo,location)) -> 
					Printf.printf "GCompTagDecl:compinfo.cname=%s\n" compinfo.cname;
					(*Printf.printf "GCompTagDecl:location.file=%s\n" (get_loc_str location);*)
				| (GEnumTag (enuminfo,location)) -> 
					Printf.printf "GEnumTagDecl:enuminfo.ename=%s\n" enuminfo.ename;
					(*Printf.printf "GEnumTag:location.file=%s\n" (get_loc_str location);*)
				| (GEnumTagDecl (enuminfo,location)) -> 
					Printf.printf "GEnumTagDecl:enuminfo.ename=%s\n" enuminfo.ename;
					(*Printf.printf "GEnumTagDecl:location.file=%s\n" (get_loc_str location);*)
				| (GVarDecl (funspec,varinfo,location)) -> 
					Printf.printf "GVarDecl:varinfo.vname=%s\n" varinfo.vname; 
					(*Printf.printf "GVarDecl:location.file=%s\n" (get_loc_str location);*)
				| (GVar (varinfo,initinfo,location)) -> 
					Printf.printf "GVar:varinfo.vname=%s\n" varinfo.vname;
					(*Printf.printf "GVar:location.file=%s\n" (get_loc_str location);*)
					Printf.printf "Gvar:varinfo.vname=%s\n" varinfo.vname;
				| (GFun (fundec,location)) -> 
					Printf.printf "%s\n" "GFun:";
					(*Printf.printf "%s" "loc:";
					Cil.d_loc Format.std_formatter location;
					Printf.printf "%s" "**\n";
					(*Printf.printf "\tlocation.file=%s\n" (get_loc_str location);*)
					Printf.printf "fundec.name=%s\n" fundec.svar.vname;
					
					Printf.printf "%s\n" "----fundec.slocals";
					List.iter (fun varinfo ->
						Printf.printf "%s\n" varinfo.vname;
						) fundec.slocals;
					Printf.printf "%s\n" "++++fundec.slocals";
					Printf.printf "%s\n" "----fundec.sformals";
					List.iter (fun ele ->
						Printf.printf "%s\n" ele.vname;
						) fundec.sformals;
					Printf.printf "%s\n" "++++fundec.sformals";*)
					
					Cfg.clearCFGinfo ~clear_id:false fundec;
					Cfg.cfgFun fundec;
					(*Function_analysis.get_loop_infor fundec;*)
					Function_analysis.count_loop_number fundec;
					(*Function_analysis.p_visitor visitor;
					Function_analysis.print_function_stmts fundec visitor;*)
					
					Function_analysis.print_function_body fundec visitor;
					(*let num = Cfg.cfgFun fundec in
					Printf.printf "\tCfg.cfgFun:num=%d\n" num;*)
					
					(*let dotName = "/home/lzh/"^fundec.svar.vname^".dot" in
					Cfg.printCfgFilename dotName fundec;
					let cmdstr = "dot /home/lzh/"^fundec.svar.vname^".dot -Tpng -o /home/lzh/"^fundec.svar.vname^".png" in
					Sys.command cmdstr;*)
					
					Printf.printf "%s\n" "";
						
					(*Format.print_string "\n";
				| (GAsm (asm,location)) -> 
					Printf.printf "GAsm:location.file=%s\n" location.file;
				| (GPragma (attribute,location)) -> 
					Printf.printf "GPragma:location.file=%s\n" location.file;*)
				| GAnnot(global_annotation , location) ->
					Cil.d_global Format.std_formatter g;
					Printf.printf "%s\n" "GAnnot:";
				| _ -> Printf.printf "%s\n" "I donnot konw.";
			) cil.globals;
			
			(*let mainname = ref "main" in
			let theFile : global list ref = ref [] in
			List.iter 
        begin
          fun g ->
            (match g with
              GFun(m, lm) when m.svar.vname = !mainname ->
                (* Prepend a prototype *)
                theFile := GVarDecl (gi.svar, lm) :: !theFile;
                m.sbody.bstmts <- 
                   compactStmts (mkStmt (Instr [Call(None, 
                                                     Lval(var gi.svar), 
                                                     [], locUnknown)]) 
                                 :: m.sbody.bstmts);
                file.globinitcalled <- true;
                if !E.verboseFlag then
                  ignore (E.log "Inserted the globinit\n")
            | _ -> ());
            theFile := g :: !theFile (* Now put the global back *)
        end
        cil.globals;*)
		Printf.printf "numbers of loops in the program=%n\n" !Function_analysis.loop_number;
		Printf.printf "%s\n" "++++cil.globals";
		
		(**get CallGraph and print*)
		let graph = Callgraph.computeGraph cil in
		Callgraph.printGraph Pervasives.stdout graph;
		
		
		(**Slicing*)
		(*let slicPro = !Db.Slicing.Project.mk_project "test_slice" in*)
		(*let slicPro = !Db.Slicing.Slice.create (Project.current ())  kfun in
		let kfuncion = !Db.Slicing.Slice.get_function (Project.current ()) in
		match kfuncion.fundec with
					| Definition (fundec , location) ->
						Printf.printf "%s\n" "Definition";
						Printf.printf "%s\n" fundec.svar.vname;
						Cil.d_loc Format.std_formatter location;
						Printf.printf "\n";
					| Declaration (funspec , varinfo , varinfolo , location) ->
						Printf.printf "%s\n" "Declaration";
						Cil.d_funspec Format.std_formatter funspec;
						Printf.printf "%s\n" varinfo.vname;
						Cil.d_loc Format.std_formatter location;
						Printf.printf "\n";
					| _ -> Printf.printf "%s\n" "i donnot konw";*)
						
		(**global kernel_function*)
		(*List.iter(fun s ->
			Printf.printf "----%s\n" s;
			List.iter(fun kfun ->
				match kfun.fundec with
					| Definition (fundec , location) ->
						Printf.printf "%s\n" "Definition";
						Printf.printf "%s\n" fundec.svar.vname;
						Cil.d_loc Format.std_formatter location;
						Printf.printf "\n";
					| Declaration (funspec , varinfo , varinfolo , location) ->
						Printf.printf "%s\n" "Declaration";
						Cil.d_funspec Format.std_formatter funspec;
						Printf.printf "%s\n" varinfo.vname;
						Cil.d_loc Format.std_formatter location;
						Printf.printf "\n";
					| _ -> Printf.printf "%s\n" "i donnot konw";
						
				) (Globals.FileIndex.get_functions s);
			Printf.printf "++++%s\n" s;
			) (Globals.FileIndex.get_files ());*)
		
		(**value compute*)
		(*let state= Db.Value.globals_state () in
		Printf.printf "Db.Value.is_reachable=%b\n" (Db.Value.is_reachable state);
		let visitor = new File.check_file cil.fileName in
		Db.Value.access visitor#current_kinstr lval;
		Printf.printf "%s\n" "begin visitFramacFile";
		Visitor.visitFramacFile visitor cil;
		Visitor.visitFramacFunction visitor fundec;
		Printf.printf "%s\n" "end visitFramacFile";*)
		
		let out_file = open_out "/home/lzh/result.c" in
		Cil.dumpFile Cil.defaultCilPrinter out_file "/home/lzh/new.c" cil;
		flush out_file;
		close_out out_file;
		(*Function_analysis.visit_cilfile cil;
		let mem_functions = Loop_parameters.MemFunctions.get () in
	  if Loop_parameters.MemExecAll.get ()
	    || not (Datatype.String.Set.is_empty mem_functions)
	  then begin
	    Loop_parameters.feedback "====== MEMOIZING FUNCTIONS ======";
	    Ast.compute ();
		end;*)
		(*Ast.compute ();
		Db.Inputs.expr ();
		Ast.compute ();
		(*Printf.printf "%s\n" "----CFG";		
		List.iter (fun ele ->
			let num = Cfg.cfgFun fundec in
			d_cfgnodename () ele;
			) fundec.sallstmts;
		Printf.printf "%s\n" "++++CFG";*)*)

  end
  
let theMain () = 
	
	Ast.get ();
	
	Self.result "Begin to execute Value Analysis.\n"; 
	Printf.printf "Db.Value.is_computed=%b\n" (Db.Value.is_computed ());
	if not (Db.Value.is_computed ()) then !Db.Value.compute ();
	Self.result "Value Analysis Over.\n";
	Self.result "Begin to execute LoopInvariant Analysis.\n"; 
	loopInvariantAnalysis (Ast.get ());
	Self.result "LoopInvariant Analysis Over.\n"
    
let compute_loop_invariant () = 
	Ast.compute ();
	ignore (visitFramacFile (new loopInvariant) (Ast.get ()));
	theMain ()
	
	
let run () =  if Enabled.get () then compute_loop_invariant ()

let () = Db.Main.extend run
