open LoopInvariant
open Project
open Cil_types
open Cil
open Cil_datatype
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
      	(*Globals.Functions.iter (fun kf ->
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
		  	let annot_list = Kernel_function.code_annotations kf in(*(stmt*rooted_code_annotation before_after) list*)
		  	List.iter(fun (stmt,root_code_annot_ba) ->
		  		(*Cil.d_stmt Format.std_formatter stmt;*)(*only stmts which own annotations*)
		  		(
		  		match root_code_annot_ba with
		  		| Before(annot) ->(
		  			(
		  			match annot with
		  			| User(code_annot) ->(
		  				Printf.printf "User before\n";
		  				Cil.d_code_annotation Format.std_formatter code_annot;
		  				Format.print_flush ();
		  				Printf.printf "\n";
		  			)
		  			| AI(alarmt,code_annot) ->(
		  				Printf.printf "AI before\n";
		  				Alarms.pretty Format.std_formatter alarmt;
		  				Printf.printf "\n";
		  				Cil.d_code_annotation Format.std_formatter code_annot;
		  				Format.print_flush ();
		  				Printf.printf "\n";
		  			)
		  			);
		  		)
		  		| After(annot) ->(
		  			(
		  			match annot with
		  			| User(code_annot) ->(
		  				Printf.printf "User after\n";
		  				Cil.d_code_annotation Format.std_formatter code_annot;
		  				Format.print_flush ();
		  				Printf.printf "\n";
		  			)
		  			| AI(alarmt,code_annot) ->(
		  				Printf.printf "AI after\n";
		  				Alarms.pretty Format.std_formatter alarmt;
		  				Printf.printf "\n";
		  				Cil.d_code_annotation Format.std_formatter code_annot;
		  				Format.print_flush ();
		  				Printf.printf "\n";
		  			)
		  			);
		  		)
		  		);
		  	)annot_list;
		  	
		  	let global = Kernel_function.get_global kf in
		  	Function_analysis.print_kf_global global;
		  			  	
		  	Printf.printf "\n";
		  	
		  	Self.result "leave function %s.\n" (Kernel_function.get_name kf);
      	);*)
      	
      	List.iter(fun g ->(
      	Function_analysis.print_kf_global g;
      	)
      	)cil.globals;
      	
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
		List.iter(fun (g_annot,gene) ->
		(*Cil.d_annotation Format.std_formatter g_annot;*)
		match g_annot with
		| Dlemma(s,b,logic_label_l,s_list,p_named,location)->(		
			Printf.printf "Dlemma---\n";
			Cil.d_annotation Format.std_formatter g_annot;
			Printf.printf "string1=%s\n" s;
			List.iter(fun label->
			match label with
			| LogicLabel(stmto,s1)->(
				Printf.printf "logic_label=%s\n" s1;
			)
			| StmtLabel(stmtr)->(
				Printf.printf "StmtLabel=";
				Cil.d_stmt Format.std_formatter !stmtr;
				Format.print_flush ();
				Printf.printf "\n";()
			);(*match label End*)
			)logic_label_l;
			List.iter(fun s1->
			Printf.printf "s_list=%s\n" s1;
			)s_list;
			
			Cil.d_predicate_named Format.std_formatter p_named;(*empty?*)
			Format.print_flush ();
			Printf.printf "\n";
			
			Printf.printf "Dlemma+++\n";
		)
		| _->(
		);(*match g_annot End*)
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
