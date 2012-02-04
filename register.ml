open Cil_types
open Cil
open LiVisitor
open Translate
open Function_analysis

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
       let help = "my loop invariant plugin. by Liu"
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
	
	let maxid = ref 0 in
	Globals.Functions.iter(fun kf ->
		match kf.fundec with
		| Definition(dec,loc)->
			get_block_maxid maxid dec.sbody;
		| Declaration(spec,v,vlo,_)->
		  ()
	);
	
	Translate.preprocess_bpoint maxid;
	
	let (fgraph,bgraph) = Frontend.build_graphs Format.std_formatter cil in
	Printf.printf "Frontend.compute_and_display begin\n";
	Frontend.compute_and_display Format.std_formatter cil fgraph bgraph manpk;
	Printf.printf "Frontend.compute_and_display over\n";
	
	
	let funsigs =
		let funsig = Hashtbl.create 2 in
		Globals.Functions.iter(fun kf ->
			let name = Kernel_function.get_name kf in
			match kf.fundec with
			| Definition(dec,_)->
			  Hashtbl.add funsig name {Loop_parameters.spec=dec.sspec;Loop_parameters.formals=Some dec.sformals;}
		  | Declaration(spec,v,vlo,_)->
		    Hashtbl.add funsig name {Loop_parameters.spec=spec;Loop_parameters.formals=vlo;}
		);
		funsig;
	in
	
	let visitor = new liVisitor (Project.current ()) in
	Globals.Functions.iter(fun kf ->		
		match kf.fundec with
		| Definition(_,_)->
	    Translate.translate_kf kf;
      (*prove_kf kf;*)
    | Declaration(spec,v,vlo,_)->
      ();
	);
  
  Globals.Functions.iter(fun kf ->
  	let fname = Kernel_function.get_name kf in
    if fname="assert" then
    (
      Self.result "This is an Assert clause.\n";
      analysis_assert kf;
    )else
    (
      Self.result "Enter function [%s].\n" fname;
      Printf.printf "the funspec is as follow:\n";
		  let funspec = Kernel_function.get_spec kf in(*structure   (term, identified_predicate, identified_term) spec*)
		  	
		  let assumes = ref [] in
		  List.iter(fun b->
		  	Printf.printf "b_name begin:%s\n" b.b_name;
		  	Printf.printf "assumes\n";
		  	let al = ref [] in
		  	List.iter(fun ip->
		  		al := (Logic_const.unamed ip.ip_content)::!al;
		  		Cil.d_identified_predicate Format.std_formatter ip;Format.print_flush ();Printf.printf "\n";
		  	)b.b_assumes;
		  	assumes := (Logic_const.pands !al)::!assumes;
		  	Printf.printf "requires\n";
		  	List.iter(fun ip->
		  		Cil.d_identified_predicate Format.std_formatter ip;Format.print_flush ();Printf.printf "\n";
		  	)b.b_requires;
		  	Printf.printf "post_cond\n";
		  	List.iter(fun (_,ip)->
		  		Cil.d_identified_predicate Format.std_formatter ip;Format.print_flush ();Printf.printf "\n";
		  	)b.b_post_cond;
		  	Printf.printf "b_name end\n";
		  )funspec.spec_behavior;
		  Printf.printf "assumes named\n";
		  List.iter(fun pn->
		  	Cil.d_predicate_named Format.std_formatter pn;Format.print_flush ();Printf.printf "\n";
		  )!assumes;
		  match kf.fundec with
		  | Definition(_,_)->
	    	analysis_kf kf manpk !linfo_list !assumes funsigs visitor;
      		(*prove_kf kf;*)
      | Declaration(spec,v,vlo,_)->
      	();
    );
  );
      	
	!Db.Properties.Interp.from_range_to_comprehension  (Cil.inplace_visit ()) (Project.current ()) cil;
		
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
		
		
	Printf.printf "%s\n" "----cil.globals";
		(*!Db.Value.compute ();
		let visitor = new File.check_file cil.fileName in*)
		
		
		(**get CallGraph and print*)
	let graph = Callgraph.computeGraph cil in
	Callgraph.printGraph Pervasives.stdout graph;
		
		
		(**Slicing*)
		(*let slicPro = !Db.Slicing.Project.mk_project "test_slice" in*)
		(*let slicPro = !Db.Slicing.Slice.create (Project.current ())  kfun in
		let kfuncion = !Db.Slicing.Slice.get_function (Project.current ()) in*)
						
		(**global kernel_function*)
		(*List.iter(fun s ->
			Printf.printf "----%s\n" s;
			List.iter(fun kfun ->
						
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
	close_out out_file
  
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
	(*Unroll_loops.compute 1 (Ast.get ());*)(*don't unroll loops now or locations in fixpoint is wrong. maybe need to modify those codes*)
  Globals.Functions.iter (fun kf ->
   (match kf.fundec with
   	| Definition(dec,_)->
      Cfg.clearCFGinfo ~clear_id:true dec;
      Cfg.prepareCFG dec;
			Cfg.computeCFGInfo dec true;
		| _->();
	);
  );
  let fpath = "/home/lzh/preprocess.c" in
  let out_file = open_out fpath in
  Cil.dumpFile Cil.defaultCilPrinter out_file "/home/lzh/new.c" (Ast.get ());
	flush out_file;
	close_out out_file;
	let newfile = File.from_filename fpath in
	ignore (Visitor.visitFramacFile (new loopInvariant) (Ast.get ()));
	theMain ()
	
	
let run () =  if Enabled.get () then compute_loop_invariant ()

let () = Db.Main.extend run
