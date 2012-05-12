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
       let help = "Loop Invariant plugin. Add some new ACSL annotations about loop structure to get better effect of Jessie and wp."
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
	let strfmt = Format.str_formatter in
	let project = Project.current () in
	
	let unknownout = open_out_gen [Open_wronly;Open_append;Open_creat;Open_trunc] 766 "/home/lzh/unknown.c" in
	let annots = ref [] in(*all annotation strings generated by loopInv*)
	
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
		| _->();
	)gannot_list;
  
	(*before compute, must clear first. set clear_id to be false*)
  Cfg.clearFileCFG ~clear_id:false cil;
	Cfg.computeFileCFG cil;
	
	(*get array vars in every function*)
	let arrayvars = Hashtbl.create 2 in
	let globalarray = ref [] in
	Globals.Vars.iter(fun v init->
		begin match v.vtype with
		| TArray(tp,_,size,_)->
			if (List.for_all(fun v1->(String.compare v.vname v1.LiType.vname)!=0) !globalarray)==true then
			begin
				let v = {LiType.v=Some v;LiType.vname=v.vname;typ=Ctype(tp);size=LiType.CSize(size);} in
				globalarray := v::!globalarray;
			end;
		| _->();
		end;
	);
	
	let sl_project = !Db.Slicing.Project.mk_project "Slicing" in
	Globals.Functions.iter(fun kf ->
		let name = Kernel_function.get_name kf in
		match kf.fundec with
		| Definition(dec,_)->
			let slice = !Db.Slicing.Slice.get_all sl_project kf in
			Printf.printf "Slice result\n";
			List.iter(fun t->
				!Db.Slicing.Slice.pretty fmt t;
			);
			Cfg.printCfgFilename ("/home/lzh/"^name^".dot") dec;			
			Hashtbl.add arrayvars (Kernel_function.get_id kf) (Translate.get_array_vars kf dec fmt);(*fundec-->arrayvars*)
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
	(*assign bid to block*)
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
	
	(*sigs of functions*)
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
		  | Definition(fundec,_)->
		  	begin match fundec.svar.vstorage with
		  	| Static->();
		  	| _->
	    		Function_analysis.analysis_kf kf !linfo_list funsigs annots visitor ipl wp_compute unknownout;
	    	end;
      | Declaration(_,_,_,_)->();
      end;
      Self.result "Leave function [%s].\n" fname;
    );
  );
  
  
	let info = C2equation.make_info cil in
	let (fgraph,bgraph) = Frontend.build_graphs fmt info !globalarray arrayvars ipl wp_compute annots unknownout in
	Printf.printf "Frontend.compute_and_display begin\n";
	Frontend.compute_and_display fmt info fgraph bgraph manpk annots;
	(*Printf.printf "Frontend.compute_and_display over\n";*)
	
	
  let logic_info_list = Logic_env.find_all_logic_functions cil.fileName in
  List.iter (fun (node:logic_info) ->
    Cil.d_logic_var Format.std_formatter node.l_var_info;
  )logic_info_list;
		
	(*get CallGraph and print*)
	let graph = Callgraph.computeGraph cil in
	Callgraph.printGraph Pervasives.stdout graph;
	
	
	let fpath = "/home/lzh/tmp2.c" in
	LiUtils.save fpath cil;
	Project.clear_all ();
	
	LiAnnot.load fpath;
	let cil = Ast.get () in
	Ast.set_file cil;
	
	let total = ref 0 and right = ref 0 in
	Globals.Functions.iter(fun kf->
		begin match kf.fundec with
		| Definition(_,_)->
			let (t,r) = LiAnnot.prove_fundec kf wp_compute unknownout in
			total := !total+t;
			right := !right+r;
		| Declaration _->();
		end;
  );
	Printf.printf "total=%d,right=%d\n" !total !right;
  
  let fpath = "/home/lzh/result2.c" in
  LiUtils.save fpath cil;
	close_out unknownout
  
let theMain () =	
	Ast.get ();	
	Self.result "Begin to execute Value Analysis.\n"; 
	Self.result "Begin to execute LoopInvariant Analysis.\n"; 
	loopInvariantAnalysis (Ast.get ());
	Self.result "LoopInvariant Analysis Over.\n"
    
let compute_loop_invariant () = 
	Ast.compute ();
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
