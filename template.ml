
open Cil_types

let print_array = Apron.Abstract0.print_array;;

let print_apron_scalar fmt scalar =
  let res = Apron.Scalar.is_infty scalar in
  if res<>0 then
    Format.pp_print_string fmt
      (if res<0 then "-oo" else "+oo")
  else begin
    match scalar with
    | Apron.Scalar.Float _ | Apron.Scalar.Mpfrf _ ->
			Apron.Scalar.print fmt scalar
    | Apron.Scalar.Mpqf mpqf ->
			Apron.Scalar.print fmt (Apron.Scalar.Float (Mpqf.to_float mpqf))
  end;;

let print_apron_interval fmt itv =
  Format.fprintf fmt "[@[<hv>%a;@,%a@]]"
    print_apron_scalar itv.Apron.Interval.inf
    print_apron_scalar itv.Apron.Interval.sup;;

let print_apron_box fmt box =
  let tinterval = box.Apron.Abstract1.interval_array in
  let env = box.Apron.Abstract1.box1_env in
  let first = ref true in
  Format.fprintf fmt "[|@[";
  Array.iteri(fun i interval ->
  	if not (Apron.Interval.is_top interval) then begin
			if not !first then Format.fprintf fmt ";@ ";
			let var = Apron.Environment.var_of_dim env i in
			let name = Apron.Var.to_string var in
			Format.fprintf fmt "%s in %a" name
				print_apron_interval interval;
			first := false
    end;
  )tinterval;
  Format.fprintf fmt "@]|]";;

let print_abstract1 fmt abs =
  if !Loop_parameters.print_box then
      let man = Apron.Abstract1.manager abs in
      let box = Apron.Abstract1.to_box man abs in
      print_apron_box fmt box;
  else
    Apron.Abstract1.print fmt abs;;

(** Build a fixpoint manager (for module [Fixpoint]) given:
  - an equation graph (forward or backward)
  - optionally, the result of a previous, dual analysis
  - a function [apply graph output manager hyperedge tabstract]
  - a function [abstract_init]
  - an APRON manager;
  - a debug level
*)
let make_fpmanager
    ~(fmt : Format.formatter)
    (graph: Equation.graph)
    ~(output : (Equation.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.output option)
    (apply :
      Equation.graph ->
      output:(Equation.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.output option ->
      'a Apron.Manager.t -> int -> 'a Apron.Abstract1.t array ->
      unit * 'a Apron.Abstract1.t)
    (abstract_init : Equation.point -> 'a Apron.Abstract1.t)
    (man:'abstract Apron.Manager.t)
    ~(debug:int)
    :
    (Equation.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.manager
    =
  Printf.printf "make_fpmanager\n";
  let info = PSHGraph.info graph in
  {
    (* Lattice operation *)
    Fixpoint.bottom = begin fun vtx ->
      Apron.Abstract1.bottom man (Hashhe.find info.Equation.pointenv vtx)
    end;
    Fixpoint.canonical = begin fun vtx abs -> ()
      (* Apron.Abstract1.canonicalize man abs *)
    end;
    Fixpoint.is_bottom = begin fun vtx abs ->
      Apron.Abstract1.is_bottom man abs
    end;
    Fixpoint.is_leq = begin fun vtx abs1 abs2 ->
      Apron.Abstract1.is_leq man abs1 abs2
    end;
    Fixpoint.join = begin fun vtx abs1 abs2 ->
      Apron.Abstract1.join man abs1 abs2
    end;
    Fixpoint.join_list = begin fun vtx labs ->
      Apron.Abstract1.join_array man (Array.of_list labs)
    end;
    Fixpoint.widening = begin fun vtx abs1 abs2 ->
      Apron.Abstract1.widening man abs1 abs2
    end;
    (* Initialisation of equations *)
    Fixpoint.abstract_init = abstract_init;
    Fixpoint.arc_init = begin fun hedge -> () end;
    (* Interpreting hyperedges *)
    Fixpoint.apply = begin fun hedge tx ->
      apply graph ~output man hedge tx
    end;
    (* Printing functions *)
    Fixpoint.print_vertex=Equation.print_point;
    Fixpoint.print_hedge=Format.pp_print_int;
    Fixpoint.print_abstract = Apron.Abstract1.print;
    Fixpoint.print_arc = begin fun fmt () -> Format.pp_print_string fmt "()" end;
    (* Fixpoint Options *)
    Fixpoint.accumulate = false;
    (* Widening Options *)
    Fixpoint.widening_start = 1;(*!Option.widening_start;*)
    Fixpoint.widening_descend = 1;(*!Option.widening_descend;*)
    (* Printing Options *)
    Fixpoint.print_fmt = fmt;
    Fixpoint.print_analysis=debug>=1;
    Fixpoint.print_component=debug>=2;
    Fixpoint.print_step=debug>=3;
    Fixpoint.print_state=debug>=4;
    Fixpoint.print_postpre=debug>=5;
    Fixpoint.print_workingsets=debug>=6;
    (* DOT Options *)
    Fixpoint.dot_fmt = None;(*!Option.dot_fmt;*)
    Fixpoint.dot_vertex=Equation.print_point;
    Fixpoint.dot_hedge=Format.pp_print_int;
    Fixpoint.dot_attrvertex=Equation.print_point;
    Fixpoint.dot_attrhedge= 
    	begin fun fmt hedge ->
      	let transfer = PSHGraph.attrhedge graph hedge in
      	Format.fprintf fmt "%i: %a"
				hedge
				Equation.print_transfer transfer
    	end;
  }
  
(** Make an output graph filled with bottom abstract avlues *)
let make_emptyoutput
  (graph : (Equation.point,int,'a,'b,'c) PSHGraph.t)
  (manager : 'abstract Apron.Manager.t)
  :
  (Equation.point, int, 'abstract Apron.Abstract1.t,unit) Fixpoint.output
  =
  let info = PSHGraph.info graph in
  PSHGraph.map graph
    (begin fun vertex attr ->
      Apron.Abstract1.bottom manager (Hashhe.find info.Equation.pointenv vertex)
    end)
    (begin fun hedge arc -> () end)
    (begin fun info ->
      {
				Fixpoint.time = 0.0;
				Fixpoint.iterations = 0;
				Fixpoint.descendings = 0;
				Fixpoint.stable = false;
      }
    end)
    
let environment_of_tvar
  (typ_of_var : Apron.Var.t -> Apron.Environment.typvar)
  (tvar : Apron.Var.t array)
  :
  Apron.Environment.t
  =
  let (lint,lreal) =
    Array.fold_right
      (begin fun var (lint,lreal) ->
	begin match typ_of_var var with
	| Apron.Environment.INT -> (var::lint,lreal)
	| Apron.Environment.REAL -> (lint,var::lreal)
	end
      end)
      tvar
      ([],[])
  in
  let tint = Array.of_list lint and treal = Array.of_list lreal in
  Apron.Environment.make tint treal;;
  
(*  ********************************************************************** *)
(** {2 Forward semantics} *)
(*  ********************************************************************** *)

module Forward = struct

  (*  ===================================================================== *)
  (** {3 Transfer function} *)
  (*  ===================================================================== *)

  let apply_tassign (manager:'a Apron.Manager.t) (abstract:'a Apron.Abstract1.t) (var: Apron.Var.t) (expr:Apron.Texpr1.t) (dest:'a Apron.Abstract1.t option)
    =
    let res =
    	Apron.Abstract1.assign_texpr
				manager abstract
				var expr dest
    in
(*
    printf "apply_tassign %a := %a (%a) = %a@."
      Apron.Var.print var Apron.Texpr1.print expr
      Apron.Abstract1.print abstract
      Apron.Abstract1.print res
    ;
*)
    res;;

  let apply_condition (manager:'a Apron.Manager.t) (abstract:'a Apron.Abstract1.t) (expr:Apron.Tcons1.earray Boolexpr.t) (dest:'a Apron.Abstract1.t option) :'a Apron.Abstract1.t =
    let labstract =
      match expr with
      | Boolexpr.TRUE ->
	  		[abstract]
      | Boolexpr.DISJ lconj ->
	  		List.map(fun conj ->
	      Apron.Abstract1.meet_tcons_array manager abstract conj
	      )lconj
    in
    let labstract =
      match dest with
      | None -> labstract
      | Some dest ->
	 		 List.map(fun abstract -> 
	 		 Apron.Abstract1.meet manager abstract dest)labstract
    in
    let res = 
    	match labstract with
		  | [] ->
				Apron.Abstract1.bottom manager (Apron.Abstract1.env abstract)
		  | [x] -> x
		  | _ -> Apron.Abstract1.join_array manager (Array.of_list labstract)
    in
    if false then
      Format.printf "apply_condition %a %a => %a@."
				Apron.Abstract1.print abstract
				(Boolexpr.print (Apron.Tcons1.array_print ~first:"@[" ~sep:" &&@ " ~last:"@]")) expr
				Apron.Abstract1.print res;
    res;;

  let apply_call
    (manager:'a Apron.Manager.t)
    (abstract:'a Apron.Abstract1.t)
    (calleeinfo:Equation.procinfo)
    (inargs:Apron.Var.t array)
    (dest:'a Apron.Abstract1.t option)
    =
    (* current environment *)
    let env = Apron.Abstract1.env abstract in
    (* 1. We begin by removing all non-argument variables from the current
     abstract value *)
    let tenv = environment_of_tvar (Apron.Environment.typ_of_var env) inargs in
    let abstract2 =
      Apron.Abstract1.change_environment manager abstract tenv false
    in
    (* From now on, we work by side-effect *)
    (* 2. We now rename actual parameters in formal ones *)
    Apron.Abstract1.rename_array_with
      manager abstract2
      inargs calleeinfo.Equation.pinput
    ;
    (* 3. Last, we embed in callee environment *)
    Apron.Abstract1.change_environment_with
      manager abstract2
      calleeinfo.Equation.penv false
    ;
    (* 4. We possibly intersect with the result of a previous analysis *)
    begin match dest with
    | None -> ()
    | Some dest ->
				Apron.Abstract1.meet_with manager abstract2 dest
    end;
    abstract2;;

  let apply_return
    (manager:'a Apron.Manager.t)
    (abscaller:'a Apron.Abstract1.t) (abscallee:'a Apron.Abstract1.t)
    (calleeinfo:Equation.procinfo)
    (inargs:Apron.Var.t array) (outargs:Apron.Var.t array)
    (dest:'a Apron.Abstract1.t option)
    =
     (* 0. We forget local variables in abscallee *)
    let env =
      Apron.Environment.remove (Apron.Abstract1.env abscallee) (calleeinfo.Equation.plocal)
    in
    let res =
      Apron.Abstract1.change_environment manager abscallee env false
    in
    (* 1. We rename in modified abscallee
       - formal in parameters by actual inparameters
       - formal out parameters by special names (to avoid name conflicts)
    *)
    Apron.Abstract1.rename_array_with
      manager res calleeinfo.Equation.pinput inargs;
    (* 2. We unify the renamed callee value and the caller value *)
    Apron.Abstract1.unify_with manager res abscaller;
    (* 3. We assign the actual out parameters *)
    (*let env = Apron.Abstract1.env res in
    let tlinexpr =
      Array.map(fun var ->
				let e = Apron.Linexpr1.make ~sparse:true env in
				Apron.Linexpr1.set_coeff e var (Apron.Coeff.s_of_int 1);
				e
			)calleeinfo.Equation.poutput_tmp
    in
    if tlinexpr<>[||] then
      Apron.Abstract1.assign_linexpr_array_with
				manager res
				outargs tlinexpr None ;
    (* 4. We remove the introduced temporary variables *)
		  Apron.Abstract1.change_environment_with
		    manager res
		    (Apron.Abstract1.env abscaller) false;*)
    (* 5. We possibly intersect with the result of a previous analysis *)
    begin match dest with
    | None -> ()
    | Some dest ->
			Apron.Abstract1.meet_with manager res dest
    end;
    res;;

  (** Main transfer function *)
  let apply
    (graph:Equation.graph)
    ~(output : (Equation.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.output option)
    (manager:'a Apron.Manager.t)
    (hedge:int)
    (tabs:'a Apron.Abstract1.t array)
    :
    unit * 'a Apron.Abstract1.t
    =
    let transfer = PSHGraph.attrhedge graph hedge in
    let abs = tabs.(0) in
    let dest = 
    	match output with
      | None -> None
      | Some(output) ->
				let tdest = PSHGraph.succvertex graph hedge in
				assert(Array.length tdest = 1);
				let dest = PSHGraph.attrvertex output tdest.(0) in
				Some dest
    in
    let res =
      match transfer with
      | Equation.Tassign(var,expr) ->
	 			apply_tassign manager abs var expr dest
      | Equation.Lassign _ ->
	 			failwith ""
      | Equation.Condition cond ->
	  		apply_condition manager abs cond dest
      | Equation.Calle(callerinfo,calleeinfo,tin,tout) ->
	  		apply_call manager abs calleeinfo tin dest
      | Equation.Return(callerinfo,calleeinfo,tin,tout) ->
	  		apply_return manager abs tabs.(1) calleeinfo tin tout dest
    in
    ((),res);;

  (*  ===================================================================== *)
  (** {3 Compute (post)fixpoint} *)
  (*  ===================================================================== *)

  let compute
    ~(fmt : Format.formatter)
    (graph:Equation.graph)
    ~(output : (Equation.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.output option)
    (manager:'a Apron.Manager.t)
    ~(debug:int)
    :
    (Equation.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.output
    =
    let info = PSHGraph.info graph in
    let dummy_sstart = PSette.singleton Equation.compare_point Equation.vertex_dummy in
    let sstart =
      try
      let maininfo = Hashhe.find info.Equation.procinfo "phase" in
      Printf.printf "maininfo\n";
      Equation.print_procinfo fmt maininfo;
      Printf.printf "\n";
      let start = maininfo.Equation.pstart in
      begin match output with
      | None ->
      	Printf.printf "ouput is none in get sstart\n";
	 		 	PSette.singleton Equation.compare_point start
      | Some output ->
				let abstract = PSHGraph.attrvertex output start in
				if Apron.Abstract1.is_bottom manager abstract then
	   		 PSette.empty Equation.compare_point
	 			else
	   		 (PSette.singleton Equation.compare_point start)
      end
      with Not_found->Printf.printf "Not_found when get sstart\n";dummy_sstart
    in
    
    if PSette.is_empty sstart then begin
    	Printf.printf "sstart empty\n";
      make_emptyoutput graph manager
    end
    else(
    	Printf.printf "sstart not empty\n";
      let abstract_init = 
      	Printf.printf "abstract_init\n";
      	begin fun vertex ->
					begin match output with
					| None ->
						Printf.printf "ouput is none in get abstract_init\n";
						Apron.Abstract1.top manager (Hashhe.find info.Equation.pointenv vertex)
					| Some(output) ->
						Printf.printf "ouput is Some in get abstract_init\n";
						PSHGraph.attrvertex output vertex
					end
      	end
      in
      let fpmanager =
      	Printf.printf "fpmanager\n";
				make_fpmanager ~fmt graph ~output	apply abstract_init	manager ~debug
      in
      let fp =
      	Printf.printf "start analysis in Template.ml\n";
				(*if !Option.iteration_guided then
					Fixpoint.analysis_guided
						fpmanager graph sstart
						(fun filter  ->
							Fixpoint.make_strategy_default
					~vertex_dummy:Equation.vertex_dummy
					~hedge_dummy:Equation.hedge_dummy
					~priority:(PSHGraph.Filter filter)
					graph sstart)
				else*)
				Printf.printf "sstart1\n";
				PSette.iter(fun v->
					Equation.print_point Format.std_formatter v;
				)sstart;
				Printf.printf "\n";
					
    		if sstart!=dummy_sstart then
					begin
					Printf.printf "sstart!=dummy_sstart\n";
					let result = Fixpoint.analysis_std
						fpmanager graph sstart
						(Fixpoint.make_strategy_default
							~vertex_dummy:Equation.vertex_dummy
							~hedge_dummy:Equation.hedge_dummy
							graph sstart) in
					Printf.printf "analysis_std result\n";
					Fixpoint.print_output fpmanager fmt result;
					Printf.printf "\n";
					result
					end
				else
							begin
							Printf.printf "sstart==dummy_sstart\n";
							let sta = {Fixpoint.time=0.0;Fixpoint.iterations=0;Fixpoint.descendings=0;Fixpoint.stable=true} in
							let result = PSHGraph.create Equation.compare 0 sta in
							Printf.printf "analysis_std result\n";
							Fixpoint.print_output fpmanager fmt result;
							Printf.printf "\n";
							result
							end
			in
			fp
		)
end

(*  ********************************************************************** *)
(** {2 Bacward semantics} *)
(*  ********************************************************************** *)

module Backward = struct

  (*  ===================================================================== *)
  (** {3 Transfer function} *)
  (*  ===================================================================== *)

  let apply_tassign
    (manager:'a Apron.Manager.t)
    (abstract:'a Apron.Abstract1.t)
    (var: Apron.Var.t)
    (expr:Apron.Texpr1.t)
    (dest:'a Apron.Abstract1.t option)
    =
    let res =
      Apron.Abstract1.substitute_texpr
	manager abstract
	var expr dest
    in
(*
    printf "apply_tassign %a := %a (%a) = %a@."
      Apron.Var.print var Apron.Texpr1.print expr
      Apron.Abstract1.print abstract
      Apron.Abstract1.print res
    ;
*)
    res

  let apply_condition = Forward.apply_condition

  let apply_call
    (manager:'a Apron.Manager.t)
    (abstract:'a Apron.Abstract1.t)
    (callerinfo:Equation.procinfo)
    (calleeinfo:Equation.procinfo)
    (inargs:Apron.Var.t array)
    (dest:'a Apron.Abstract1.t option)
    =
    (* current environment *)
    let env = Apron.Abstract1.env abstract in
    (* 1. We begin by removing all non-argument variables from the current
     abstract value *)
    let tenv =
      environment_of_tvar
	(Apron.Environment.typ_of_var env)
	calleeinfo.Equation.pinput
    in
    let abstract2 =
      Apron.Abstract1.change_environment manager abstract tenv false
    in
    (* From now on, we work by side-effect *)
    (* 2. We now rename formal parameters into actual ones *)
    Apron.Abstract1.rename_array_with
      manager abstract2
      calleeinfo.Equation.pinput inargs
    ;
    (* 3. Last, we embed in caller environment *)
    Apron.Abstract1.change_environment_with
      manager abstract2
      callerinfo.Equation.penv false
    ;
    (* 4. We possibly intersect with the result of a previous analysis *)
    begin match dest with
    | None -> ()
    | Some dest ->
	Apron.Abstract1.meet_with manager abstract2 dest
    end;
    abstract2

  (*let apply_return
    (manager:'a Apron.Manager.t)
    (abstract:'a Apron.Abstract1.t)
    (callerinfo:Equation.procinfo)
    (calleeinfo:Equation.procinfo)
    (inargs:Apron.Var.t array) (outargs:Apron.Var.t array)
    (dest:'a Apron.Abstract1.t option)
    =
    (* 1. We rename actual output parameters by temporary output parameters 
    let res =
      Apron.Abstract1.rename_array
				manager abstract
				outargs calleeinfo.Equation.poutput_tmp
    in*)
    (* 2. We switch to an environment composed of
	  temporary output parameters and actual input paramaters 
    let lint = ref [] and lreal = ref [] in
    Array.iteri(fun i var ->
			let list =
				match Apron.Environment.typ_of_var calleeinfo.Equation.penv var with
				| Apron.Environment.INT -> lint
				| Apron.Environment.REAL -> lreal
			in
			let var_tmp = calleeinfo.Equation.poutput_tmp.(i) in
			list := var_tmp :: !list
    )calleeinfo.Equation.poutput;
    Array.iter(fun var ->
			let list =
				match Apron.Environment.typ_of_var callerinfo.Equation.penv var with
				| Apron.Environment.INT -> lint
				| Apron.Environment.REAL -> lreal
			in
			list := var :: !list
    )inargs;
    let tint = Array.of_list !lint and treal = Array.of_list !lreal in
    let tenv = Apron.Environment.make tint treal in
    Apron.Abstract1.change_environment_with manager res tenv false;*)
    (* 3. We rename
       temporary output parameters -> formal output
       actual input -> formal input 
    Apron.Abstract1.rename_array_with
      manager res
      (Array.append calleeinfo.Equation.poutput_tmp inargs)
      (Array.append calleeinfo.Equation.poutput  calleeinfo.Equation.pinput)
    ;*)
    (* 4. We embed into callee environment 
    Apron.Abstract1.change_environment_with manager res calleeinfo.Equation.penv false;*)
    (* 5. We possibly intersect with the result of a previous analysis 
    begin match dest with
    | None -> ()
    | Some dest ->
			Apron.Abstract1.meet_with manager res dest
    end;*)
    res*)

  (** Main transfer function *)
  let apply
    (graph:Equation.graph)
    ~(output : (Equation.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.output option)
    (manager:'a Apron.Manager.t)
    (hedge:int)
    (tabs:'a Apron.Abstract1.t array)
    :
    unit * 'a Apron.Abstract1.t
    =
    let transfer = PSHGraph.attrhedge graph hedge in
    let abs = tabs.(0) in
    let dest = match output with
      | None -> None
      | Some(output) ->
	  let tdest = PSHGraph.succvertex graph hedge in
	  assert(Array.length tdest = 1);
	  let dest = PSHGraph.attrvertex output tdest.(0) in
	  Some dest
    in
    let res =
      match transfer with
      | Equation.Tassign(var,expr) ->
	 			apply_tassign manager abs var expr dest
      | Equation.Lassign _ ->
	  		failwith ""
      | Equation.Condition cond ->
	  		apply_condition manager abs cond dest
      | Equation.Calle(callerinfo,calleeinfo,tin,tout) ->
	  		apply_call manager abs callerinfo calleeinfo tin dest
      | Equation.Return(callerinfo,calleeinfo,tin,tout) ->
	  		failwith ""(*apply_return manager abs callerinfo calleeinfo tin tout dest*)
    in
    ((),res)

  (*  ===================================================================== *)
  (** {3 Compute (post)fixpoint} *)
  (*  ===================================================================== *)

  let compute
      ~(fmt : Format.formatter)
      (prog:Cil_types.file)
      (graph:Equation.graph)
      ~(output : (Equation.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.output option)
      (manager:'a Apron.Manager.t)
      ~(debug:int)
      :
      (Equation.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.output
      =
    let info = PSHGraph.info graph in
    let sstart = ref (PSette.empty Equation.compare_point) in
    
    Globals.Functions.iter(fun kf ->
			try
				let fundec = Kernel_function.get_definition kf in
				List.iter(fun stmt ->
					(*if stmt.Spl_syn.instruction = Spl_syn.FAIL then 
					(let ok = 
							match output with
							| None -> true
							| Some output ->
									let abstract = PSHGraph.attrvertex output bpoint in
									not (Apron.Abstract1.is_bottom manager abstract)
						in
						if ok then
							sstart := PSette.add bpoint !sstart;
					)*)();
				)fundec.sallstmts;
			with Kernel_function.No_Definition -> Printf.printf "exception No_Definition\n";
		);
    (*List.iter(fun procedure ->
			Spl_syn.iter_eltinstr(fun (bpoint,instr) ->
				if instr.Spl_syn.instruction = Spl_syn.FAIL then begin
					let ok = 
						match output with
						| None -> true
						| Some output ->
								let abstract = PSHGraph.attrvertex output bpoint in
								not (Apron.Abstract1.is_bottom manager abstract)
					in
					if ok then
						sstart := PSette.add bpoint !sstart;
					end
			)procedure.Spl_syn.pcode;
    )prog.Spl_syn.procedures;*)

    if PSette.is_empty !sstart then begin
      make_emptyoutput graph manager
    end
    else
    (
      let abstract_init = begin fun vertex ->
				begin match output with
				| None ->
						Apron.Abstract1.top manager (Hashhe.find info.Equation.pointenv vertex)
				| Some(output) ->
						PSHGraph.attrvertex output vertex
				end
      end
      in
      
      let fpmanager = make_fpmanager ~fmt graph ~output apply abstract_init manager ~debug in
      
      let fp =
				(*if !Option.iteration_guided then
					Fixpoint.analysis_guided
						fpmanager graph !sstart
						(fun filter  ->
							Fixpoint.make_strategy_default
					~vertex_dummy:Equation.vertex_dummy
					~hedge_dummy:Equation.hedge_dummy
					~priority:(PSHGraph.Filter filter)
					graph !sstart)
				else*)
					Fixpoint.analysis_std
						fpmanager graph !sstart
						(Fixpoint.make_strategy_default
							~vertex_dummy:Equation.vertex_dummy
							~hedge_dummy:Equation.hedge_dummy
							graph !sstart)
			in
			fp
		)
end

let print_output prog fmt fp =
	Globals.Functions.iter(fun kf ->
			try
				let fundec = Kernel_function.get_definition kf in
				Cil.d_block fmt fundec.sbody;
			with Kernel_function.No_Definition -> Printf.printf "exception No_Definition\n";
		)
    
let var_x = Apron.Var.of_string "x";;
let var_y = Apron.Var.of_string "y";;
let var_z = Apron.Var.of_string "z";;
let var_w = Apron.Var.of_string "w";;
let var_u = Apron.Var.of_string "u";;
let var_v = Apron.Var.of_string "v";;
let var_a = Apron.Var.of_string "a";;
let var_b = Apron.Var.of_string "b";;

let output_of_graph graph =
	PSHGraph.copy
  	(fun vertex attrvertex -> attrvertex.FixpointType.reach)
    (fun hedge attrhedge -> attrhedge.FixpointType.arc)
    (fun info -> {
			Fixpoint.time = !(info.FixpointType.itime);
			Fixpoint.iterations = !(info.FixpointType.iiterations);
			Fixpoint.descendings = !(info.FixpointType.idescendings);
			Fixpoint.stable = !(info.FixpointType.istable)
    })
    graph;;
      
let lincons1_array_print fmt x =
  Apron.Lincons1.array_print fmt x;;

let generator1_array_print fmt x =
  Apron.Generator1.array_print fmt x;;

let generate_template (man:'a Apron.Manager.t) (vars:Apron.Var.t array) (cofs:Apron.Var.t array)=
	Format.printf "Using Library: %s, version %s@." (Apron.Manager.get_library man) (Apron.Manager.get_version man);
	try
		let env = Apron.Environment.make vars cofs in
  	Format.printf "env=%a@."
   	 (fun x -> Apron.Environment.print x) env;
    
    let tab = Apron.Lincons1.array_make env (Array.length vars) in
    let expr = Apron.Linexpr1.make env in
    let cons = Apron.Lincons1.make expr Apron.Lincons1.EQ in
  	Apron.Lincons1.array_set tab 0 cons;
  	
  	
		Format.printf "tab = %a@." lincons1_array_print tab;

		let abs = Apron.Abstract1.of_lincons_array man env tab in
		Format.printf "abs=%a@." Apron.Abstract1.print abs;
		let array = Apron.Abstract1.to_generator_array man abs in
		Format.printf "gen=%a@." generator1_array_print array;
		let array = Apron.Abstract1.to_generator_array man abs in
		Format.printf "gen=%a@." generator1_array_print array;
		
  with Failure(e)->Printf.printf "make failure\n";;
	
let ex1 (man:'a Apron.Manager.t) : 'a Apron.Abstract1.t =
  Printf.printf "Using Library: %s, version %s@." (Apron.Manager.get_library man) (Apron.Manager.get_version man);

  let env = Apron.Environment.make
    [|var_x; var_y; var_z; var_w|]
    [|var_u; var_v; var_a; var_b|]
  in
  let env2 = Apron.Environment.make [|var_x; var_y; var_z; var_w|] [||]
  in
  Format.printf "env=%a@.env2=%a@."
    (fun x -> Apron.Environment.print x) env
    (fun x -> Apron.Environment.print x) env2
  ;
  (* Creation of abstract value
     1/2x+2/3y=1, [1,2]<=z+2w<=4, 0<=u<=5 *)
  let tab = Apron.Lincons1.array_make env 5 in

  let expr = Apron.Linexpr1.make env in
  Apron.Linexpr1.set_array expr
    [|
      (Apron.Coeff.Scalar (Apron.Scalar.Mpqf (Mpqf.of_frac 1 2)), var_x);
      (Apron.Coeff.Scalar (Apron.Scalar.Mpqf (Mpqf.of_frac 2 3)), var_y)
    |]
    (Some (Apron.Coeff.Scalar (Apron.Scalar.Mpqf (Mpqf.of_int (1)))))
    ;
  let cons = Apron.Lincons1.make expr Apron.Lincons1.EQ in
  Apron.Lincons1.array_set tab 0 cons;

  let expr = Apron.Linexpr1.make env in
  Apron.Linexpr1.set_array expr
    [|
      (Apron.Coeff.Scalar (Apron.Scalar.Float (-1.0)), var_z);
      (Apron.Coeff.Scalar (Apron.Scalar.Float (-2.0)), var_w)
    |]
    (Some (Apron.Coeff.Scalar (Apron.Scalar.Float (4.0))))
  ;
  Apron.Lincons1.array_set tab 1 (Apron.Lincons1.make expr Apron.Lincons1.SUPEQ);
 
  let expr = Apron.Linexpr1.make env2 in
  Apron.Linexpr1.set_array expr
    [|
      (Apron.Coeff.Scalar (Apron.Scalar.Float 1.0), var_z);
      (Apron.Coeff.Scalar (Apron.Scalar.Float 2.0), var_w)
    |]
    (Some 
      (Apron.Coeff.Interval
	(Apron.Interval.of_infsup
	  (Apron.Scalar.Float (-2.0))
	  (Apron.Scalar.Float (-1.0)))))
    ;
  Apron.Linexpr1.extend_environment_with expr env;
  Apron.Lincons1.array_set tab 2 (Apron.Lincons1.make expr Apron.Lincons1.SUPEQ);
 
  let cons = Apron.Lincons1.make (Apron.Linexpr1.make env) Apron.Lincons1.SUPEQ in
  Apron.Lincons1.set_array cons
    [|
      (Apron.Coeff.Scalar (Apron.Scalar.Mpqf (Mpqf.of_int 1)), var_u)
    |]
    None
  ;
  Apron.Lincons1.array_set tab 3 cons;
  let cons = Apron.Lincons1.make (Apron.Linexpr1.make env) Apron.Lincons1.SUPEQ in
  Apron.Lincons1.set_array cons
    [|
      (Apron.Coeff.Scalar (Apron.Scalar.Mpqf (Mpqf.of_int (-1))), var_u)
    |]
    (Some (Apron.Coeff.Scalar (Apron.Scalar.Mpqf (Mpqf.of_int 5))))
  ;
  Apron.Lincons1.array_set tab 4 cons;
 
  Format.printf "tab = %a@." lincons1_array_print tab;

  let abs = Apron.Abstract1.of_lincons_array man env tab in
  Format.printf "abs=%a@." Apron.Abstract1.print abs;
  let array = Apron.Abstract1.to_generator_array man abs in
  Format.printf "gen=%a@." generator1_array_print array;
  let array = Apron.Abstract1.to_generator_array man abs in
  Format.printf "gen=%a@." generator1_array_print array;

  (* Extraction (we first extract values for existing constraints, then for
     dimensions) *)
  let box = Apron.Abstract1.to_box man abs in
  Format.printf "box=%a@." (print_array Apron.Interval.print) box.Apron.Abstract1.interval_array;
  for i=0 to 4 do
    let expr = Apron.Lincons1.get_linexpr1 (Apron.Lincons1.array_get tab i) in
    let box = Apron.Abstract1.bound_linexpr man abs expr in
    Format.printf "Bound of %a = %a@."
      Apron.Linexpr1.print expr
      Apron.Interval.print box;
  done;
  (* 2. dimensions *)
  (* 3. of box *)
  let abs2 = Apron.Abstract1.of_box man env [|var_x; var_y; var_z; var_w; var_u; var_v; var_a; var_b|]
    box.Apron.Abstract1.interval_array 
  in
  Format.printf "abs2=%a@." Apron.Abstract1.print abs2;
  (* 4. Tests top and bottom *)
  let abs3 = Apron.Abstract1.bottom man env in
  Format.printf "abs3=%a@.is_bottom(abs3)=%b@."
    Apron.Abstract1.print abs3 
    (Apron.Abstract1.is_bottom man abs3);

  Format.printf "abs=%a@." 
    Apron.Abstract1.print abs;
  let p2 = Apron.Abstract1.expand man abs (var_y) [|Apron.Var.of_string "y1"; Apron.Var.of_string "y2"|] in
  Format.printf "p2=expand(abs,y,[y1,y2]))=%a@."
    Apron.Abstract1.print p2; 
  let p2 = Apron.Abstract1.expand man abs (var_u) [|Apron.Var.of_string "u1"; Apron.Var.of_string "u2"|] in
  Format.printf "p2=expand(abs,u,[u1,u2]))=%a@."
    Apron.Abstract1.print p2;
	let interval_x = Apron.Abstract1.bound_variable man abs var_x in
	Apron.Interval.print Format.std_formatter interval_x;
	Format.print_flush ();
  abs
;;