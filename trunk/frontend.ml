open Format
open Equation
open Template
open Cil_types
open Loop_parameters
  
let build_graphs (fmt:Format.formatter) (prog:Equation.info) globalarray arrayvars ipl wp_compute annots unknownout :graph * graph =
  (* Converting prog into a forward equation system *)
  let (fgraph:graph) = C2equation.Forward.make prog globalarray arrayvars fmt ipl wp_compute annots unknownout in
	(*fprintf fmt "print fgraph after ok 1\n";
  Equation.print_graph fmt fgraph;
	fprintf fmt "print fgraph after ok 2\n";
  Converting prog into a backward equation system *)
  (*let (bgraph:graph) = C2equation.Backward.make prog in
  fprintf fmt "print bgraph after ok 1\n";
  Equation.print_graph fmt bgraph;
	fprintf fmt "print bgraph after ok 2\n";*)
	let bgraph = fgraph in
  (fgraph,bgraph)
		
let compute_and_display (fmt:Format.formatter) (prog:Equation.info) (fgraph:Equation.graph) (bgraph:Equation.graph) (manager:'a Apron.Manager.t) annots : unit =
  let (previous:(Equation.point, int, 'a Apron.Abstract1.t, Equation.transfer) Fixpoint.output option ref) =
    ref None
  in
  
  Hashtbl.iter(fun pname _->
  	List.iter(fun t ->
      (* Computation *)
			let fp =
				begin match t with
				| Loop_parameters.Forward ->
					Printf.printf "Forward:%s\n" pname;
					let fp =
						Template.Forward.compute ~fmt fgraph pname ~output:(!previous) manager annots ~debug:1
					in
					fp
				| Loop_parameters.Backward ->
					Printf.printf "Backward\n";
					let fp =
						Template.Backward.compute ~fmt bgraph ~output:(!previous) manager ~debug:1
					in
					fp
				end
		  in
		    (* Apply and Display *)
		  previous := Some fp;
		  Apply.apply_result prog fmt fp annots;
		  (*Template.print_output prog fmt fp;
		  match !previous with
		  | Some(out)->
		    Printf.printf "previous is some\n";
		  | None->
		    Printf.printf "previous is none\n";*)
		)!analysis;
  )prog.Equation.procinfo
