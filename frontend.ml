open Format
open Equation
open Template
open Cil_types
open Loop_parameters
  
let build_graphs (fmt:Format.formatter) (prog:Cil_types.file):graph * graph =
  (* Converting prog into a forward equation system *)
  let (fgraph:graph) = C2equation.Forward.make prog Format.std_formatter in
	fprintf fmt "print graph after ok 1\n";
  Equation.print_graph fmt fgraph;
	fprintf fmt "print graph after ok 2\n";
  (* Converting prog into a backward equation system *)
  let (bgraph:graph) = C2equation.Backward.make prog in
  (fgraph,bgraph)
  

let compute_and_display (fmt:Format.formatter) (prog:Cil_types.file) (fgraph:Equation.graph) (bgraph:Equation.graph) (manager:'a Apron.Manager.t) : unit =
  let (previous:(Equation.point, int, 'a Apron.Abstract1.t, unit) Fixpoint.output option ref) =
    ref None
  in
  List.iter(fun t ->
      (* Computation *)
  	let fp =
			begin match t with
			| Loop_parameters.Forward ->
				Printf.printf "Forward\n";
				let fp =
					Template.Forward.compute ~fmt fgraph ~output:(!previous) manager ~debug:0
				in
				fprintf fmt "%sAnnotated program after forward analysis%s@ " (!Loop_parameters.displaytags).precolorB (!Loop_parameters.displaytags).postcolor;
				fp
			| Loop_parameters.Backward ->
				Printf.printf "Backward\n";
				let fp =
					Template.Backward.compute ~fmt prog bgraph ~output:(!previous) manager ~debug:0
				in
				fprintf fmt "Annotated program after backward analysis@ ";
					fp
			end
    in
      (* Display *)
      Template.print_output prog fmt fp;
      previous := Some fp;
    )!analysis;
  ()
