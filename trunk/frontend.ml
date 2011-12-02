open Format
open Equation
open Cil_types
open Loop_parameters
  
let build_graphs (fmt:Format.formatter) (prog:Cil_types.file):graph * graph =
  (* Converting prog into a forward equation system *)
  let (fgraph:graph) = C2equation.Forward.make prog in
  (* Converting prog into a backward equation system *)
  let (bgraph:graph) = C2equation.Backward.make prog in
  (fgraph,bgraph)
  
let compute_and_display (fmt:Format.formatter) (prog:Cil_types.file) (fgraph:Equation.graph) (bgraph:Equation.graph) (manager:'a Apron.Manager.t) : unit =
  let (previous:(Cil_types.location, int, 'a Apron.Abstract1.t, unit) Equation.output option ref) =
    ref None
  in
  List.iter(fun t ->
      (* Computation *)
  	let fp =
			begin match t with
			| Loop_parameters.Forward ->
				Printf.printf "Forward\n";
				(*let fp =
					Solving.Forward.compute ~fmt fgraph ~output:(!previous) manager ~debug:!debug
				in
				fprintf fmt "%sAnnotated program after forward analysis%s@ "
					(!Option.displaytags).precolorB (!Option.displaytags).postcolor;
					fp*)
			| Loop_parameters.Backward ->
				Printf.printf "Backward\n";
				(*let fp =
					Solving.Backward.compute ~fmt prog bgraph ~output:(!previous) manager ~debug:!debug
				in
				fprintf fmt "%sAnnotated program after backward analysis%s@ "
					(!Option.displaytags).precolorB (!Option.displaytags).postcolor;
					fp*)
			end
    in
      (* Display 
      Solving.print_output prog fmt fp;
      previous := Some fp;*)();
    )!analysis;
  ()
