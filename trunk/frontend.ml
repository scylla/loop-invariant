open Format
open Equation
  
let build_graphs (fmt:Format.formatter) (prog:Cil_types.file):graph * graph =
  (* Converting prog into a forward equation system *)
  let (fgraph:graph) = C2equation.Forward.make prog in
  (* Converting prog into a backward equation system *)
  let (bgraph:graph) = C2equation.Backward.make prog in
  (fgraph,bgraph)
