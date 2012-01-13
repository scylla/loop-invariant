(** Fixpoint analysis of an equation system: types *)

(** {2 Introduction}

    This module provides a generic engine for computing
    iteratively the solution of a fixpoint equation on a lattice.

    The equation system is represented with an hypergraph, in
    which vertices corresponds to unknown and oriented hyperedges
    to functions. It is assumed that hyperedges have unique
    destination vertex, and that associated functions are strict
    in each of their arguments: a bottom value in one of the
    argument implies that the result is empty.

    The equation system is parameterized by a manager, which
    provides the operations of the abstract lattices, and the
    transfer functions involved in the equation system.

    This interface is polymorphic and makes use of the following
    type variables:

    - ['vertex] is the type of vertex identifiers in the hypergraphs
    - ['hedge] is the type of hyperedges identifiers in the hypergraphs
    - ['abstract] is the type of abstract values (or dataflow properties)
    - ['arc] is the type of the information associated to hyperedges (optional features).

*)

open Format

(*  ********************************************************************** *)
(** {2 Public datatypes} *)
(*  ********************************************************************** *)

(*  ====================================================================== *)
(** {3 Manager} *)
(*  ====================================================================== *)

type ('vertex,'hedge,'abstract,'arc) manager = {
  (** Lattice operation *)
  mutable bottom : 'vertex -> 'abstract;
  mutable canonical : 'vertex -> 'abstract -> unit;
  mutable is_bottom : 'vertex -> 'abstract -> bool;
  mutable is_leq : 'vertex -> 'abstract -> 'abstract -> bool;
  mutable join :  'vertex -> 'abstract -> 'abstract -> 'abstract;
  mutable join_list : 'vertex -> 'abstract list -> 'abstract;
  mutable widening : 'vertex -> 'abstract -> 'abstract -> 'abstract;

  (** Initialisation of equations *)
  mutable abstract_init : 'vertex -> 'abstract;
  mutable arc_init : 'hedge -> 'arc;

  (** Interpreting hyperedges *)
  mutable apply : 'hedge -> 'abstract array -> 'arc * 'abstract;

  (** Printing functions *)
  mutable print_vertex : Format.formatter -> 'vertex -> unit;
  mutable print_hedge : Format.formatter -> 'hedge -> unit;
  mutable print_abstract: Format.formatter -> 'abstract -> unit;
  mutable print_arc: Format.formatter -> 'arc -> unit;

  (** Fixpoint Options *)
  mutable accumulate : bool;

  (** Widening Options *)
  mutable widening_start : int;
  mutable widening_descend : int;

  (** Printing Options *)
  mutable print_fmt : Format.formatter;
  mutable print_analysis : bool;
  mutable print_component : bool;
  mutable print_step : bool;
  mutable print_state : bool;
  mutable print_postpre : bool;
  mutable print_workingsets : bool;

  (** DOT Options *)
  mutable dot_fmt : Format.formatter option;
  mutable dot_vertex : Format.formatter -> 'vertex -> unit;
  mutable dot_hedge : Format.formatter -> 'hedge -> unit;
  mutable dot_attrvertex : Format.formatter -> 'vertex -> unit;
  mutable dot_attrhedge : Format.formatter -> 'hedge -> unit;
}

(*  ====================================================================== *)
(** {3 Dynamically explored equation system} *)
(*  ====================================================================== *)

type ('vertex,'hedge) equation =
  'vertex -> ('hedge, 'vertex array * 'vertex) PMappe.t

(*  ====================================================================== *)
(** {3 Iteration strategies} *)
(*  ====================================================================== *)

type ('vertex,'hedge) strategy_vertex = {
  mutable vertex : 'vertex;
  mutable hedges : 'hedge list;
  mutable widen : bool;
}
type ('vertex,'hedge) strategy = ('vertex,'hedge) strategy_vertex Ilist.t

let print_strategy_vertex
  (man:('vertex,'hedge,'abstract,'arc) manager)
  fmt
  (v:('vertex,'hedge) strategy_vertex)
  =
  fprintf fmt "@[<h>(%b,%a,%a)@]"
    v.widen
    man.print_vertex v.vertex
    (Print.list ~first:"@[<h>[" ~sep:"," ~last:"]@]"
	man.print_hedge)
    v.hedges

let print_strategy
  (man:('vertex,'hedge,'abstract,'arc) manager)
  fmt
  (s:('vertex,'hedge) strategy)
  =
  Ilist.print
    ~first:"[ @[<hv>"
    ~last:"@] ]"
    (print_strategy_vertex man) fmt s


let make_strategy_vertex
    (graph:('vertex,'hedge,'a,'b,'c) PSHGraph.t)
    (widen:bool)
    (vertex:'vertex)
    :
    ('vertex,'hedge) strategy_vertex
    =
  let spredhedges = PSHGraph.predhedge graph vertex in
  let hedges = PSette.elements spredhedges in
  
  let strategy_vertex = {
    vertex = vertex;
    hedges = hedges;
    widen = widen
  }
  in
  strategy_vertex

let make_strategy_default
    ?(depth=2)
    ?priority
    ~(vertex_dummy:'vertex)
    ~(hedge_dummy:'hedge)
    (graph:('vertex,'hedge,'a,'b,'c) PSHGraph.t)
    (sinit:'vertex PSette.t)
    :
    ('vertex,'hedge) strategy
    =
  let scfc =
    PSHGraph.scfc_multi
      vertex_dummy hedge_dummy
      ?priority graph sinit
  in
  let scfc = Ilist.map
    (begin fun flag vertex ->
      make_strategy_vertex graph flag vertex
    end)
    scfc
  in
  Ilist.flatten ~depth scfc

(*  ====================================================================== *)
(** {3 Output} *)
(*  ====================================================================== *)

(** statistics at the end of the analysis *)
type stat = {
  time : float;
  iterations : int;
  descendings : int;
  stable : bool;
}

(** result of the analysis *)
type ('vertex,'hedge,'abstract,'arc) output =
  ('vertex,'hedge,'abstract, 'arc, stat) PSHGraph.t

let print_stat fmt (stat:stat)
  =
  fprintf fmt "{ @[<hov>time=%f;@ iterations=%i;@ descendings=%i;@ stable=%b@] }"
    stat.time stat.iterations stat.descendings stat.stable

let print_output
    (man:('vertex,'hedge,'abstract,'arc) manager)
    fmt
    (g:('vertex,'hedge,'abstract,'arc,stat) PSHGraph.t)
    =
  PSHGraph.print
    man.print_vertex
    man.print_hedge
    man.print_abstract
    man.print_arc
    print_stat
    fmt
    g

(*  ********************************************************************** *)
(** {2 Internal datatypes} *)
(*  ********************************************************************** *)

type 'abstract attr = {
  mutable reach : 'abstract;
  mutable empty : bool;
}

type 'arc arc = {
  mutable arc : 'arc;
  mutable aempty : bool;
}

type ('vertex,'hedge) infodyn = {
  mutable iaddhedge : ('hedge,'vertex array * 'vertex) PHashhe.t;
  iequation : ('vertex,'hedge) equation
}

type ('vertex,'hedge) info = {
  iinit : 'vertex PSette.t;
  itime : float ref;
  iiterations : int ref;
  idescendings : int ref;
  istable : bool ref;
  mutable iworkvertex : ('vertex,unit) PHashhe.t;
  mutable iworkhedge : ('hedge,unit) PHashhe.t;
  iinfodyn : ('vertex,'hedge) infodyn option;
}

type ('vertex,'hedge,'abstract,'arc) fpGraph =
  ('vertex, 'hedge, 'abstract attr, 'arc arc, ('vertex,'hedge) info) PSHGraph.t

(*  ====================================================================== *)
(** {3 Printing functions} *)
(*  ====================================================================== *)

let print_attr
    (man:('vertex,'hedge,'abstract,'arc) manager)
    (fmt:Format.formatter)
    (attr:'abstract attr)
  =
  fprintf fmt "{ @[<hov>reach=%a;@ empty=%b@] }"
    man.print_abstract attr.reach
    attr.empty

let print_arc
    (man:('vertex,'hedge,'abstract,'arc) manager)
    (fmt:Format.formatter)
    (arc:'arc arc)
  =
  fprintf fmt "{ @[<hov>arc=%a;@ aempty=%b@] }"
    man.print_arc arc.arc
    arc.aempty

let print_info
    (man:('vertex,'hedge,'abstract,'arc) manager)
    (fmt:Format.formatter)
    (info:('vertex,'hedge) info)
  =
  fprintf fmt "{ @[<hov>itime=%f;@ iiterations=%i;@ idescendings=%i;@ istable=%b;@ iworkvertex=%a;@ iworkhedge=%a@] }"
    !(info.itime)
    !(info.iiterations)
    !(info.idescendings)
    !(info.istable)
    (PHashhe.print man.print_vertex (fun _ _ -> ())) info.iworkvertex
    (PHashhe.print man.print_hedge (fun _ _ -> ())) info.iworkhedge

let print_workingsets
    (man:('vertex,'hedge,'abstract,'arc) manager)
    (fmt:Format.formatter)
    (graph:('vertex,'hedge,'abstract,'arc) fpGraph)
    :
    unit
    =
  let hashprint print fmt x =
      PHashhe.print
	~first:"[@[<hov>" ~last:"@]]"
	~firstbind:"" ~sepbind:"" ~lastbind:""
	print (fun _ _ -> ())
	fmt x
  in
  let info = PSHGraph.info graph in
  fprintf fmt "@[<v>workvertex = %a@ workhedge = %a"
    (hashprint man.print_vertex) info.iworkvertex
    (hashprint man.print_hedge) info.iworkhedge
  ;
  begin match info.iinfodyn with
  | Some(dyn) ->
      fprintf fmt "@ addhedge = %a"
	(hashprint man.print_hedge) dyn.iaddhedge
  | None -> ()
  end;
  fprintf fmt "@]"

let print_graph
    (man:('vertex,'hedge,'abstract,'arc) manager)
    (fmt:Format.formatter)
    (g:('vertex,'hedge,'abstract,'arc) fpGraph)
    =
  PSHGraph.print
    man.print_vertex
    man.print_hedge
    (print_attr man)
    (print_arc man)
    (print_info man)
    fmt
    g

(*  ====================================================================== *)
(** {3 DOT functions} *)
(*  ====================================================================== *)

let set2_of_strategy
    comparev
    (strategy:('vertex,'hedge) strategy)
    :
    'vertex PSette.t * 'vertex PSette.t
    =
  let empty = PSette.empty comparev in
  Ilist.fold_left
    (begin fun (res,resw) _ v ->
      if v.widen then
	res,(PSette.add v.vertex resw)
      else
	(PSette.add v.vertex res),resw
    end)
    (empty,empty) strategy

let dot_graph
    ?(style="size=\"7.5,10\";center=true;ranksep=0.16;nodesep=0.02;")
    ?(titlestyle="fontsize=18")
    ?(vertexstyle="shape=box,fontsize=18,height=0.02,width=0.01")
    ?(hedgestyle="shape=plaintext,fontsize=18,height=0.0,width=0.01")
    ?strategy
    ?vertex
    (man:('vertex,'hedge,'abstract,'arc) manager)
    (graph:('vertex,'hedge,'abstract,'arc) fpGraph)
    ~(title:string)
    =
  let comparev = graph.PSHGraph.compare.PSHGraph.comparev in
  match man.dot_fmt with
  | None -> ()
  | Some dot_fmt ->
      let (set,setw) = match strategy with
	| None -> let e = PSette.empty comparev in (e,e)
	| Some strategy -> set2_of_strategy comparev strategy
      in
      let info = PSHGraph.info graph in
      let fvertexstyle = begin fun v ->
	let vertexstyle =
	  if begin match vertex with
	  | None -> false
	  | Some vertex -> (graph.PSHGraph.compare.PSHGraph.comparev v vertex) = 0
	  end
	  then
	    vertexstyle^",style=filled,fillcolor=coral1"
	  else if PSette.mem v setw then
	    vertexstyle^",style=filled,fillcolor=red1"
	  else if PSette.mem v set then
	    vertexstyle^",style=filled,fillcolor=orange1"
	  else
	    vertexstyle
	in
	let vertexstyle =
	  if PHashhe.mem info.iworkvertex v then
	    vertexstyle^",fontcolor=blue3"
	  else
	    vertexstyle
	in
	vertexstyle
      end
      in
      let fhedgestyle = begin fun h ->
	let hedgestyle =
	  if PHashhe.mem info.iworkhedge h then
	    hedgestyle^",fontcolor=blue3"
	  else
	    hedgestyle
	in
	hedgestyle
      end
      in
      PSHGraph.print_dot
	~titlestyle
	~style
	~fvertexstyle
	~fhedgestyle
	~title
	(fun fmt vertex ->
	  fprintf fmt "\"%s\""
	    (Print.escaped ~linebreak:'n'
	      (Print.sprintf "%a" man.dot_vertex vertex)))
	(fun fmt hedge ->
	  fprintf fmt "\"%s\""
	    (Print.escaped ~linebreak:'n'
	      (Print.sprintf "%a" man.dot_hedge hedge)))
	(fun fmt vertex attr ->
	  fprintf fmt "%s"
	    (Print.escaped ~linebreak:'n'
	      (Print.sprintf ~margin:40 "%a@.%a"
		man.dot_attrvertex vertex
		man.print_abstract attr.reach)))
	(fun fmt hedge arc ->
	  fprintf fmt "%s"
	    (Print.escaped ~linebreak:'n'
	      (Print.sprintf ~margin:40 "%a@.%a"
		man.dot_attrhedge hedge
		man.print_arc arc.arc)))
	dot_fmt
	graph
