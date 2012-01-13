(** Fixpoint analysis of an equation system *)

open Format

(*  ********************************************************************** *)
(** {2 Datatypes} *)
(*  ********************************************************************** *)

type ('vertex,'hedge,'abstract,'arc) manager =
  ('vertex,'hedge,'abstract,'arc) FixpointType.manager = {
    mutable bottom : 'vertex -> 'abstract;
    mutable canonical : 'vertex -> 'abstract -> unit;
    mutable is_bottom : 'vertex -> 'abstract -> bool;
    mutable is_leq : 'vertex -> 'abstract -> 'abstract -> bool;
    mutable join :  'vertex -> 'abstract -> 'abstract -> 'abstract;
    mutable join_list : 'vertex -> 'abstract list -> 'abstract;
    mutable widening : 'vertex -> 'abstract -> 'abstract -> 'abstract;
    mutable abstract_init : 'vertex -> 'abstract;
    mutable arc_init : 'hedge -> 'arc;
    mutable apply : 'hedge -> 'abstract array -> 'arc * 'abstract;
    mutable print_vertex : Format.formatter -> 'vertex -> unit;
    mutable print_hedge : Format.formatter -> 'hedge -> unit;
    mutable print_abstract: Format.formatter -> 'abstract -> unit;
    mutable print_arc: Format.formatter -> 'arc -> unit;
    mutable accumulate : bool;
    mutable widening_start : int;
    mutable widening_descend : int;
    mutable print_fmt : Format.formatter;
    mutable print_analysis : bool;
    mutable print_component : bool;
    mutable print_step : bool;
    mutable print_state : bool;
    mutable print_postpre : bool;
    mutable print_workingsets : bool;
    mutable dot_fmt : Format.formatter option;
    mutable dot_vertex : Format.formatter -> 'vertex -> unit;
    mutable dot_hedge : Format.formatter -> 'hedge -> unit;
    mutable dot_attrvertex : Format.formatter -> 'vertex -> unit;
    mutable dot_attrhedge : Format.formatter -> 'hedge -> unit;
  }

type ('vertex,'hedge) strategy_vertex =
  ('vertex,'hedge) FixpointType.strategy_vertex = {
    mutable vertex : 'vertex;
    mutable hedges : 'hedge list;
    mutable widen : bool;
  }
type ('vertex,'hedge) strategy =
  ('vertex,'hedge) strategy_vertex Ilist.t
  (* = ('vertex,'hedge) FixpointType.strategy *)

type ('vertex,'hedge) equation =
  'vertex -> ('hedge, 'vertex array * 'vertex) PMappe.t
  (* = ('vertex,'hedge) FixpointType.equation *)

type stat = FixpointType.stat = {
  time : float;
  iterations : int;
  descendings : int;
  stable : bool;
}
  (** statistics at the end of the analysis *)

type ('vertex,'hedge,'abstract,'arc) output =
  ('vertex,'hedge,'abstract, 'arc, stat) PSHGraph.t
  (** result of the analysis *)

(*  ********************************************************************** *)
(** {2 Functions} *)
(*  ********************************************************************** *)

let make_strategy_default
    ?depth ?priority
    ~vertex_dummy ~hedge_dummy
    graph sinit
    =
  FixpointType.make_strategy_default
    ?depth ?priority ~vertex_dummy ~hedge_dummy graph sinit

let analysis_std manager input sinit strategy (ap_manager:'a Apron.Manager.t)
    =
  FixpointStd.analysis manager input sinit strategy ap_manager

(*
let analysis_guided manager input sinit make_strategy
    =
  FixpointGuided.analysis manager input sinit make_strategy

let analysis_dyn compare ~guided manager equation sinit make_strategy
=
  FixpointDyn.analysis compare ~guided manager equation sinit make_strategy

let equation_of_graph ?filter graph
    =
  FixpointDyn.equation_of_graph ?filter graph

let graph_of_equation compare ?filter ~make_attrvertex ~make_attrhedge ~info equation
    =
  FixpointDyn.graph_of_equation compare
    ?filter ~make_attrvertex ~make_attrhedge ~info equation
*)

(*  ********************************************************************** *)
(** {2 Printing functions} *)
(*  ********************************************************************** *)

let print_strategy_vertex = FixpointType.print_strategy_vertex
let print_strategy = FixpointType.print_strategy
let print_stat = FixpointType.print_stat
let print_output = FixpointType.print_output
