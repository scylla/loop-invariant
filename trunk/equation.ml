(** Representing equation system *)

open Format
open Lexing
open Cil

type loop = {con:Cil_types.exp;body:Cil_types.stmt list}

let print_loop fmt loop =
	fprintf fmt "while(%a){}" 
	Cil.d_exp loop.con
	 
(*vertex and point*)
type point = {fname:string;sid:int}
type vertex = point

let print_point fmt p =
	fprintf fmt "%s:%d" p.fname p.sid

	
let compare_point (a:vertex) (b:vertex) =
  (compare a.sid b.sid)(*(String.compare a.fname b.fname)&&*)

let equal_point (a:vertex) (b:vertex) =
  (a.sid==b.sid)(*a.fname==b.fname&&*)

let hash_point (x:vertex) =
  abs (x.sid+5)
  	
(*edge*)
type hedge = int

let print_hedge fmt e =
	fprintf fmt "%d" e

(*dummy*)
let vertex_dummy = 
	{
		fname = "";
		sid = -2;
	}
let hedge_dummy = -1

let compare = {
  PSHGraph.hashv = {
    Hashhe.hash = hash_point;
    Hashhe.equal = equal_point;
  };
  PSHGraph.hashh = {
    Hashhe.hash = (fun x -> abs x);
    Hashhe.equal = (==)
  };
  PSHGraph.comparev = compare_point;
  PSHGraph.compareh = (-)
}

let create n info = PSHGraph.create compare n info

(*  ********************************************************************* *)
(** {2 Preprocessed information} *)
(*  ********************************************************************* *)

(** Useful information associated to a procedure *)
type procinfo = {
	kf : Cil_types.kernel_function;
  pname : string;        (** Procedure name *)
  pstart: point; (** Procedure start point *)
  pexit: point;  (** Procedure exit point *)
  pinput: Apron.Var.t array;  (** Array of input variables *)
  plocal: Apron.Var.t array;  (** Array of other variables *)
  penv: Apron.Environment.t;  (** Environment of the procedure *)
  avar2cvar: (Apron.Var.t,Cil_types.varinfo) Hashhe.t;
}

let dummy_procinfo =
	{
		kf = Kernel_function.dummy ();
		pname = "";
		pstart = vertex_dummy;
		pexit = vertex_dummy;
		pinput = [||];
		plocal = [||];
		penv = Apron.Environment.make [||] [||];
		avar2cvar = Hashhe.create 1;
	}
(** Useful information for the program *)
type info = {
  procinfo : (string, procinfo) Hashhe.t;
    (** Hashtable [procedure name -> procinfo].
	Main procedure has empty name *)
  callret : (point,point) DHashhe.t;
    (** Two-way association call points/return points generated by procedure
      calls. *)
  pointenv : (point,Apron.Environment.t) Hashhe.t;
    (** Hashtable [point -> environment of the enclosing procedure]. *)
  mutable counter : int;
    (** Last free hyperedge identifier (used by [add_equation]). *)
}

let dummy_info =
	{
		procinfo = Hashhe.create 0;
		callret = DHashhe.create 0;
		pointenv = Hashhe.create 0;
		counter = -1;
	}

(*  ********************************************************************* *)
(** {2 Equation system} *)
(*  ********************************************************************* *)

(** A variable in an equation = a control point *)
type var = point

(** Information associated to hyperedges/functions used in equations *)
type transfer =
	| Lcons of Apron.Tcons1.t * Apron.Lincons1.t * Cil_types.code_annotation * bool ref
		(**linear constraint. cond,cons and is all true?*)
	| Tcons of Apron.Tcons1.t * Apron.Tcons1.t * Cil_types.code_annotation * bool ref
  | Lassign of Apron.Var.t * Apron.Linexpr1.t
    (** Assignement by a linear expression *)
  | Tassign of Apron.Var.t * Apron.Texpr1.t
    (** Assignement by a tree expression *)
  | Condition of Apron.Tcons1.earray Boolexpr.t
    (** Filtering of a predicate by a Boolean expression *)
  | Calle of procinfo * procinfo * (Apron.Texpr1.t array) * (Apron.Texpr1.t array) option
    (** Procedure call, of the form
	  [Call(callerinfo,calleeinfo,actual input parameters,actual
	  output parameters)] *)
  | Return of procinfo * procinfo * (Apron.Texpr1.t array) * (Apron.Texpr1.t array)
    (** Procedure return, of the form
	  [Call(callerinfo,calleeinfo,actual input parameters,actual
	  output parameters)] *)

(** Equation system, represented by a graph, where vertex
    identifiers are control point, and hyperedge identifiers are
    integers, with which are associated objects of type
    [transfer]. Global information associated with the graph is of
    type [info]. *)
type graph = (vertex,hedge,unit,transfer,info) PSHGraph.t
  
(*  ********************************************************************* *)
(** {2 Functions} *)
(*  ********************************************************************* *)

(** Adding an equation *)
let add_equation (graph:graph) (torg:var array) (transfer:transfer) (dest:var):unit =
  Array.iter(fun var ->
      if not (PSHGraph.is_vertex graph var) then PSHGraph.add_vertex graph var ()
  )torg;
  if not (PSHGraph.is_vertex graph dest) then PSHGraph.add_vertex graph dest ();
  if transfer<>(Condition(Boolexpr.DISJ([]))) then begin
    let info = PSHGraph.info graph in
    PSHGraph.add_hedge graph info.counter transfer ~pred:torg ~succ:[|dest|];
    info.counter <- info.counter + 1;
  end;
  ()
 
(*  ===================================================================== *)
(** {3 Printing functions} *)
(*  ===================================================================== *)
      
let print_list
  ?(first=("[@[":(unit,Format.formatter,unit) format))
  ?(sep = (";@ ":(unit,Format.formatter,unit) format))
  ?(last = ("@]]":(unit,Format.formatter,unit) format))
  (print_elt: Format.formatter -> 'a -> unit)
  (fmt:Format.formatter)
  (list: 'a list)
  : unit
  =
  if list=[] then begin
    fprintf fmt first;
    fprintf fmt last;
  end
  else begin
    fprintf fmt first;
    let rec do_sep = function
      [e] -> print_elt fmt e
      | e::l -> (print_elt fmt e ; fprintf fmt sep; do_sep l)
      | [] -> failwith ""
    in
    do_sep list;
    fprintf fmt last;
  end
  
let print_tvar fmt (tvar:Apron.Var.t array) =
  print_list
    ~first:"[|@[<hov>" ~sep:";@ " ~last:"@]|]"
    Apron.Var.print
    fmt (Array.to_list tvar)

let print_texpr fmt (texpr:Apron.Texpr1.t array) =
	print_list
    ~first:"[|@[<hov>" ~sep:";@ " ~last:"@]|]"
    Apron.Texpr1.print
    fmt (Array.to_list texpr)

let print_procinfo fmt procinfo =
  fprintf fmt "{ @[<v>pstart = %a;@ pexit = %a;@ pinput = %a;@ plocal = %a;@ penv = %a;@] }"
  	print_point procinfo.pstart
  	print_point procinfo.pexit
    print_tvar procinfo.pinput
    print_tvar procinfo.plocal
    (fun fmt e -> Apron.Environment.print fmt e) procinfo.penv

let print_info fmt info =
  fprintf fmt "{ @[<v>procinfo = %a;@ callret = %a;@ pointenv = %a;@ counter = %i;@] }"
    (Hashhe.print pp_print_string print_procinfo) info.procinfo
    (DHashhe.print print_point print_point) info.callret
    (Hashhe.print print_point Apron.Environment.print) info.pointenv
    info.counter

let print_transfer fmt transfer = 
	match transfer with
	| Lcons(cond,cons1,code_annotation,sat)->
		Apron.Lincons1.print fmt cons1
	| Tcons(cond,tcons,code_annotation,sat)->
		Apron.Tcons1.print fmt tcons
  | Lassign _ -> failwith ""
  | Tassign(v,e) ->
    fprintf fmt "%a = %a"
    Apron.Var.print v
    Apron.Texpr1.print e
  | Condition(bexpr) ->
    fprintf fmt "IF %a"
    (Boolexpr.print (Apron.Tcons1.array_print ~first:"@[" ~sep:" &&@ " ~last:"@]")) bexpr
  | Calle(callerinfo,calleeinfo,pin,pout) ->
  	(match pout with
  	| Some(out)->
      fprintf fmt "CALL %a = %s(%a)"
      print_texpr out
      calleeinfo.pname
      print_texpr pin
    | None->
    	fprintf fmt "CALL %s(%a)"
      calleeinfo.pname
      print_texpr pin
    )
  | Return(callerinfo,calleeinfo,pin,pout) ->
  	if (Array.length pout)>0 then
      fprintf fmt "RETURN %a = %s(%a)"
      print_texpr pout
      calleeinfo.pname
      print_texpr pin
     else
      fprintf fmt "RETURN %s(%a)"
      calleeinfo.pname
      print_texpr pin
      
let print_unit fmt ()=
	fprintf fmt ""
	
let print_graph fmt graph =
	PSHGraph.print 
		print_point
		print_hedge
		print_unit 
		print_transfer 
		print_info 
		fmt
		graph
