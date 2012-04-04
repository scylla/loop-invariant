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
		sid = -1;
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
  var2coeff: (string,Apron.Coeff.t list ref) Hashtbl.t;(**varname to coeff*)
  avar2cvar: (Apron.Var.t,Cil_types.varinfo) Hashhe.t;
  has_def: bool;(*the fun is only declaration?*)
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
		var2coeff = Hashtbl.create 3;
		avar2cvar = Hashhe.create 1;
		has_def = false;
	}
(** Useful information for the program *)
type info = {
  procinfo : (string, procinfo) Hashtbl.t;
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
		procinfo = Hashtbl.create 0;
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
	| Tcons of Apron.Tcons1.t * Apron.Tcons1.t * Cil_types.code_annotation * bool ref
  | Assign of Apron.Var.t * LiType.arg
  | Condition of Apron.Tcons1.earray Boolexpr.t
    (** Filtering of a predicate by a Boolean expression *)
  | Calle of procinfo * procinfo * LiType.arg array * LiType.arg array option
    (** Procedure call, of the form
	  [Call(callerinfo,calleeinfo,actual input parameters,actual
	  output parameters)] *)
  | Return of procinfo * procinfo * LiType.arg array * LiType.arg array
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

let print_aptexpr fmt (texpr:Apron.Texpr1.expr array) =
	print_list
    ~first:"[|@[<hov>" ~sep:";@ " ~last:"@]|]"
    Apron.Texpr1.print_expr
    fmt (Array.to_list texpr)

let print_apvar fmt (var:Apron.Var.t array) =
	print_list
    ~first:"[|@[<hov>" ~sep:";@ " ~last:"@]|]"
    Apron.Var.print
    fmt (Array.to_list var)

let print_procinfo fmt procinfo =
  fprintf fmt "{ @[<v>pstart = %a;@ pexit = %a;@ pinput = %a;@ plocal = %a;@ penv = %a;@] }"
  	print_point procinfo.pstart
  	print_point procinfo.pexit
    print_tvar procinfo.pinput
    print_tvar procinfo.plocal
    (fun fmt e -> Apron.Environment.print fmt e) procinfo.penv

let print_info fmt info =
  fprintf fmt "{ @[<v>procinfo = ;@ callret = %a;@ pointenv = %a;@ counter = %i;@] }"(*%a
    (Hashtbl.print pp_print_string print_procinfo) info.procinfo*)
    (DHashhe.print print_point print_point) info.callret
    (Hashhe.print print_point Apron.Environment.print) info.pointenv
    info.counter


let print_transfer fmt transfer = 
	match transfer with
	| Lcons(_,cons1,_,_)->
		Printf.printf "Lcons:";Format.print_flush ();Apron.Lincons1.print fmt cons1
	| Tcons(_,tcons,_,_)->
		Printf.printf "Tcons:";Format.print_flush ();Apron.Tcons1.print fmt tcons
  | Assign(v,ass)->
    fprintf fmt "%a = %a"
    Apron.Var.print v
    LiType.print_arg ass
  | Condition(bexpr) ->
    fprintf fmt "IF %a"
    (Boolexpr.print (Apron.Tcons1.array_print ~first:"@[" ~sep:" &&@ " ~last:"@]")) bexpr
  | Calle(_,calleeinfo,pin,pout) ->
  	(match pout with
  	| Some(out)->
      fprintf fmt "CALL %s:" calleeinfo.pname;
      Array.iter(fun arg->
		    begin match arg with
				| LiType.APTexpr(dest)->
					Apron.Texpr1.print fmt dest;
		    | LiType.APLexpr(dest)->
			    Apron.Linexpr1.print fmt dest
			  | LiType.APVar(dest)->
			  	Apron.Var.print fmt dest
			  | LiType.APScalar(dest)->
			  	Apron.Scalar.print fmt dest
			  end;
	   	)out;
	   	Array.iter(fun arg->
      begin match arg with
				| LiType.APTexpr(source)->
					Apron.Texpr1.print fmt source;
		    | LiType.APLexpr(source)->
			    Apron.Linexpr1.print fmt source
			  | LiType.APVar(source)->
			  	Apron.Var.print fmt source
			  | LiType.APScalar(source)->
			  	Apron.Scalar.print fmt source
	    end;
	    )pin;
    | None->
    	fprintf fmt "CALL %s:" calleeinfo.pname;
      Array.iter(fun arg->
     		begin match arg with
				| LiType.APTexpr(source)->
					Apron.Texpr1.print fmt source;
		    | LiType.APLexpr(source)->
			    Apron.Linexpr1.print fmt source
			  | LiType.APVar(source)->
			  	Apron.Var.print fmt source
			  | LiType.APScalar(s)->
			  	Apron.Scalar.print fmt s
	    	end;
	  	)pin;
    )
  | Return(_,calleeinfo,pin,pout) ->
  	let length =
  		Array.length pout
  	in
  	if length>0 then
    begin  
    	fprintf fmt "RETURN %s:" calleeinfo.pname;
      Array.iter(fun arg->
		    begin match arg with
				| LiType.APTexpr(dest)->
					Apron.Texpr1.print fmt dest;
		    | LiType.APLexpr(dest)->
			    Apron.Linexpr1.print fmt dest
			  | LiType.APVar(dest)->
			  	Apron.Var.print fmt dest
			  | LiType.APScalar(s)->
			  	Apron.Scalar.print fmt s
			  end;
	   	)pout;
      Array.iter(fun arg->
     		begin match arg with
				| LiType.APTexpr(source)->
					Apron.Texpr1.print fmt source;
		    | LiType.APLexpr(source)->
			    Apron.Linexpr1.print fmt source
			  | LiType.APVar(source)->
			  	Apron.Var.print fmt source
			  | LiType.APScalar(s)->
			  	Apron.Scalar.print fmt s
	    	end;
	  	)pin;
		end
		else
    begin
      fprintf fmt "RETURN %s:" calleeinfo.pname;
      Array.iter(fun arg->
     		begin match arg with
				| LiType.APTexpr(source)->
					Apron.Texpr1.print fmt source;
		    | LiType.APLexpr(source)->
			    Apron.Linexpr1.print fmt source
			  | LiType.APVar(source)->
			  	Apron.Var.print fmt source
			  | LiType.APScalar(s)->
			  	Apron.Scalar.print fmt s
	    	end;
	  	)pin;
    end
      
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
