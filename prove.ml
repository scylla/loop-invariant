open Dynamic
open Type
open Datatype
open Cil_types
open Cil_datatype

let prove_predicate (kf:Cil_types.kernel_function) (bhv:string list option) ip=
	(*let wp_run = Dynamic.get ~plugin:"Wp" "run" (Datatype.func Datatype.unit Datatype.unit) in
	wp_run ();*)
	
	Dynamic.Parameter.String.set "-wp-proof" "z3";
	Dynamic.Parameter.String.set "-wp-model" "Hoare";
	let module OLS = Datatype.Option(Datatype.List(Datatype.String)) in
	let module OKF = Datatype.Option(Kernel_function) in
	let module OP = Datatype.Option(Property) in
	let wp_compute = Dynamic.get ~plugin:"Wp" "wp_compute" (Datatype.func3 OKF.ty OLS.ty OP.ty Datatype.unit) in
	wp_compute (Some(kf)) bhv (Some(ip));
	Property_status.get ip
	(*(
	match prop with
	| Some(ip)->
		let status = Property_status.get ip in
		status;
	| None->Property_status.Never_tried;
	)*)
