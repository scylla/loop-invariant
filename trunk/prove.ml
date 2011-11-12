open Dynamic
open Type
open Datatype
open Cil_types
open Cil_datatype

let prove_predicate (kf:Cil_types.kernel_function) (bhv:string list) ip=
	(*let wp_run = Dynamic.get ~plugin:"Wp" "run" (Datatype.func Datatype.unit Datatype.unit) in
	wp_run ();*)
	
	Dynamic.Parameter.String.set "-wp-proof" "cvc3";(*alt-ergocvc3*)
	Dynamic.Parameter.String.set "-wp-model" "Runtime";(*Store*)
	Dynamic.Parameter.Int.set "-wp-timeout" 100;
	Dynamic.Parameter.Int.set "-wp-par" 1;
	let module OLS = Datatype.List(Datatype.String) in(*Datatype.Option*)
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
