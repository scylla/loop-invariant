open Dynamic
open Type
open Datatype
open Cil_types
open Cil_datatype

let prove_predicate (kf:Db_types.kernel_function) (bhv:string list option) prop=
	(*let wp_run = Dynamic.get ~plugin:"Wp" "run" (Datatype.func Datatype.unit Datatype.unit) in
	wp_run ();*)
	
	let module OLS = Datatype.Option(Datatype.List(Datatype.String)) in
	let module OKF = Datatype.Option(Kernel_function) in
	let module OP = Datatype.Option(Property) in
	let wp_compute = Dynamic.get ~plugin:"Wp" "wp_compute" (Datatype.func3 OKF.ty OLS.ty OP.ty Datatype.unit) in
	wp_compute (Some(kf)) bhv prop;
	(
	match prop with
	| Some(ip)->
		let result = Properties_status.get_all ~who:[] ip in
		result;
	| None->[];
	)
