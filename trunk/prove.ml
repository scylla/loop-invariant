
let prove_predicate (kf:Cil_types.kernel_function) (bhv:string list) ip=
	(*let wp_run = Dynamic.get ~plugin:"Wp" "run" (Datatype.func Datatype.unit Datatype.unit) in
	wp_run ();
	
	Dynamic.Parameter.String.set "-wp-proof" "cvc3";*)(*alt-ergocvc3*)
	try
	Dynamic.Parameter.String.set "-wp-model" "Store";(*Runtime*)
	Dynamic.Parameter.Int.set "-wp-timeout" 15;
	Dynamic.Parameter.String.set "-wp-out" "/home/lzh/Documents/why-out";
	Dynamic.Parameter.Int.set "-wp-par" 1;
	let module OLS = Datatype.List(Datatype.String) in(*Datatype.Option*)
	let module OKF = Datatype.Option(Kernel_function) in
	let module OP = Datatype.Option(Property) in
	let wp_compute = Dynamic.get ~plugin:"Wp" "wp_compute" (Datatype.func3 OKF.ty OLS.ty OP.ty Datatype.unit) in
	wp_compute (Some(kf)) bhv (Some(ip));
	let status = Property_status.Consolidation.get ip in
	(match status with
	| Property_status.Consolidation.Considered_valid|Property_status.Consolidation.Valid(_)|Property_status.Consolidation.Valid_under_hyp(_)|Property_status.Consolidation.Valid_but_dead(_)->
		Printf.printf "Valid?\n";1;
	|_->
		Printf.printf "Invalid\n";0;
	);
	with Exit->Printf.printf "Exit\n";0;
	(*let status = Property_status.get ip in
	match status with
	| Property_status.Never_tried->
		Printf.printf "result Never_tried\n";0;
	| Property_status.Best(e_status,erl)->
		Printf.printf "result Best\n";
		(match e_status with
		| True->
			Printf.printf "result True\n";1;
		| False_if_reachable->
			Printf.printf "result False_if_reachable\n";0;
		| False_and_reachable->
			Printf.printf "result False_and_reachable\n";0;
		| Dont_know->
			Printf.printf "result Dont_know\n";0;);
	| Inconsistent(inc)->
		Printf.printf "result InConsistent\n";0;
	with Exit->Printf.printf "Exit\n";0;*)
