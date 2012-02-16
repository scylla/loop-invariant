
let prove_predicate (kf:Cil_types.kernel_function) (bhv:string list) ip wp_compute :int =
	(*let wp_run = Dynamic.get ~plugin:"Wp" "run" (Datatype.func Datatype.unit Datatype.unit) in
	wp_run ();1;
	
	Dynamic.Parameter.String.set "-wp-proof" "cvc3";*)(*alt-ergocvc3*)
	(*
	Dynamic.Parameter.Bool.on "-wp" ();
	Dynamic.Parameter.String.set "-wp-model" "Store";(*Runtime*)
	Dynamic.Parameter.Int.set "-wp-timeout" 15;
	Dynamic.Parameter.String.set "-wp-out" "/home/lzh/why-out";
	Dynamic.Parameter.Int.set "-wp-par" 1;*)
	try	
	wp_compute (Some(kf)) bhv (Some(ip));(*(Some(kf))*)
	(*let status = Property_status.Feedback.get ip in
	(match status with
	| Property_status.Feedback.Unknown->
		Printf.printf "Unknown\n";0;
	| Property_status.Feedback.Valid|Property_status.Feedback.Valid_under_hyp->
		Printf.printf "Valid\n";1;
	| _->1;
	);
	*)	
	let status = Property_status.Consolidation.get ip in
	(match status with
	| Property_status.Consolidation.Considered_valid|Property_status.Consolidation.Valid(_)|Property_status.Consolidation.Valid_under_hyp(_)|Property_status.Consolidation.Valid_but_dead(_)->
		Printf.printf "Valid?\n";1;
	| Property_status.Consolidation.Unknown(pend)->
		Printf.printf "Unkonwn\n";0;
	|_->
		Printf.printf "Invalid\n";0;
	);
	
	with Exit->Printf.printf "Exit\n";0;
	(*1;with Exit->0;
	let status = Property_status.get ip in
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
