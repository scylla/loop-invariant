let prove_predicate (kf:Cil_types.kernel_function) (bhv:string list) ip wp_compute :int =
	try	
		wp_compute (Some(kf)) bhv (Some(ip));(*(Some(kf))*)
		let status = Property_status.Consolidation.get ip in
		(match status with
		| Property_status.Consolidation.Considered_valid|Property_status.Consolidation.Valid(_)|Property_status.Consolidation.Valid_under_hyp(_)|Property_status.Consolidation.Valid_but_dead(_)->
			Printf.printf "Valid\n";1;
		| Property_status.Consolidation.Unknown(_)->
			Printf.printf "Unkonwn\n";2;
		|_->
			Printf.printf "Invalid\n";0;
		);	
	with Stack_overflow|Exit->Printf.printf "Exit\n";0;
