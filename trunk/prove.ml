open Dynamic
open Datatype

let prove_predicate (kf:Db_types.kernel_function) bhv prop=
	Dynamic.get ~plugin:"Wp" "wp_compute" (kf bhv prop) ~journalize:false;
	(*Dynamic.get ~plugin:"Wp" "run" (f () ()) ~journalize:true;*)
	Printf.printf "in my prove\n"
