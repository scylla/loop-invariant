open Cil_types
open Cil_datatype

(** Return an integer constant term from the given value. *)
let mk_int_term value =
  Logic_const.term
    (TConst( CInt64(Int64.of_int value,IInt,Some(string_of_int value))))
    (Ctype Cil.intType)

(** Return an integer constant term with the 0 value. *)
let zero_term() =
  mk_int_term 0

(** Returns a term representing the given logic variable (usually a fresh quantified variable). *)
let mk_term_from_logic_var lvar =
  Logic_const.term (TLval(TVar(lvar),TNoOffset)) (Ctype Cil.intType)

(** Returns a term representing the variable associated to the given varinfo *)
let mk_term_from_vi vi =
  Logic_const.term
    (TLval((Logic_utils.lval_to_term_lval ~cast:true (Cil.var vi))))
    (Ctype Cil.intType)
    
let removeAt (l:'a list) i = 
	let l1 = ref [] in
	for j=0 to (List.length l)-1 do
		if j<>i then
		(l1 := (List.nth l j)::!l1;)
	done;
	!l1
	
let swap l i j =
	let a = List.nth l i in
	let b = List.nth l j in 
	let nl = ref [] in
	for k=(List.length l)-1 to 0 do
		if k=i then (nl := b::!nl;) else
		if k=j then (nl := a::!nl;) else
		(nl := (List.nth l k)::!nl;)
	done;
	!nl
