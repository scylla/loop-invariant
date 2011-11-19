open Cil_types
open Cil_datatype


let print_exp_type (e:Cil_types.exp) =
	match e.enode with
	| Const(_)->Printf.printf "Const\n"
	| Lval(l)->Printf.printf "Lval:";
		let (host,off) = l in
		(match host with
		| Var(v)->Printf.printf "var:";
		| Mem(_)->Printf.printf "Mem:";
		);
		(match off with
		| NoOffset->Printf.printf "NoOffset\n";
		| Field(_,_)->Printf.printf "Field\n";
		| Index(_,_)->Printf.printf "Index\n";
		)
	| SizeOf(_)->Printf.printf "SizeOf\n"
	| SizeOfE(_)->Printf.printf "SizeOfE\n"
	| SizeOfStr(_)->Printf.printf "SizeOfStr\n"
	| AlignOf(_)->Printf.printf "AlignOf\n"
	| AlignOfE(_)->Printf.printf "AlignOfE\n"
	| UnOp(_,_,_)->Printf.printf "UnOp\n"
	| BinOp(_,_,_,_)->Printf.printf "BinOp\n"
	| CastE(_,_)->Printf.printf "CastE\n"
	| AddrOf(_)->Printf.printf "AddrOf\n"
	| StartOf(_)->Printf.printf "StartOf\n"
	| Info(_,_)->Printf.printf "Info\n"
	
(** Return an integer constant term from the given value. *)
let mk_int_term value = Cil.lconstant (My_bigint.of_int value)

(** Return an integer constant term with the 0 value.
    @deprecated use directly Cil.lzero
*)
let zero_term() = Cil.lzero ()

let one_term () = Cil.lconstant My_bigint.one

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
	for j=0 to ((List.length l)-1) do
		if j<>i then
		(l1 := (List.nth l j)::!l1;);
	done;
	!l1;;
	
let swap (l:varinfo list) i j =
	let a = List.nth l i in
	let b = List.nth l j in 
	let nl = ref [] in
	for k=0 to ((List.length l)-1) do
		if k=i then (nl := b::!nl;) else
		if k=j then (nl := a::!nl;) else
		(nl := (List.nth l k)::!nl;)
	done;
	List.rev !nl;;
