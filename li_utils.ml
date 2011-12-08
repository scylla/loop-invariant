open Cil_types
open Cil_datatype

let print_predicate_named_type (pn:Cil_types.predicate named)=
	match pn.content with
	| Psubtype(t1,t2)->
		Printf.printf "Psubtype\n"
	| Pfresh(t)->
		Printf.printf "Pfresh\n"
	| Pvalid_range(t1,t2,t3)->
		Printf.printf "Pvalid_range\n"
	| Pvalid_index(t1,t2)->
		Printf.printf "Pvalid_index\n"
	| Pvalid(t)->
		Printf.printf "Pvalid\n"
	| Pat(pn1,label)->
		Printf.printf "Pat\n"
	| Pexists(q,pn1)->
		Printf.printf "Pexists\n"
	| Pforall(q,pn1)->
		Printf.printf "Pforall\n"
	| Plet(linfo,pn1)->
		Printf.printf "Plet\n"
	| Pfalse->
		Printf.printf "Pfalse\n"
	| Ptrue->
		Printf.printf "Ptrue\n"
	| Papp(linfo,l1,l2)->
		Printf.printf "Papp\n"
	| Pseparated(tl)->
		Printf.printf "Pseparated\n"
	| Prel(re,t1,t2)->
		Printf.printf "Prel\n"
	| Pand(pn1,pn2)->
		Printf.printf "Pand\n"
	| Por(pn1,pn2)->
		Printf.printf "Por\n"
	| Pxor(pn1,pn2)->
		Printf.printf "Pxor\n"
	| Pimplies(pn1,pn2)->
		Printf.printf "Pimplies\n"
	| Piff(pn1,pn2)->
		Printf.printf "Piff\n"
	| Pnot(pn1)->
		Printf.printf "Pnot\n"
	| Pif(t,pn1,pn2)->
		Printf.printf "Pif\n"
	| _->
		Printf.printf "other\n"
		  		
      			
let print_exp_type (e:Cil_types.exp) =
	match e.enode with
	| Const(_)->Printf.printf "Const\n"
	| Lval(l)->Printf.printf "Lval:";
		let (host,off) = l in
		(match host with
		| Var(v)->Printf.printf "var:";
			Cil.d_type Format.std_formatter v.vtype; Printf.printf "TFun:\n";
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
	
let rec get_stmt_location (s:Cil_types.stmt) :Cil_types.location = 
	match s.skind with
	| Instr(instr)->
		(match instr with
		| Set(_,_,l)|Call(_,_,_,l)|Asm(_,_,_,_,_,l)|Skip(l)|Code_annot(_,l)->l;
		);
	| Return(_,l)|Goto(_,l)|Break(l)|Continue(l)|If(_,_,_,l)|Switch(_,_,_,l)|Loop(_,_,l,_,_)|TryFinally(_,_,l)|TryExcept(_,_,_,l)->l;
	| Block(block)->
		let first_stmt = List.nth block.bstmts 0 in
		get_stmt_location first_stmt;
	| UnspecifiedSequence(seq)->
		let block = Cil.block_from_unspecified_sequence seq in
		let first_stmt = List.nth block.bstmts 0 in
		get_stmt_location first_stmt;
