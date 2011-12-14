open Cil_types
open Cil_datatype
open TypePrinter

let get_constant_str (c:Cil_types.constant) =
	match c with
  | CInt64(i, _, Some s)->Escape.escape_char (Char.chr (My_bigint.to_int i))
  | CStr(s) ->Escape.escape_string s
  | CWStr(sl) ->
  	let s = ref "" in
    List.iter(fun elt ->
    	s := !s^(Escape.escape_char (Char.chr (Int64.to_int elt)))
    )sl;
		!s
  | CChr(c) ->Escape.escape_char c
  | CReal(_, _, Some s) ->s
  | CReal(f, fsize, None) ->string_of_float f
  | CEnum (item) ->item.eiorig_name
   
let rec replace_logic_varname (t:Cil_types.term) (lv:Cil_types.logic_var) (exp:Cil_types.exp) =
	Printf.printf "replace now\n";
	let fmt = Format.std_formatter in
	Cil.d_exp fmt exp;Format.print_flush ();Printf.printf "\n";
	TypePrinter.print_exp_type fmt exp;
	match exp.enode with
	| Lval((host,offset))|AddrOf((host,offset))|StartOf((host,offset))->
		(match host with
		| Var(v)->
			Printf.printf "Var name replace:%s,%s\n" lv.lv_name v.vname;
			lv.lv_name <- v.vname;
		| Mem(e1)->
			Printf.printf "Mem in replace 1\n";
			replace_logic_varname t lv e1;
			Printf.printf "Mem in replace 2\n";
			(*(match offset with
			| Index(e,_)->replace_logic_varname p lv e;
			| _->();
			);*)
		)
	| CastE(_,e)|SizeOfE(e)|AlignOfE(e)|Info(e,_)->
		replace_logic_varname t lv e
	| Const(con)->
		Printf.printf "Const replace\n";
		t.term_node <- TConst(con)(*modify Cil_types.term.term_node to be mutable*)
		(*lv.lv_name <- (get_constant_str con)*)
	| UnOp(_,e1,_)->
		replace_logic_varname t lv e1
	| BinOp(_,e1,e2,_)->
		replace_logic_varname t lv e1;
		replace_logic_varname t lv e2
	| _->Printf.printf "other no replace\n"
	
let rec replace_term (t:Cil_types.term) (p:Cil_types.predicate) (formals:Cil_types.varinfo list) (args:Cil_types.exp list) =
	let fmt = Format.std_formatter in
	Cil.d_term fmt t;Format.print_flush ();Printf.printf "\n";
	TypePrinter.print_tnode_type fmt t.term_node;
	match t.term_node with
	| TLval((thost,toffset))|TAddrOf((thost,toffset))|TStartOf((thost,toffset))->
		(match thost with
		| TVar(lv)->
			let len = (List.length formals)-1 in
			for i=0 to len do
			(
				Printf.printf "formals_i=%s,lv_name=%s\n" ((List.nth formals i).vname) lv.lv_name;
				if ((List.nth formals i).vname)=lv.lv_name then
				(replace_logic_varname t lv (List.nth args i););
			);done
		| TMem(t1)->replace_term t1 p formals args;
		| TResult(_)->();
		);
	| TSizeOfE(t1)|TAlignOfE(t1)|TUnOp(_,t1)|TCastE(_,t1)|Tlambda(_,t1)|Tat(t1,_)|Tbase_addr(t1)|Tblock_length(t1)|TCoerce(t1,_)|Ttypeof(t1)|Tcomprehension(t1,_,_)|Tlet(_,t1)->
		Printf.printf "TCastE 1\n";
		replace_term t1 p formals args;
		let check_cons t0 t1 = 
			(match t1.term_node with
			| TConst(c)->
				t0.term_node <- t1.term_node
			| _->()
			);
		in
		check_cons t t1; 
		Printf.printf "TCastE 2\n"
	| TBinOp(_,t1,t2)|TUpdate(t1,_,t2)|TCoerceE(t1,t2)->
		replace_term t1 p formals args;
		replace_term t2 p formals args
	| Tapp(_,_,tl)|TDataCons(_,tl)|Tunion(tl)|Tinter(tl)->
		List.iter(fun t1->
			replace_term t1 p formals args;
		)tl
	| Tif(t1,t2,t3)->
		replace_term t1 p formals args;
		replace_term t2 p formals args;
		replace_term t3 p formals args
	| Trange(to1,to2)->
		(match to1 with
		| Some(t1)->
			replace_term t1 p formals args;
		| None->();
		);
		(match to2 with
		| Some(t1)->
			replace_term t1 p formals args;
		| None->();
		)
	| TConst(_)|TSizeOf(_)|TSizeOfStr(_)|TAlignOf(_)|Tnull|Ttype(_)|Tempty_set->()
		
let rec replace_predicate_var (p:Cil_types.predicate) (formals:Cil_types.varinfo list) (args:Cil_types.exp list) =
	let fmt = Format.std_formatter in
	TypePrinter.print_predicate_type fmt p;
	match p with
	| Psubtype(t1,t2)|Pvalid_index(t1,t2)|Prel(_,t1,t2)->
		replace_term t1 p formals args;
		replace_term t2 p formals args
	| Pfresh(t1)|Pvalid(t1)->
		replace_term t1 p formals args
	| Pvalid_range(t1,t2,t3)->
		replace_term t1 p formals args;
		replace_term t2 p formals args;
		replace_term t3 p formals args
	| Pat(pn,_)|Pexists(_,pn)|Pforall(_,pn)|Plet(_,pn)|Pnot(pn)->
		replace_predicate_var pn.content formals args
	| Papp(_,_,tl)|Pseparated(tl)->
		List.iter(fun t1->
			replace_term t1 p formals args;
		)tl
	| Pand(pn1,pn2)|Por(pn1,pn2)|Pxor(pn1,pn2)|Pimplies(pn1,pn2)|Piff(pn1,pn2)|Pif(_,pn1,pn2)->
		replace_predicate_var pn1.content formals args;
		replace_predicate_var pn2.content formals args
	| Pfalse|Ptrue->()
		  		
let get_exp_name (e:Cil_types.exp) =
	match e.enode with
	| Const(_)->Printf.printf "Const\n";assert false
	| Lval(l)->Printf.printf "Lval:";
		let (host,off) = l in
		(match host with
		| Var(v)->Printf.printf "var:";
			v.vname;
		| Mem(_)->Printf.printf "Mem:";assert false;
		);
	| SizeOf(_)->Printf.printf "SizeOf\n";assert false
	| SizeOfE(_)->Printf.printf "SizeOfE\n";assert false
	| SizeOfStr(_)->Printf.printf "SizeOfStr\n";assert false
	| AlignOf(_)->Printf.printf "AlignOf\n";assert false
	| AlignOfE(_)->Printf.printf "AlignOfE\n";assert false
	| UnOp(_,_,_)->Printf.printf "UnOp\n";assert false
	| BinOp(_,_,_,_)->Printf.printf "BinOp\n";assert false
	| CastE(_,_)->Printf.printf "CastE\n";assert false
	| AddrOf(_)->Printf.printf "AddrOf\n";assert false
	| StartOf(_)->Printf.printf "StartOf\n";assert false
	| Info(_,_)->Printf.printf "Info\n";assert false

	
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
		| Set(_,_,l)|Call(_,_,_,l)|Asm(_,_,_,_,_,l)|Skip(l)|Code_annot(_,l)->
			Printf.printf "Instr loc1\n";Cil.d_loc Format.std_formatter l;Format.print_flush ();Printf.printf "\nInstr loc2\n";l;
		);
	| Return(_,l)|Goto(_,l)|Break(l)|Continue(l)|If(_,_,_,l)|Switch(_,_,_,l)|Loop(_,_,l,_,_)|TryFinally(_,_,l)|TryExcept(_,_,_,l)->l;
	| Block(block)->
		let first_stmt = List.nth block.bstmts 0 in
		get_stmt_location first_stmt;
	| UnspecifiedSequence(seq)->
		let block = Cil.block_from_unspecified_sequence seq in
		let first_stmt = List.nth block.bstmts 0 in
		get_stmt_location first_stmt;;
		
let get_block_spoint (b:Cil_types.block) :Cil_types.location =
	if (List.length b.bstmts)>0 then
	(let first_stmt = List.nth b.bstmts 0 in
	TypePrinter.print_stmtkind Format.std_formatter first_stmt.skind;
	get_stmt_location first_stmt;
	)else (Lexing.dummy_pos,Lexing.dummy_pos);;

let get_block_epoint (b:Cil_types.block) :Cil_types.location =
	if (List.length b.bstmts)>0 then
	(let first_stmt = List.nth b.bstmts ((List.length b.bstmts)-1) in
	get_stmt_location first_stmt;
	)else (Lexing.dummy_pos,Lexing.dummy_pos);;
