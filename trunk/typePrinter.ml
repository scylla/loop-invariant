open Format 
open Cil_types
open Cil_datatype
		
let print_predicate_type fmt (p:Cil_types.predicate) =
	match p with
	| Psubtype(t1,t2)->
		fprintf fmt "Psubtype\n"
	| Pfresh(t)->
		fprintf fmt "Pfresh\n"
	| Pvalid_range(t1,t2,t3)->
		fprintf fmt "Pvalid_range\n"
	| Pvalid_index(t1,t2)->
		fprintf fmt "Pvalid_index\n"
	| Pvalid(t)->
		fprintf fmt "Pvalid\n"
	| Pat(pn1,label)->
		fprintf fmt "Pat\n"
	| Pexists(q,pn1)->
		fprintf fmt "Pexists\n"
	| Pforall(q,pn1)->
		fprintf fmt "Pforall\n"
	| Plet(linfo,pn1)->
		fprintf fmt "Plet\n"
	| Pfalse->
		fprintf fmt "Pfalse\n"
	| Ptrue->
		fprintf fmt "Ptrue\n"
	| Papp(linfo,l1,l2)->
		fprintf fmt "Papp\n"
	| Pseparated(tl)->
		fprintf fmt "Pseparated\n"
	| Prel(re,t1,t2)->
		fprintf fmt "Prel\n"
	| Pand(pn1,pn2)->
		fprintf fmt "Pand\n"
	| Por(pn1,pn2)->
		fprintf fmt "Por\n"
	| Pxor(pn1,pn2)->
		fprintf fmt "Pxor\n"
	| Pimplies(pn1,pn2)->
		fprintf fmt "Pimplies\n"
	| Piff(pn1,pn2)->
		fprintf fmt "Piff\n"
	| Pnot(pn1)->
		fprintf fmt "Pnot\n"
	| Pif(t,pn1,pn2)->
		fprintf fmt "Pif\n"
	| _->
		fprintf fmt "other\n"
		
let print_tnode_type fmt (tnode:Cil_types.term_node) =
	match tnode with		
	| TConst _->fprintf fmt "TConst\n"
	| TLval _->fprintf fmt "TLval\n"
	| TSizeOf _->fprintf fmt "TSizeOf\n"
	| TSizeOfE _->fprintf fmt "TSizeOfE\n"
	| TSizeOfStr _->fprintf fmt "TSizeofStr\n"
	| TAlignOf _->fprintf fmt "TAlignOf\n"
	| TAlignOfE _->fprintf fmt "TAlignOfE\n"
	| TUnOp _->fprintf fmt "TUnOp\n"
	| TBinOp _->fprintf fmt "TBinOp\n"
	| TCastE _->fprintf fmt "TCastE\n"
	| TAddrOf _->fprintf fmt "TAddrOf\n"
	| TStartOf _->fprintf fmt "TStartOf\n"
	| Tapp _->fprintf fmt "Tapp\n"
	| Tlambda _->fprintf fmt "Tlambda\n"
	| TDataCons _->fprintf fmt "TDataCons\n"
	| Tif _->fprintf fmt "Tif\n"
	| Tat _->fprintf fmt "Tat\n"
	| Tbase_addr _->fprintf fmt "Tbase_addr\n"
	| Tblock_length _->fprintf fmt "Tblock_length\n"
	| Tnull _->fprintf fmt "Tnull\n"
	| TCoerce _->fprintf fmt "TCoerce\n"
	| TCoerceE _->fprintf fmt "TCoerceE\n"
	| TUpdate _->fprintf fmt "TUpdate\n"
	| Ttypeof _->fprintf fmt "Ttypeof\n"
	| Ttype _->fprintf fmt "Ttype\n"
	| Tempty_set _->fprintf fmt "Tempty_set\n"
	| Tunion _->fprintf fmt "Tunion\n"
	| Tinter _->fprintf fmt "Tinter\n"
	| Tcomprehension _->fprintf fmt "Tcomprehension\n"
	| Trange _->fprintf fmt "Trange\n"
	| Tlet _->fprintf fmt "Tlet\n"
	
let print_exp_type fmt (e:Cil_types.exp) =
	match e.enode with
	| Const(_)->fprintf fmt "Const\n"
	| Lval(l)->fprintf fmt "Lval:";
		let (host,off) = l in
		(match host with
		| Var(v)->fprintf fmt "var:";
			Cil.d_type Format.std_formatter v.vtype;
		| Mem(_)->fprintf fmt "Mem:";
		);
		(match off with
		| NoOffset->fprintf fmt "NoOffset\n";
		| Field(_,_)->fprintf fmt "Field\n";
		| Index(_,_)->fprintf fmt "Index\n";
		)
	| SizeOf(_)->fprintf fmt "SizeOf\n"
	| SizeOfE(_)->fprintf fmt "SizeOfE\n"
	| SizeOfStr(_)->fprintf fmt "SizeOfStr\n"
	| AlignOf(_)->fprintf fmt "AlignOf\n"
	| AlignOfE(_)->fprintf fmt "AlignOfE\n"
	| UnOp(_,_,_)->fprintf fmt "UnOp\n"
	| BinOp(_,_,_,_)->fprintf fmt "BinOp\n"
	| CastE(_,_)->fprintf fmt "CastE\n"
	| AddrOf(_)->fprintf fmt "AddrOf\n"
	| StartOf(_)->fprintf fmt "StartOf\n"
	| Info(_,_)->fprintf fmt "Info\n"
		
let print_instrkind fmt (ins:Cil_types.instr) =
	match ins with
	| Set _->fprintf fmt "Set\n"
	| Call _->fprintf fmt "Call\n"
	| Asm _->fprintf fmt "Asm\n"
	| Skip _->fprintf fmt "Skip\n"
	| Code_annot _->fprintf fmt "Code_annot\n"
	
let print_stmtkind fmt (s:Cil_types.stmtkind) =
	match s with
	| Instr (ins)->
		fprintf fmt "Instr\n";
	| Return _->fprintf fmt "Return\n"
	| Goto _->fprintf fmt "Goto\n"
	| Break _->fprintf fmt "Break\n"
	| Continue _->fprintf fmt "Continue\n"
	| If _->fprintf fmt "If\n"
	| Switch _->fprintf fmt "Switch\n"
	| Loop _->fprintf fmt "Loop\n"
	| Block _->fprintf fmt "Block\n"
	| UnspecifiedSequence _->fprintf fmt "UnspecifiedSequence\n"
	| TryFinally _->fprintf fmt "TryFinally\n"
	| TryExcept _->fprintf fmt "TryExcept\n"
