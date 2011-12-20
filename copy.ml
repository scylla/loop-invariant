open Cil_types
open Cil_datatype
open Visitor

let copy_exp (e:Cil_types.exp) :Cil_types.exp =
	Cil.copy_exp e
	
let copy_IdPredicate (visitor:Visitor.frama_c_visitor) (p:Cil_types.identified_predicate) :Cil_types.identified_predicate =
	Visitor.visitFramacIdPredicate visitor p
(*	
let copy_predicate (visitor:Visitor.frama_c_visitor) (p:Cil_types.predicate) :Cil_types.predicate =
	Visitor.visitFramacPredicate visitor p
*)
let rec copy_label (label:Cil_types.label) :Cil_types.label =
	match label with
	| Label(s,l,b)->
		Label(s,l,b)
	| Case(exp,l)->
		Case((copy_exp exp),l)
	| Default(l)->
		Default(l)

let rec copy_stmt (stmt:Cil_types.stmt) :Cil_types.stmt =
	let nl = ref [] in
	List.iter(fun l->
		nl := !nl@[copy_label l];
	)stmt.labels;
	let nsuccs = ref [] in
	List.iter(fun s->
		nsuccs := !nsuccs@[copy_stmt s];
	)stmt.succs;
	let npreds = ref [] in
	List.iter(fun s->
		npreds := !npreds@[copy_stmt s];
	)stmt.preds;
	{
		labels = !nl;
		skind = stmt.skind;
		sid = stmt.sid;
		succs = !nsuccs;
		preds = !npreds;
		predicate_list = [];
		free_lv_list = [];
		ghost = stmt.ghost;
	}
	
let rec copy_logic_label (label:Cil_types.logic_label) :Cil_types.logic_label =
	match label with
	| StmtLabel(stmtr)->
		let nstmtr = ref (copy_stmt !stmtr) in
		StmtLabel(nstmtr)
	| LogicLabel(so,s)->
		LogicLabel(so,s)
		
let rec copy_varinfo (v:Cil_types.varinfo) :Cil_types.varinfo =
	Cil.copyVarinfo v v.vname
	(*let rec copy_logic_var (lv:Cil_types.logic_var) :Cil_types.logic_var =
		match lv.lv_origin with
		| Some(v)->
			{
				lv_name = lv.lv_name;
				lv_id = lv.lv_id;
				lv_type = lv.lv_type;
				lv_origin = Some(copy_varinfo v);
			}	
		| None->
			{
				lv_name = lv.lv_name;
				lv_id = lv.lv_id;
				lv_type = lv.lv_type;
				lv_origin = None;
			}
	in

	match v.vlogic_var_assoc with
	| Some(lv)->		
		{
			vname = v.vname;
			vorig_name = v.vorig_name;
			vtype = v.vtype;
			vattr = v.vattr;
			vstorage = v.vstorage;
			vglob = v.vglob;
			vdefined = v.vdefined;
			vformal = v.vformal;
			vinline = v.vinline;
			vdecl = v.vdecl;
			vid = v.vid;
			vaddrof = v.vaddrof;
			vreferenced = v.vreferenced;
			vgenerated = v.vgenerated;
			vdescr = v.vdescr;
			vdescrpure = v.vdescrpure;
			vghost = v.vghost;
			vlogic = v.vlogic;
			vlogic_var_assoc = Some(copy_logic_var lv);
		}
	| None->
		{
			vname = v.vname;
			vorig_name = v.vorig_name;
			vtype = v.vtype;
			vattr = v.vattr;
			vstorage = v.vstorage;
			vglob = v.vglob;
			vdefined = v.vdefined;
			vformal = v.vformal;
			vinline = v.vinline;
			vdecl = v.vdecl;
			vid = v.vid;
			vaddrof = v.vaddrof;
			vreferenced = v.vreferenced;
			vgenerated = v.vgenerated;
			vdescr = v.vdescr;
			vdescrpure = v.vdescrpure;
			vghost = v.vghost;
			vlogic = v.vlogic;
			vlogic_var_assoc = None;
		}*)

let rec copy_logic_var (lv:Cil_types.logic_var) :Cil_types.logic_var =
	match lv.lv_origin with
	| Some(v)->
		{
			lv_name = lv.lv_name;
			lv_id = lv.lv_id;
			lv_type = lv.lv_type;
			lv_origin = Some(copy_varinfo v);
		}	
	| None->
		{
			lv_name = lv.lv_name;
			lv_id = lv.lv_id;
			lv_type = lv.lv_type;
			lv_origin = None;
		}

let rec copy_term (t:Cil_types.term) :Cil_types.term =
	let copy_identified_term (it:Cil_types.identified_term) :Cil_types.identified_term =
		{it_id=it.it_id;it_content=copy_term it.it_content;}
	in
	
	let copy_term_option (t:Cil_types.term option) :Cil_types.term option=
		match t with
		| Some(t1)->Some(copy_term t1)
		| None->None
	in
		
	let rec copy_predicate (p:Cil_types.predicate) :Cil_types.predicate =
		match p with
		| Psubtype(t1,t2)->
			Psubtype((copy_term t1),(copy_term t2))
		| Pvalid_index(t1,t2)->
			Pvalid_index((copy_term t1),(copy_term t2))
		|Prel(rel,t1,t2)->
			Prel(rel,(copy_term t1),(copy_term t2))
		| Pfresh(t1)->
			Pfresh(copy_term t1)
		|Pvalid(t1)->
			Pvalid(copy_term t1)
		| Pvalid_range(t1,t2,t3)->
			Pvalid_range((copy_term t1),(copy_term t2),(copy_term t3))
		| Pat(pn,label)->
			let npn = 
			{name=pn.name;
			loc=pn.loc;
			content=(copy_predicate pn.content);
			} in
			Pat(npn,label)
		| Pexists(qua,pn)->
			let npn = 
			{name=pn.name;
			loc=pn.loc;
			content=copy_predicate pn.content;
			} in
			Pexists(qua,npn)
		| Pforall(qua,pn)->
			let npn = 
			{name=pn.name;
			loc=pn.loc;
			content=copy_predicate pn.content;
			} in
			Pforall(qua,npn)
		| Plet(linfo,pn)->
			let npn = 
			{name=pn.name;
			loc=pn.loc;
			content=copy_predicate pn.content;
			} in
			Plet((Cil_datatype.Logic_info.copy linfo),npn)
		| Pnot(pn)->
			let npn = 
			{name=pn.name;
			loc=pn.loc;
			content=copy_predicate pn.content;
			} in
			Pnot(npn)
		| Papp(linfo,labell,tl)->
			let nlabell = ref [] in
			List.iter(fun (l1,l2)->
				nlabell := !nlabell@[((copy_logic_label l1),(copy_logic_label l2))];
			)labell;
			let ntl = ref [] in
			List.iter(fun t->
				ntl := !ntl@[copy_term t];
			)tl;
			Papp((Cil_datatype.Logic_info.copy linfo),!nlabell,!ntl)
		| Pseparated(tl)->
			let ntl = ref [] in
			List.iter(fun t->
				ntl := !ntl@[copy_term t];
			)tl;
			Pseparated(!ntl)
		| Pand(pn1,pn2)->
			let npn1 = 
			{name=pn1.name;
			loc=pn1.loc;
			content=copy_predicate pn1.content;
			} in
			let npn2 = 
			{name=pn2.name;
			loc=pn2.loc;
			content=copy_predicate pn2.content;
			} in
			Pand(npn1,npn2)
		| Por(pn1,pn2)->
			let npn1 = 
			{name=pn1.name;
			loc=pn1.loc;
			content=copy_predicate pn1.content;
			} in
			let npn2 = 
			{name=pn2.name;
			loc=pn2.loc;
			content=copy_predicate pn2.content;
			} in
			Por(npn1,npn2)
		| Pxor(pn1,pn2)->
			let npn1 = 
			{name=pn1.name;
			loc=pn1.loc;
			content=copy_predicate pn1.content;
			} in
			let npn2 = 
			{name=pn2.name;
			loc=pn2.loc;
			content=copy_predicate pn2.content;
			} in
			Pxor(npn1,npn2)
		| Pimplies(pn1,pn2)->
			let npn1 = 
			{name=pn1.name;
			loc=pn1.loc;
			content=copy_predicate pn1.content;
			} in
			let npn2 = 
			{name=pn2.name;
			loc=pn2.loc;
			content=copy_predicate pn2.content;
			} in
			Pimplies(npn1,npn2)
		| Piff(pn1,pn2)->
			let npn1 = 
			{name=pn1.name;
			loc=pn1.loc;
			content=copy_predicate pn1.content;
			} in
			let npn2 = 
			{name=pn2.name;
			loc=pn2.loc;
			content=copy_predicate pn2.content;
			} in
			Piff(npn1,npn2)
		| Pif(t,pn1,pn2)->
			let npn1 = 
			{name=pn1.name;
			loc=pn1.loc;
			content=copy_predicate pn1.content;
			} in
			let npn2 = 
			{name=pn2.name;
			loc=pn2.loc;
			content=copy_predicate pn2.content;
			} in
			Pif((copy_term t),npn1,npn2)
		| Pfalse->Pfalse
		| Ptrue->Ptrue
	in
			
	let rec copy_logic_info (linfo:Cil_types.logic_info) :Cil_types.logic_info =
		let copy_logic_body (body:Cil_types.logic_body) :Cil_types.logic_body =
			match body with
			| LBnone->
				LBnone
			| LBreads(itl)->
				let nitl = ref [] in
				List.iter(fun it->
					nitl := !nitl@[copy_identified_term it];
				)itl;
				LBreads(!nitl)
			| LBterm(t)->
				LBterm(copy_term t)
			| LBpred(pn)->
				LBpred({name=pn.name;loc=pn.loc;content=copy_predicate pn.content;})
			| LBinductive(l)->
				let nl = ref [] in
				List.iter(fun (s,llabell,sl,pn)->
					let nllabell = ref [] in
					let nsl = ref [] in
					List.iter(fun llabel->
						nllabell := !nllabell@[copy_logic_label llabel];
					)llabell;
					List.iter(fun s->
						nsl := !nsl@[s];
					)sl;
					nl := !nl@[(s,!nllabell,!nsl,{name=pn.name;loc=pn.loc;content=copy_predicate pn.content;})];
				)l;
				LBinductive(!nl)
			in
		let nllabell = ref [] in
		List.iter(fun llabel->
			nllabell := !nllabell@[copy_logic_label llabel];
		)linfo.l_labels;
		let nprofilel = ref [] in
		List.iter(fun lv->
			nprofilel := !nprofilel@[copy_logic_var lv];
		)linfo.l_profile;
		{
			l_var_info = copy_logic_var linfo.l_var_info;
			l_labels = !nllabell;
			l_tparams = linfo.l_tparams;
			l_type = linfo.l_type;
			l_profile = !nprofilel;
			l_body = copy_logic_body linfo.l_body;
		}
	in
	
	let rec copy_term_offset (offset:Cil_types.term_offset) :Cil_types.term_offset =
		match offset with
		| TNoOffset->
			TNoOffset
		| TField(fi,toff)->
			TField(fi,(copy_term_offset toff))
		| TIndex(t1,toff)->
			TIndex((copy_term t1),(copy_term_offset toff))
	in
		
	let rec copy_term_lhost (thost:Cil_types.term_lhost) :Cil_types.term_lhost =
		match thost with
		| TVar(lv)->
			TVar(copy_logic_var lv)
		| TResult(tp)->
			TResult(tp)
		| TMem(t1)->
			TMem(copy_term(t1))
	in
			
	let rec copy_term_node (tnode:Cil_types.term_node) :Cil_types.term_node =
		let rec copy_term_lval (tl:Cil_types.term_lval) :Cil_types.term_lval =
			let (host,off) = tl in
			((copy_term_lhost host),(copy_term_offset off))
		in
		match tnode with
		| TConst(con)->
			TConst(con)
		| TLval(tl)->
			TLval(copy_term_lval tl)
		| TSizeOf(typ)->
			TSizeOf(typ)
		| TSizeOfE(t)->
			TSizeOfE(copy_term t)
		| TAlignOf(typ)->
			TAlignOf(typ)
		| TAlignOfE(t)->
			TAlignOfE(copy_term t)
		| TUnOp(op,t)->
			TUnOp(op,(copy_term t))
		| TBinOp(op,t1,t2)->
			TBinOp(op,(copy_term t1),(copy_term t2))
		| TCastE(typ,t)->
			TCastE(typ,(copy_term t))
		| TAddrOf(tl)->
			TAddrOf((copy_term_lval tl))
		| TStartOf(tl)->
			TStartOf((copy_term_lval tl))
		| Tapp(linfo,llabell,tl)->
			let nllabell = ref [] in
			let ntl = ref [] in
			List.iter(fun (l1,l2)->
				nllabell := !nllabell@[((copy_logic_label l1),(copy_logic_label l2))];
			)llabell;
			List.iter(fun t->
				ntl := !ntl@[copy_term t];
			)tl;
			Tapp((copy_logic_info linfo),!nllabell,!ntl)
		| Tlambda(qua,t)->
			Tlambda(qua,(copy_term t))
		| TDataCons(lctor,tl)->
			let ntl = ref [] in
			List.iter(fun t->
				ntl := !ntl@[copy_term t];
			)tl;
			TDataCons(lctor,!ntl)
		| Tif(t1,t2,t3)->
			Tif((copy_term t1),(copy_term t2),(copy_term t3))
		| Tat(t,llabel)->
			Tat((copy_term t),(copy_logic_label llabel))
		| Tbase_addr(t)->
			Tbase_addr(copy_term t)
		| Tblock_length(t)->
			Tblock_length(copy_term t)
		| Tnull->Tnull
		| TCoerce(t,typ)->
			TCoerce((copy_term t),typ)
		| TCoerceE(t1,t2)->
			TCoerceE((copy_term t1),(copy_term t2))
		| TUpdate(t1,toff,t2)->
			TUpdate((copy_term t1),(copy_term_offset toff),(copy_term t2))
		| Ttypeof(t)->
			Ttypeof(copy_term t)
		| Ttype(typ)->Ttype(typ)
		| Tempty_set->Tempty_set
		| Tunion(tl)->
			let ntl = ref [] in
			List.iter(fun t->
				ntl := !ntl@[(copy_term t)];
			)tl;
			Tunion(!ntl)
		| Tinter(tl)->
			let ntl = ref [] in
			List.iter(fun t->
				ntl := !ntl@[(copy_term t)];
			)tl;
			Tinter(!ntl)
		| Tcomprehension(t,qua,pno)->
			(match pno with
			| Some(pn)->
				Tcomprehension((copy_term t),qua,Some {name=pn.name;loc=pn.loc;content=copy_predicate pn.content;})
			| None->
				Tcomprehension((copy_term t),qua,None)
			)
		| Trange(to1,to2)->
			Trange((copy_term_option to1),(copy_term_option to2))
		| Tlet(linfo,t)->
			Tlet((copy_logic_info linfo),(copy_term t))
	in
	{
		term_node = copy_term_node t.term_node;
		term_loc = t.term_loc;
		term_type = t.term_type;
		term_name = t.term_name;
	}
	
let rec copy_predicate (p:Cil_types.predicate) :Cil_types.predicate =
	match p with
	| Psubtype(t1,t2)->
		Psubtype((copy_term t1),(copy_term t2))
	| Pvalid_index(t1,t2)->
		Pvalid_index((copy_term t1),(copy_term t2))
	|Prel(rel,t1,t2)->
		Prel(rel,(copy_term t1),(copy_term t2))
	| Pfresh(t1)->
		Pfresh(copy_term t1)
	|Pvalid(t1)->
		Pvalid(copy_term t1)
	| Pvalid_range(t1,t2,t3)->
		Pvalid_range((copy_term t1),(copy_term t2),(copy_term t3))
	| Pinitialized(t)->
		Pinitialized(copy_term t)
	| Pat(pn,label)->
		let npn = 
		{name=pn.name;
		loc=pn.loc;
		content=copy_predicate pn.content;
		} in
		Pat(npn,label)
	| Pexists(qua,pn)->
		let npn = 
		{name=pn.name;
		loc=pn.loc;
		content=copy_predicate pn.content;
		} in
		Pexists(qua,npn)
	| Pforall(qua,pn)->
		let npn = 
		{name=pn.name;
		loc=pn.loc;
		content=copy_predicate pn.content;
		} in
		Pforall(qua,npn)
	| Plet(linfo,pn)->
		let npn = 
		{name=pn.name;
		loc=pn.loc;
		content=copy_predicate pn.content;
		} in
		Plet((Cil_datatype.Logic_info.copy linfo),npn)
	| Pnot(pn)->
		let npn = 
		{name=pn.name;
		loc=pn.loc;
		content=copy_predicate pn.content;
		} in
		Pnot(npn)
	| Papp(linfo,labell,tl)->
		let nlabell = ref [] in
		List.iter(fun (l1,l2)->
			nlabell := !nlabell@[((copy_logic_label l1),(copy_logic_label l2))];
		)labell;
		let ntl = ref [] in
		List.iter(fun t->
			ntl := !ntl@[copy_term t];
		)tl;
		Papp((Cil_datatype.Logic_info.copy linfo),!nlabell,!ntl)
	| Pseparated(tl)->
		let ntl = ref [] in
		List.iter(fun t->
			ntl := !ntl@[copy_term t];
		)tl;
		Pseparated(!ntl)
	| Pand(pn1,pn2)->
		let npn1 = 
		{name=pn1.name;
		loc=pn1.loc;
		content=copy_predicate pn1.content;
		} in
		let npn2 = 
		{name=pn2.name;
		loc=pn2.loc;
		content=copy_predicate pn2.content;
		} in
		Pand(npn1,npn2)
	| Por(pn1,pn2)->
		let npn1 = 
		{name=pn1.name;
		loc=pn1.loc;
		content=copy_predicate pn1.content;
		} in
		let npn2 = 
		{name=pn2.name;
		loc=pn2.loc;
		content=copy_predicate pn2.content;
		} in
		Por(npn1,npn2)
	| Pxor(pn1,pn2)->
		let npn1 = 
		{name=pn1.name;
		loc=pn1.loc;
		content=copy_predicate pn1.content;
		} in
		let npn2 = 
		{name=pn2.name;
		loc=pn2.loc;
		content=copy_predicate pn2.content;
		} in
		Pxor(npn1,npn2)
	| Pimplies(pn1,pn2)->
		let npn1 = 
		{name=pn1.name;
		loc=pn1.loc;
		content=copy_predicate pn1.content;
		} in
		let npn2 = 
		{name=pn2.name;
		loc=pn2.loc;
		content=copy_predicate pn2.content;
		} in
		Pimplies(npn1,npn2)
	| Piff(pn1,pn2)->
		let npn1 = 
		{name=pn1.name;
		loc=pn1.loc;
		content=copy_predicate pn1.content;
		} in
		let npn2 = 
		{name=pn2.name;
		loc=pn2.loc;
		content=copy_predicate pn2.content;
		} in
		Piff(npn1,npn2)
	| Pif(t,pn1,pn2)->
		let npn1 = 
		{name=pn1.name;
		loc=pn1.loc;
		content=copy_predicate pn1.content;
		} in
		let npn2 = 
		{name=pn2.name;
		loc=pn2.loc;
		content=copy_predicate pn2.content;
		} in
		Pif((copy_term t),npn1,npn2)
	| Pfalse->Pfalse
	| Ptrue->Ptrue
