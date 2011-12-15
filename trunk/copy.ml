open Cil_types
open Cil_datatype
open Visitor

let copy_exp (e:Cil_types.exp) :Cil_types.exp =
	Cil.copy_exp e
	
let copy_IdPredicate (visitor:Visitor.frama_c_visitor) (p:Cil_types.identified_predicate) :Cil_types.identified_predicate =
	Visitor.visitFramacIdPredicate visitor p
(*let copy_label (label:Cil_types.label) :Cil_types.label =
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
	
let copy_logic_label (label:Cil_types.logic_label) :Cil_types.logic_label =
	match label with
	| StmtLabel(stmtr)->
		let nstmtr = ref (copy_stmt !stmtr) in
		StmtLabel(nstmtr)
	| LogicLabel(so,s)->
		LogicLabel(so,s)
		
let rec copy_varinfo (v:Cil_types.varinfo) :Cil_types.varinfo =
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
		}

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

let rec copy_term_offset (offset:Cil_types.term_offset) :Cil_types.term_offset =
	match offset with
	| TNoOffset->
		TNoOffset
	| TField(fi,toff)->
		TField(fi,(copy_term_offset toff))
	| TIndex(t,toff)->
		TIndex((copy_term t),(copy_term_offset toff))
		
let copy_term_lhost (thost:Cil_types.term_lhost) :Cil_types.term_lhost =
	match thost with
	| TVar(lv)->
		TVar(copy_logic_var lv)
	| TResult(tp)->
		TResult(tp)
	| TMem(t)->
		TMem(copy_term(t))
		
let copy_term_lval (tl:Cil_types.term_lval) :Cil_types.term_lval =
	let (host,offset) = tl in
	((copy_term_host host),(copy_term_offset offset))
	
let rec copy_term_node (tnode:Cil_types.term_node) :Cil_types.term_node =
	tnode
	
let rec copy_term (t:Cil_types.term) :Cil_types.term =
	t

		
let rec copy_predicate (p:Cil_types.predicate) :Cil_types.predicate =
	match p with
	| Psubtype(t1,t2)->
		Psubtype((Cil_datatype.Term.copy t1),(Cil_datatype.Term.copy t2))
	| Pvalid_index(t1,t2)->
		Pvalid_index((Cil_datatype.Term.copy t1),(Cil_datatype.Term.copy t2))
	|Prel(rel,t1,t2)->
		Prel(rel,(Cil_datatype.Term.copy t1),(Cil_datatype.Term.copy t2))
	| Pfresh(t1)->
		Pfresh(Cil_datatype.Term.copy t1)
	|Pvalid(t1)->
		Pvalid(Cil_datatype.Term.copy t1)
	| Pvalid_range(t1,t2,t3)->
		Pvalid_range((Cil_datatype.Term.copy t1),(Cil_datatype.Term.copy t2),(Cil_datatype.Term.copy t3))
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
			nlabell := !nlabell@[((Cil_datatype.Logic_label.copy l1),(Cil_datatype.Logic_label.copy l2))];
		)labell;
		let ntl = ref [] in
		List.iter(fun t->
			ntl := !ntl@[Cil_datatype.Term.copy t];
		)tl;
		Papp((Cil_datatype.Logic_info.copy linfo),!nlabell,!ntl)
	| Pseparated(tl)->
		let ntl = ref [] in
		List.iter(fun t->
			ntl := !ntl@[Cil_datatype.Term.copy t];
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
		Pif((Cil_datatype.Term.copy t),npn1,npn2)
	| Pfalse->Pfalse
	| Ptrue->Ptrue
	*)
