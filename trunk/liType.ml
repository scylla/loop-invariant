open Cil_types

(*element accessed by plugin Value*)
type valEle =
	| Var of varinfo
	| Lval of lval

let print_valEle fmt ele =
	begin match ele with
	| Var(v)->
		Cil.d_var fmt v;
	| Lval(lv)->
		Cil.d_lval fmt lv;
	end;
	Format.print_flush ()

(*arguments type*)
type arg =
	| APTexpr of Apron.Texpr1.t
	| APLexpr of Apron.Linexpr1.t
	| APVar of Apron.Var.t
	| APScalar of Apron.Scalar.t(*const-->Scalar?*)

let print_arg fmt arg =
	begin match arg with
	| APTexpr(exp)->
		Apron.Texpr1.print fmt exp;
	| APLexpr(exp)->
		Apron.Linexpr1.print fmt exp;
	| APVar(v)->
		Apron.Var.print fmt v;
	| APScalar(s)->
		Apron.Scalar.print fmt s;
	end;
	Format.print_flush ()

type array_size =
	| CSize of Cil_types.bitsSizeofTypCache
	| CTerm of Cil_types.term

type array_info =
	{
		v:varinfo;
		typ:typ;
		size:array_size;
	}
