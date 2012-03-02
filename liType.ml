open Cil_types

(*element accessed by plugin Value*)
type valEle =
	| Var of varinfo
	| Lval of lval

(*arguments type*)
type arg =
	| APTexpr of Apron.Texpr1.t
	| APVar of Apron.Var.t

let print_arg fmt arg =
	begin match arg with
	| APTexpr(exp)->
		Apron.Texpr1.print fmt exp;
	| APVar(v)->
		Apron.Var.print fmt v;
	end;
	Format.print_flush ()

type array_info =
	{
		v:varinfo;
		typ:typ;
		size:bitsSizeofTypCache;
	}
