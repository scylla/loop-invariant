open Cil_types

(*element accessed by plugin Value*)
type valEle =
	| Var of varinfo
	| Lval of lval
