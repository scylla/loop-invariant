open Apron
open Mpqf

let print_array = Abstract0.print_array;;

let manpk = Polka.manager_alloc_strict();;
let manbox = Box.manager_alloc ();;
let manoct = Oct.manager_alloc ();;
let manppl = Ppl.manager_alloc_strict();;
let mangrid = Ppl.manager_alloc_grid ();;
let maneq = Polka.manager_alloc_equalities ();;
let manpkgrid = PolkaGrid.manager_alloc manpk mangrid;;

let var_x = Var.of_string "x";;
let var_y = Var.of_string "y";;
let var_z = Var.of_string "z";;
let var_w = Var.of_string "w";;
let var_u = Var.of_string "u";;
let var_v = Var.of_string "v";;
let var_a = Var.of_string "a";;
let var_b = Var.of_string "b";;

let lincons1_array_print fmt x =
  Lincons1.array_print fmt x;;

let generator1_array_print fmt x =
  Generator1.array_print fmt x;;
