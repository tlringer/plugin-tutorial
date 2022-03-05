(*
 * General utilities for collections in OCaml
 * From coq-plugin-lib, mostly
 *)

(*
 * min -> max -> [min, max)
 *)
val range : int -> int -> int list

(*
 * Split a list l into (l1, l2) where |l1| = n and |l2| = |l| - n
 *)
val take_split : int -> 'a list -> ('a list * 'a list)
