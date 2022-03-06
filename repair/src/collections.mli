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

(*
 * Get the last element of a list
 *)
val last : 'a list -> 'a

(*
 * Get all but the last element of a list
 *)
val all_but_last : 'a list -> 'a list

(*
 * Add an element to the end of a list
 *)
val snoc : 'a -> 'a list -> 'a list
