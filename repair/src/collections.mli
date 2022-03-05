(*
 * General utilities for collections in OCaml
 * From coq-plugin-lib, mostly
 *)

(*
 * min -> max -> [min, max)
 *)
val range : int -> int -> int list
