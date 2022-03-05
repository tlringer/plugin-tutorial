(*
 * General utilities for collections in OCaml
 * From coq-plugin-lib, mostly
 *)

(*
 * [min, max)
 *)
let rec range (min : int) (max : int) : int list =
  if min < max then
    min :: range (min + 1) max
  else
    []
