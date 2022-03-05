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

(*
 * Split a list l into (l1, l2) where |l1| = n and |l2| = |l| - n
 *)
let rec take_split (i : int) (l : 'a list) : ('a list * 'a list) =
  if i = 0 then
    ([], l)
  else
    match l with
    | [] ->
       ([], [])
    | h :: tl ->
       let (before, after) = take_split (i - 1) tl in
       (h :: before, after)
