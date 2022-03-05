open Evd
open Environ
open Stateutils
   
(*
 * Count the number of occurrences of terms equal to src in trm.
 * Make some simplifying assumptions about the format of trm
 * (no pattern matching, no fixpoints, no lets, and so on).
 *
 * I have done this one for you, to help you figure out how to implement sub.
 *)
val count :
  env -> (* environment *)
  EConstr.t -> (* src *)
  EConstr.t -> (* trm *)
  evar_map -> (* state *)
  int state (* stateful count *)

(*
 * Substitute all occurrences of terms equal to src in trm with dst.
 * Make some simplifying assumptions about the format of trm
 * (no pattern matching, no fixpoints, not lets, and so on).
 *)
val sub :
  env -> (* environment *)
  (EConstr.t * EConstr.t) -> (* src, dst *)
  EConstr.t -> (* trm *)
  evar_map -> (* state *)
  EConstr.t state (* stateful updated term *)
