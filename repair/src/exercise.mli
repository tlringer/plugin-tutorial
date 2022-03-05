open Evd
open Environ
open Stateutils

(*
 * TODO explain etc
 *)
val get_swap_map :
  env -> (* environment *)
  EConstr.t -> (* supplied map function f : old_ind -> new_ind *)
  EConstr.t -> (* old_ind *)
  evar_map -> (* state *)
  ((EConstr.t * EConstr.t) list) state (* map from old to new constructors *)

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
  EConstr.t state (* updated term *)
