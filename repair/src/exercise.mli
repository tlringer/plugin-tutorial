open Evd
open Environ
open Stateutils

(*
 * Given a map function:
 *   map : forall ..., old_ind pms -> new_ind pms
 * return the inductive types old_ind and new_ind.
 *
 * For example, if the input is f from Demo.v, with:
 *   f : forall (T : Type), list T -> new_list T
 * This returns (list, new_list).
 *)
val inductives_from_map :
  env -> (* environment *)
  EConstr.t -> (* supplied map function f *)
  evar_map -> (* state *)
  (EConstr.t * EConstr.t) state (* (old_new, new_ind) *)
   
(*
 * Given an environment, a mapping function, and a state, return the
 * map of constructors between the old and new inductive type corresponding
 * to the supplied mapping function. For example, given f : list -> New.list
 * in Demo.v, this should return:
 *   [(nil, New.nil), (cons, New.cons)]
 *
 * This is mostly implemented for you---your job is to finish implementing
 * the swap_constructor function that this calls.
 *)
val get_constructor_map :
  env -> (* environment *)
  EConstr.t -> (* supplied map function f *)
  evar_map -> (* state *)
  ((EConstr.t * EConstr.t) list) state (* map from old to new constructors *)

(*
 * TODO explain etc
 *)
val get_induction_map :
  env -> (* environment *)
  EConstr.t -> (* supplied map function f *)
  evar_map -> (* state *)
  ((EConstr.t * EConstr.t) list) state (* map from old to new induction *)
  
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
