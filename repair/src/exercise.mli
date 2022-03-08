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
 * Map each old induction principle to an induction principle over the
 * new inductive type, but with arguments in the same order as the old
 * induction principle. (There are multiple induction principles per
 * inductive type as a sort of technicality of how Coq works, but this
 * is not really important for this exercise---it's just why there is a list
 * instead of a single term.)
 *
 * For example, if the input maps:
 *   list T -> New.list T
 * this takes the induction principle:
 *   list_rect :
 *     forall (T : Type) (P : list T -> Type),
 *       P (nil T) ->
 *       (forall (t : T) (l : list T), P l -> P (cons T t l)) ->
 *       forall (l : list T), P l.
 * to the induction principle:
 *   new_list_rect :
 *     forall (T : Type) (P : New.list T -> Type),
 *       P (New.nil T) ->
 *       (forall (t : T) (l : New.list T), P l -> P (New.cons T t l)) ->
 *       forall (l : New.list T), P l.
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
