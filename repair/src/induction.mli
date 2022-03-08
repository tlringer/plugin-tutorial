open Evd
open Stateutils
open Environ

(*
 * A file full of useful functions for reasoning about inductive types
 * and inductive proofs inside of Coq.
 *)

(* --- Inductive Proofs --- *)

(*
 * A nice useful representation of an inductive proof
 *)
type inductive_proof =
  {
    ip : EConstr.t; (* induction principle *)
    pms : EConstr.t list; (* polymorphic type parameters *)
    p : EConstr.t; (* inductive motive P *)
    cases : EConstr.t list; (* cases of the inductive proof *)
    final_args : EConstr.t list; (* any remaining arguments at the end *)
  }

(*
 * Convert a fully applied term to an inductive_proof
 *)
val of_application :
  env -> (* environment *)
  EConstr.t -> (* inductive proof as a fully applied term *)
  EConstr.t -> (* inductive type *)
  evar_map -> (* state *)
  inductive_proof state (* representation as inductive_proof *)

(*
 * Convert the body of an induction principle to an inductive proof
 * Return the proof, and the environment in which it can be interpreted
 *
 * For example, if we call of_ip on list_rect and list, since the type
 * of list_rect is:
 *
 *   forall (T : Type) (P : list T -> Type),
 *     P nil ->
 *     (forall (t : T) (l : list T), P l -> P (t :: l)) ->
 *     forall (l : list T), P l
 *
 * this pushes the following names and types to the environment:
 *
 *    T : Type
 *    P : list T -> Type
 *    pnil : P nil
 *    pcons : forall (t : T) (l : list T), P l -> P (t :: l)
 *    l : list T
 *
 * then returns:
 *
 *  {
 *    ip = list_rect;
 *    pms = [T];
 *    p = P;
 *    cases = [pnil; pcons];
 *    final_args = [l]
 *  }
 *)
val of_ip :
  env -> (* environment *)
  EConstr.t -> (* induction principle, as a term *)
  EConstr.t -> (* inductive type *)
  evar_map -> (* state *)
  (env * inductive_proof) state (* representation as env * inductive_proof *)

(* --- Constructors --- *)

(*
 * Map a function f on the constructors of inductive type ind.
 * Note that this does not handle mutually inductive types.
 *)
val map_constructors :
  (EConstr.t -> evar_map -> 'a state) -> (* f *)
  env -> (* environment *)
  EConstr.t -> (* ind *)
  evar_map -> (* state *)
  ('a list) state (* (map f (constructors ind)) *)

(*
 * Constructors in Coq are represented as a 1-indexed collection.
 * But 1-indexing is painful, so here I represent them as 0-indexed
 * collection.
 *
 * So, for example, for the inductive type list, I treat nil as
 * Constr(0, list T), and I treat cons as Constr(1, list T).
 * This gets back the 0-indexed index.
 *)
val index_of_constructor :
  EConstr.t -> (* term that represents a constructor *)
  evar_map -> (* state *)
  int (* index, starting at 0 *)
  
(* --- Induction Principles --- *)

(*
 * Get the induction principles from an inductive type ind
 * Return the empty list if ind is not an inductive type
 *)
val principles :
  env -> (* environment *)
  EConstr.t -> (* ind *)
  evar_map -> (* state *)
  (EConstr.t list) state (* list of induction principles *)
