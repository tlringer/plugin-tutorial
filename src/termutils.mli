(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 *)

open Evd
open Environ
open Constrexpr

(* --- State monad --- *)

(*
 * All terms in Coq have to carry around evar_maps (found in the Evd module),
 * which store a bunch of constraints about terms that help with things like
 * unification, type inference, and equality checking. This is annoying to
 * deal with, so I usually define some helper functions to make it easier.
 *
 * These come from https://github.com/uwplse/coq-plugin-lib in stateutils.mli,
 * and the idea to use this design pattern comes from my grad school advisor
 * Dan Grossman.
 *
 * For any type 'a, a 'a state is a tuple of an evar_map and a 'a.
 * So basically, a 'a that carries around an evar_map.
 *)
type 'a state = evar_map * 'a

(*
 * These are monadic return and bind. Basically, they let you kind of pretend
 * you're not in the state monad (that is, pretend you're not carrying around
 * an evar_map with you everywhere). If you've ever used Haskell, it's common
 * to have syntax that makes this kind of thing look even nicer.
 *
 * Bind lets you chain calls with state:
 *)
val bind :
  (evar_map -> 'a state) -> (* f1 *)
  ('a -> evar_map -> 'b state) -> (* f2 *)
  evar_map -> (* state *)
  'b state (* stateful f1; f2 *)

(* Ret lets you forget the state in the final call: *)
val ret :
  'a -> (* a *)
  evar_map -> (* state *)
  'a state (* stateful a *)

(* Like List.fold_left, but threading state *)
val fold_left_state :
  ('b -> 'a -> evar_map -> 'b state) -> (* f *)
  'b -> (* b *)
  'a list -> (* l *)
  evar_map -> (* state *)
  'b state (* stateful (fold_left f b l) *)

(* List List.map, but threading state *)
val map_state :
  ('a -> evar_map -> 'b state) -> (* f *)
  'a list -> (* l *)
  evar_map -> (* state *)
  ('b list) state (* stateful (map f l) *)
  
(* Like fold_left_state, but over arrays *)
val fold_left_state_array :
  ('b -> 'a -> evar_map -> 'b state) -> (* f *)
  'b -> (* b *)
  'a array -> (* arr *)
  evar_map -> (* state *)
  'b state (* stateful (fold_left f b arr) *)

(* Like map_state, but over arrays *)
val map_state_array :
  ('a -> evar_map ->'b state) -> (* f *)
  'a array -> (* arr *)
  evar_map -> (* state *)
  ('b array) state (* stateful (map f arr) *)

(* --- Environments and definitions --- *)

(*
 * Environments in the Coq kernel map names to types. Here are a few
 * utility functions for environments.
 *)

(*
 * This gets the global environment the corresponding state:
 *)
val global_env : unit -> env state

(* Push a local binding to an environment *)
val push_local :
  Names.Name.t Context.binder_annot * EConstr.t -> (* name, type *)
  env -> (* environment *)
  env (* updated environment *)

(*
 * One of the coolest things about plugins is that you can use them
 * to define new terms. Here's a simplified (yes it looks terrifying,
 * but it really is simplified) function for defining new terms and storing them
 * in the global environment.
 *
 * This will only work if the term you produce
 * type checks in the end, so don't worry about accidentally proving False.
 * If you want to use the defined function later in your plugin, you
 * have to refresh the global environment by calling global_env () again,
 * but we don't need that in this plugin.
 *)
val define :
  Names.Id.t -> (* name of the new term *)
  EConstr.t -> (* the new term *)
  Evd.evar_map -> (* state *)
  unit

(*
 * When you first start using a plugin, if you want to manipulate terms
 * in an interesting way, you need to move from the external representation
 * of terms to the internal representation of terms. This does that for you.
 *)
val internalize :
  env -> (* environment *)
  constr_expr -> (* external representation *)
  evar_map -> (* state *)
  EConstr.t state (* stateful internal representation *)

(* --- Equality --- *)
  
(*
 * This checks if there is any set of internal constraints in the state
 * such that trm1 and trm2 are definitionally equal in the current environment.
 *)
val equal :
  env -> (* environment *)
  EConstr.t -> (* trm1 *)
  EConstr.t -> (* trm2 *)
  evar_map -> (* state *)
  bool state (* stateful (t1 = t2) *)

