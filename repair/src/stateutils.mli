open Evd

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
