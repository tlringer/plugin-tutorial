open Evd

(* --- State monad --- *)

(*
 * All terms in Coq have to carry around evar_maps (found in the Evd module),
 * which store a bunch of constraints about terms that help with things like
 * unification, type inference, and equality checking. This is annoying to
 * deal with, so I usually define some helper functions to make it easier.
 *
 * These come from https://github.com/uwplse/coq-plugin-lib in stateutils.ml,
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
 *)
let ret a = fun sigma -> sigma, a
let bind f1 f2 = (fun sigma -> let sigma, a = f1 sigma in f2 a sigma)

(* Like List.fold_left, but threading state *)
let fold_left_state f b l sigma =
  List.fold_left (fun (sigma, b) a -> f b a sigma) (sigma, b) l

(* List List.map, but threading state *)
let map_state f args =
  bind
    (fold_left_state
       (fun bs a sigma ->
         let sigma, b = f a sigma in
         sigma, b :: bs)
       []
       args)
    (fun fargs -> ret (List.rev fargs))

(* Like fold_left_state, but over arrays *)
let fold_left_state_array f b args =
  fold_left_state f b (Array.to_list args)

(* Like map_state, but over arrays *)
let map_state_array f args =
  bind
    (map_state f (Array.to_list args))
    (fun fargs -> ret (Array.of_list fargs))
