open EConstr
open Termutils
open Stateutils

(* TODO move, explain, clean *)
let pms_from_constructor_body env_c_body c_body sigma =
  let sigma, c_body_typ = reduce_type env_c_body c_body sigma in
  sigma, all_args c_body_typ sigma

(* TODO move, explain, clean *)
let constructor_body env c sigma =
  let open Environ in
  let sigma, c_typ = reduce_type env c sigma in
  let env_c_body, c_body = push_all_locals_prod env c_typ sigma in
  let nargs = nb_rel env_c_body - nb_rel env in
  sigma, (env_c_body, mkAppl (c, mk_n_args nargs))

(* TODO explain, clean *)
let swap_constructor env f c sigma =
  let sigma, (env_c_body, c_body) = constructor_body env c sigma in
  let sigma, pms = pms_from_constructor_body env_c_body c_body sigma in
  let f_args = List.append pms [c_body] in
  let f_c = apply_reduce normalize_term env f f_args sigma in
  sigma, first_fun f_c sigma

(* TODO make exercise, explain, clean *)
let get_swap_map env f old_ind sigma =
  map_constructors
    (fun old_c sigma ->
      let sigma, new_c = swap_constructor env f old_c sigma in
      sigma, (old_c, new_c))
    env
    (destInd sigma old_ind)
    sigma

(*
 * Substitute all occurrences of terms equal to src in trm with dst.
 * Make some simplifying assumptions about the format of trm
 * (no pattern matching, no fixpoints, not lets, and so on).
 *
 * HINT 1: You will want to use the mkLambda, mkProd, and mkApp functions 
 * defined in EConstr: https://github.com/coq/coq/blob/v8.14/engine/eConstr.mli
 *
 * HINT 2: If you are totally stuck, try copying and pasting the body of
 * each case of count, then adapting it to return the substituted term
 * instead of a number. The function will have almost exactly the same
 * structure.
 *)
let rec sub env (src, dst) trm sigma =
  let sigma, is_eq = equal env src trm sigma in
  if is_eq then
    (* when src is equal to trm, return dst *)
    sigma, dst
  else
    match kind sigma trm with
    | Constr.Lambda (n, t, b) ->
       (* sub (fun (n : t) => b) := fun (n : sub t) => sub b *)
       let sigma, sub_t = sub env (src, dst) t sigma in
       let sigma, sub_b = sub (push_local (n, t) env) (src, dst) b sigma in
       sigma, mkLambda (n, sub_t, sub_b)
    | Constr.Prod (n, t, b) ->
       (* sub (forall (n : t), b) := forall (n : sub t), sub b *)
       let sigma, sub_t = sub env (src, dst) t sigma in
       let sigma, sub_b = sub (push_local (n, t) env) (src, dst) b sigma in
       sigma, mkProd (n, sub_t, sub_b)
    | Constr.App (f, args) ->
       (* sub (f args) := ((sub f) (map sub args)) *)
       let sigma, sub_f = sub env (src, dst) f sigma in
       let sigma, sub_args =
         map_state_array
           (sub env (src, dst))
           args
           sigma
       in sigma, mkApp (sub_f, sub_args)
    | _ ->
       (* otherwise, return trm *)
       sigma, trm
