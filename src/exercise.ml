open EConstr
open Termutils

(*
 * Count the number of occurrences of terms equal to src in trm.
 * Make some simplifying assumptions about the format of trm
 * (no pattern matching, no fixpoints, no lets, and so on).
 *
 * I have done this one for you, to help you figure out how to implement sub.
 * I tried to use the state monad only when I felt like it added clarity,
 * but if you find it confusing, please ask for help.
 *)
let rec count env src trm sigma =
  let sigma, is_eq = equal env src trm sigma in
  if is_eq then
    (* when src is equal to trm, up the count *)
    sigma, 1
  else
    match kind sigma trm with
    | Constr.Lambda (n, t, b) ->
       (* count (fun (n : t) => b) := count t + count b *)
       let sigma, count_t = count env src t sigma in
       let sigma, count_b = count (push_local (n, t) env) src b sigma in
       sigma, count_t + count_b
    | Constr.Prod (n, t, b) ->
       (* count (forall (n : t), b := count t + count b *)
       let sigma, count_t = count env src t sigma in
       let sigma, count_b = count (push_local (n, t) env) src b sigma in
       sigma, count_t + count_b
    | Constr.App (f, args) ->
       (* count (f args) := count f + sum (count args) *)
       let sigma, count_f = count env src f sigma in
       let sigma, count_args =
         map_state_array
           (count env src)
           args
           sigma
       in sigma, Array.fold_left (fun b a -> b + a) count_f count_args
    | _ ->
       (* otherwise, no occurrences *)
       sigma, 0

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
let (*rec*) sub env (src, dst) trm sigma = (* uncomment rec when implementing *)
  let sigma, is_eq = equal env src trm sigma in
  if is_eq then
    (* when src is equal to trm, return dst *)
    sigma, dst
  else
    match kind sigma trm with
    | Constr.Lambda (n, t, b) -> (* fun (n : t) => b *)
       sigma, trm (* <- your implementation here *)
    | Constr.Prod (n, t, b) -> (* forall (n : t), b *)
       sigma, trm (* <- your implementation here *)
    | Constr.App (f, args) -> (* f args *)
       sigma, trm (* <- your implementation here *)
    | _ ->
       (* otherwise, return trm *)
       sigma, trm
