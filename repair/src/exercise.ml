open EConstr
open Termutils
open Stateutils
open Induction
open Collections

(* --- Exercise 1 --- *)

(*
 * Given the type of the supplied map function:
 *   old_ind pms -> new_ind pms
 * return the inductive types old_ind and new_ind.
 *
 * For example, if the input is:
 *   forall (T : Type), list T -> new_list T
 * This returns (list, new_list).
 *
 * I've given you a code skeleton; your job is to complete the code.
 *
 * HINTS:
 * 1. In Coq, (A -> B) is syntax for (forall (a : A), B),
 *    which is Constr.Prod (a, A, B) in the AST. So, our type:
 *      forall (T : Type), list T -> new_list T
 *    is really:
 *      Constr.Prod (T, Type, Constr.Prod (l, list T, new_list T))
 *
 * 2. The syntax:
 *      Constr.Prod (n, t, b) when isProd sigma b
 *    means that the match case is only triggered when b is also a product.
 *    So it would trigger on:
 *      Constr.Prod (T, Type, Constr.Prod (l, list T, new_list T))
 *    but it would not trigger on:
 *      Constr.Prod (l, list T, new_list T)
 *    Instead, the second case triggers on that.
 *
 * 3. We don't need to properly update the environment for this function,
 *    since we are returning something with no local variables in the
 *    end, like (list, new_list). I've included one for debugging purposes,
 *    and I've added a call that you can use to debug your function.
 *    It is commented out. You can uncomment it to print the type to debug.
 *    If you uncomment it, though, you will need you use push_local again
 *    to keep your environment up to date as you recurse, like you did in
 *    the first tutorial.
 *
 * 4. I've written a function:
 *      first_fun : EConstr.t -> evar_map -> EConstr.t
 *    that gets a function from an application in a disciplined way,
 *    dealing with some annoying Coq details about partial application.
 *    You may find it useful. It is in termutils.mli.
 *)
let rec inductives_from_map_type env map_type sigma : EConstr.t * EConstr.t =
  (* let _ = print_message env map_type sigma in *) (* <- uncomment to debug *) 
  match kind sigma map_type with
  | Constr.Prod (n, t, b) when isProd sigma b ->
     (* forall (n : t), forall ... *)
     let env_b = push_local (n, t) env in
     inductives_from_map_type env_b b sigma
  | Constr.Prod (n, t, b) ->
     (* forall (n : t), b *)
     (first_fun t sigma, first_fun b sigma)
  | _ ->
     (* print an error message *)
     CErrors.user_err
       (Pp.str "Map function does not have type old_ind -> new_ind")

(*
 * Given a map function:
 *   map : old_ind pms -> new_ind pms
 * return the inductive types old_ind and new_ind.
 *
 * For example, if the input is f from Demo.v, with:
 *   f : forall (T : Type), list T -> new_list T
 * This returns (list, new_list).
 *
 * I have given you the skeleton of this function.
 * You will finish implementing inductives_from_map_type.
 *)
let inductives_from_map env map sigma : (EConstr.t * EConstr.t) state =
  let sigma, map_type = normalize_type env map sigma in (* get type of map *)
  sigma, inductives_from_map_type env map_type sigma (*find (old_ind, new_ind)*)

(* --- Exercise 2 --- *)

(* TODO move, explain, clean *)
let constructor_body_typ_args env_c_body c_body sigma =
  let sigma, c_body_typ = reduce_type env_c_body c_body sigma in
  sigma, all_args c_body_typ sigma

(* TODO move, explain, clean *)
let constructor_body env c sigma =
  let sigma, c_typ = reduce_type env c sigma in
  let env_c_body, c_body = push_all_locals_prod env c_typ sigma in
  let nargs = arity c_typ sigma in
  sigma, (env_c_body, mkAppl (c, mk_n_args nargs))

(* TODO explain, clean *)
let swap_constructor env f c sigma =
  let sigma, (env_c_body, c_body) = constructor_body env c sigma in
  let sigma, typ_args = constructor_body_typ_args env_c_body c_body sigma in
  let f_args = snoc c_body typ_args in
  let f_c = apply_reduce normalize_term env f f_args sigma in
  sigma, first_fun f_c sigma

(* TODO make exercise, explain, clean *)
let get_swap_map env map sigma =
  let sigma, (old_ind, _) = inductives_from_map env map sigma in
  Induction.map_constructors
    (fun old_c sigma ->
      let sigma, new_c = swap_constructor env map old_c sigma in
      sigma, (old_c, new_c))
    env
    old_ind
    sigma

(* --- Exercise 3 --- *)

 (* TODO make exercise, explain, clean *)
let get_induction_map env map sigma =
  let sigma, swap_map = get_swap_map env map sigma in
  let sigma, (old_ind, new_ind) = inductives_from_map env map sigma in
  let sigma, old_ips = Induction.principles env old_ind sigma in
  (* TODO explain, move etc *)
  let lift_cases cases sigma =
    List.map
      (fun (c_o, c_n) ->
        List.nth cases (index_of_constructor c_n sigma))
      swap_map
  in
  (* TODO *)
  let lift_inductive t sigma =
    let args_o = is_or_applies old_ind t sigma in
    if Option.has_some args_o then
      let args = Option.get args_o in
      apply_reduce reduce_term env new_ind args sigma
    else
      t
  in
  (* TODO *)
  let rec lift_motive_type typ sigma =
      match kind sigma typ with
      | Constr.Prod (n, t, b) ->
         mkProd (n, lift_inductive t sigma, lift_motive_type b sigma)
      | _ ->
         typ
  in
  (* TODO *)
  let lift_constructor c sigma =
    let i = index_of_constructor c sigma in
    let swap_map = Array.of_list swap_map in
    snd (swap_map.(i))
  in
  (* TODO *)
  let rec lift_case_typ env case_typ sigma =
    match kind sigma case_typ with
    | Constr.Prod (n, t, b) ->
       let env_b = push_local (n, t) env in
       mkProd (n, lift_inductive t sigma, lift_case_typ env_b b sigma)
    | _ ->
       let f = first_fun case_typ sigma in
       let args = all_but_last (all_args case_typ sigma) in
       let arg = last (all_args case_typ sigma) in
       let c_args = all_args arg sigma in
       let lifted_constr = lift_constructor (first_fun arg sigma) sigma in
       let arg' = reduce_term env (mkAppl (lifted_constr, c_args)) sigma in
       reduce_term env (mkAppl (f, snoc arg' args)) sigma
  in
  (* TODO explain, move, etc *)
  let lift_env env old_ip sigma =
    let sigma, old_ip = expand_eta env old_ip sigma in
    let sigma, (_, old_ip_app) = Induction.of_ip env old_ip old_ind sigma in (* TODO env *)
    let env_pms, old_ip_pms = push_n_locals_lambda (List.length old_ip_app.pms) env old_ip sigma in
    let (p_n, p_typ, b) = destLambda sigma old_ip_pms in
    let env_pms_p = push_local (p_n, lift_motive_type p_typ sigma) env_pms in
    (* TODO *)
    let rec lift env elim i sigma =
      match kind sigma elim with
      | Constr.Lambda (n, t, b) ->
         if i < List.length old_ip_app.cases then
           lift (push_local (n, lift_case_typ env t sigma) env) b (i + 1) sigma
         else
           lift (push_local (n, lift_inductive t sigma) env) b (i + 1) sigma
      | _ ->
         env
    in lift env_pms_p b 0 sigma
  in
  (* TODO explain, move, clean, etc *)
  let lift_induction env old_ip new_ip sigma =
    let open Environ in
    let env_lifted = lift_env env old_ip sigma in
    let sigma, (_, new_ip_app) = Induction.of_ip env_lifted new_ip new_ind sigma in (* TODO env *)
    let pms = new_ip_app.pms in
    let p = new_ip_app.p in
    let new_ip_p_pms = mkAppl (new_ip, snoc p pms) in
    let sigma, (_, new_ip_p_pms_app) = Induction.of_ip env_lifted new_ip_p_pms new_ind sigma in (* TODO env *)
    let cs = lift_cases new_ip_app.cases sigma in
    let args = new_ip_p_pms_app.final_args in
    let new_ip_p_pms_cs_args = mkAppl (new_ip_p_pms, List.append cs args) in
    sigma, snd (reconstruct_lambda_n (nb_rel env) env_lifted new_ip_p_pms_cs_args)
  in
  let sigma, new_ips = Induction.principles env new_ind sigma in
  let sigma, lifted_ips =
    map_state
      (fun (old_ip, new_ip) sigma -> lift_induction env old_ip new_ip sigma)
      (List.combine old_ips new_ips)
      sigma
  in sigma, List.combine old_ips lifted_ips

(* --- Exercise 4 --- *)

(*
 * All code you need to implement for exercise 4 is in tuto2.mlg.
 * This is just a reminder of how things work, and the function you can call
 * in case you didn't get this far in the first tutorial.
 *
 * Substitute all occurrences of terms equal to src in trm with dst.
 * Make some simplifying assumptions about the format of trm
 * (no pattern matching, no fixpoints, not lets, and so on).
 *
 * This is an implementation that I wrote for the problem in the first
 * tutorial. The only difference is that I've extended it to handle casts,
 * since those show up in many simple test cases. I'm adding a couple of other
 * cases that are common but fairly straightforward. I haven't extended
 * it to handle some other cases that have a lot of complexities involved,
 * though, like fixpoints and recursively lifted constants.
 *
 * NOTE: In real life, it's common to use a higher-order function to map
 * over terms, since this pattern occurs frequently. This is more supportive,
 * but I didn't port any of mine here. This means we still have some limitations
 * to the terms we'll support. Nonetheless, you can find my higher-order
 * functions here, if interested:
 * https://github.com/uwplse/coq-plugin-lib/blob/master/src/coq/logicutils/hofs
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
    | Constr.Cast (b, k, t) ->
       (* sub (b : t) := ((sub b) : (sub t)) *)
       let sigma, sub_b = sub env (src, dst) b sigma in
       let sigma, sub_t = sub env (src, dst) t sigma in
       sigma, mkCast (sub_b, k, sub_t)
    | Constr.LetIn (n, trm, typ, e) ->
       (* ... honestly, I always get confused which term is which in let *)
       let sigma, sub_trm = sub env (src, dst) trm sigma in
       let sigma, sub_typ = sub env (src, dst) typ sigma in
       let sigma, sub_e = sub (push_let_in (n, e, typ) env) (src, dst) e sigma in
       sigma, mkLetIn (n, sub_trm, sub_typ, sub_e)
    | _ ->
       (* otherwise, return trm *)
       sigma, trm
