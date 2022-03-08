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
 *
 * 5. When you recurse, you'll need to add the word "rec" before the function
 *    name inductives_from_map_type, again.
 *)
let inductives_from_map_type env map_type sigma : EConstr.t * EConstr.t =
  (* let _ = print_message env map_type sigma in *) (* <- uncomment to debug *) 
  match kind sigma map_type with
  | Constr.Prod (n, t, b) when isProd sigma b ->
     (* forall (n : t), forall ... *)
     CErrors.user_err (Pp.str "Not yet implemented") (* <- your code here *)
  | Constr.Prod (n, t, b) ->
     (* forall (n : t), b *)
     CErrors.user_err (Pp.str "Not yet implemented") (* <- your code here *)
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

(*
 * Get the body of a constructor, and an environment to interpret it in.
 *
 * For example, if the input is cons, we can think of this as really being:
 *   (fun (T : Type) (t : T) (l : list T) => cons T t l)
 * So, this function returns an environment:
 *   T : Type
 *   t : T
 *   l : list T
 * and an applied constructor:
 *   (cons T t l)
 *
 * I've written this for you.
 *)
let constructor_body env c sigma : (Environ.env * EConstr.t) state =
  let sigma, c = expand_eta env c sigma in
  let env_c_body, c_body = push_all_locals_lambda env c sigma in
  sigma, (env_c_body, mkAppl (c, mk_n_args (arity c sigma)))

(*
 * Given a constructor body, get the right arguments to the mapping function
 * to apply it to that constructor.
 *
 * For example, if the input is (cons T t l), this returns a list:
 *   [T; cons T t l]
 * so that we can apply the mapping function to those arguments:
 *   f T (cons T t l)
 *
 * I've written this for you.
 *)
let get_map_args_for_constructor env c_body sigma : (EConstr.t list) state =
  let sigma, c_body_type = reduce_type env c_body sigma in
  let typ_args = all_args c_body_type sigma in
  sigma, snoc c_body typ_args
  
(*
 * Given a constructor, like:
 *   cons
 * get the constructor that it maps to using the supplied map function, like:
 *   New.cons
 *
 * I've given you a skeleton of this, and a lot of helper functions.
 * There are many ways to solve this problem, but I find the easiest way
 * (about 4-5 LOC total) is to apply the map function to the constructor
 * at the right arguments, like:
 *   f T (cons T t l)
 * then reduce the result, producing a term like:
 *   New.cons T t (f T l)
 * and then get the first function:
 *   New.cons
 *
 * HINT 1: The first two lines I've written for you get all of the arguments
 * to the mapping function, like:
 *   [T; (cons T t l)]
 * you will want to apply the mapping function map to those arguments,
 * then reduce or normalize the result and get the first function. (Or at least,
 * that's one way to solve this problem.)
 *
 * HINT 2: Some functions that may be useful, from termutils.mli:
 *   normalize_term
 *   reduce_term
 *   apply_reduce
 *   first_fun
 *)
let swap_constructor env map c sigma : EConstr.t state =
  let sigma, (env, c_body) = constructor_body env c sigma in 
  let sigma, map_args = get_map_args_for_constructor env c_body sigma in
  ignore map_args; (* <- delete this line *)
  CErrors.user_err (Pp.str "Not yet implemented") (* <- your code here *)

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
let get_constructor_map env map sigma : ((EConstr.t * EConstr.t) list) state =
  let sigma, (old_ind, _) = inductives_from_map env map sigma in
  Induction.map_constructors
    (fun old_c sigma ->
      let sigma, new_c = swap_constructor env map old_c sigma in
      sigma, (old_c, new_c))
    env
    old_ind
    sigma

(* --- Exercise 3 --- *)

(*
 * NOTE: There is a lot of boilerplate needed here---I'm leaving just
 * the two most interesting cases for you, which given the induction 
 * principle over the old inductive type:
 * 1. swap cases to the order of the induction principle for the new
 *    inductive type, and
 * 2. repair the types of those cases to refer to the new inductive type
 *    rather than the old.
 *
 * The rest I will implement for you.
 *)
  
(*
 * Given the cases of an inductive proof in the order that makes sense
 * for the new inductive type, reorder those cases to the order that
 * would have made sense for the old inductive type.
 * 
 * For example, for list and New.list, proofs over New.list
 * take the cons case first, then the nil case, whereas proofs over
 * plain old lists took the nil case first, then the cons case.
 * Thus, given cases corresponding to:
 *   [cons; nil]
 * this function will reorder them, producing cases corresponding to:
 *   [nil; cons]
 *
 * Similarly, considering the five case enum in the test case, given
 * cases corresponding to:
 *   [e5'; e2'; e4'; e1'; e3']
 * this reorders them to cases corresponding to:
 *   [e1'; e2'; e3'; e4'; e5']
 *
 * This takes a bit of thought. I recommend working it out with a pencil
 * and paper before you rush to implement it, otherwise it's easy to mess up
 * (I did the first time). I've given you a number of hints below to help
 * if you get stuck. The Enum case is probably the most helpful for
 * testing this and walking through this; you can find it in Demo.v.
 *
 * HINT 1: Each constructor in Coq is associated with an index.
 * Usually this is 1-indexed, but I think it's much easier to work with
 * 0-indexed constructors. So we can think of New.cons as:
 *   Constr(0, New.list)
 * and we can think of New.nil as:
 *   Constr(1, New.list)
 * So, I've written a function for you, which you can find in induction.mli,
 * that returns this index. If you pass it New.nil, you'll get back 1;
 * if you pass it New.cons, you'll get back 0.
 *
 * HINT 2: In the body of this function, I've also written some skeleton
 * code for you that returns a map of indices given a map of constructors.
 * So, considering the enum above, index_map will be:
 *   [(0, 4); (1, 1); (2, 3); (3, 0); (4, 2)]
 * So, in the enum case, where you are given:
 *   [e5'; e2'; e4'; e1'; e3']
 * The corresponding indices are:
 *   [4; 1; 3; 0; 2]
 * And you want to reorder those cases to ones corresponding to:
 *   [0; 1; 2; 3; 4]
 * How do you do that? Read on to the next hint if you want more help.
 * The list library will be useful: https://ocaml.org/api/List.html
 *
 * HINT 3: Reverse each tuple in the index map:
 *   let index_map_rev = List.map (fun (i_o, i_n) -> (i_n, i_o)) index_map in ..
 * Now you have:
 *   [(4, 0); (1, 1); (3, 2); (0, 3); (2, 4)]
 * then, given some case corresponding to index:
 *   4
 * you will want to return the case corresponding to the index:
 *   0
 * Where is the 0 case in the input list? It's at the offset:
 *   List.assoc 0 index_map_rev
 * which is equal to 3. We can get the third case with:
 *   List.nth cases 3
 * So, the 0th case will map to:
 *   List.nth cases (List.assoc 0 (index_map_rev)),
 * and so on, for each i in [0, ..., List.length cases].
 *
 * There are a few ways to get each i for this; one way is to use
 * List.mapi, which maps over not just each list element, but also its
 * index in the list.
 *)
let repair_cases env cases constructor_map sigma : EConstr.t list =
  let index_map =
    List.map
      (fun (c_o, c_n) ->
        (index_of_constructor c_o sigma, index_of_constructor c_n sigma))
      constructor_map
  in
  ignore index_map; (* <- delete this line *)
  CErrors.user_err (Pp.str "Not yet implemented") (* <- your code here *)

(*
 * Given a constructor over the old type applied to some arguments,
 * repair it to the constructor over the new type, applied to the same arguments.
 *
 * This is the meat of repair_case_type, which is why I've left it to you.
 * So, for example, given:
 *   (cons T t l)
 * This should return:
 *   (New.cons T t l)
 *
 * HINT 1: Some functions that I found useful, from termutils.mli:
 *   first_fun
 *   all_args
 *   apply_reduce
 *   reduce_term
 * and from induction.mli:
 *   index_of_constructor
 * plus snd and List.nth from OCaml.
 *
 * HINT 2: Alternatively, you can pattern match over constr_app to
 * get the function and its arguments, and just do something in the Constr.App
 * case, avoiding the need for first_fun, all_args, and mkAppl.
 * This is less robust in general, but shouldn't make a difference here.
 *
 * HINT 3: My implementation was about 4-5 LOC.
 *
 * NOTE: This is the last thing you need to implement! After this you're
 * done. I've commented the rest of this, though, in case you feel like
 * looking at how things are implemented.
 *)
let repair_constructor env constr_app constructor_map sigma : EConstr.t =
  CErrors.user_err (Pp.str "Not yet implemented") (* <- your code here *)

(*
 * Lift an inductive type along the mapping function, and apply to
 * the same arguments. If the type is not the inductive type,
 * then do nothing. I've implemented this for you.
 *)
let repair_inductive env (old_ind, new_ind) t sigma : EConstr.t =
  let args_o = is_or_applies old_ind t sigma in
  if Option.has_some args_o then
    let args = Option.get args_o in
    apply_reduce reduce_term env new_ind args sigma
  else
    t

(*
 * Using that and your repair_inductive function, repair the type of the case.
 * I've implemented this for you, calling you repair_constructor function.
 *)
let rec repair_case_type env inds case_type constructor_map sigma : EConstr.t =
  match kind sigma case_type with
  | Constr.Prod (n, t, b) ->
     let t' = repair_inductive env inds t sigma in
     let env_b = push_local (n, t) env in
     mkProd (n, t', repair_case_type env_b inds b constructor_map sigma)
  | _ ->
     let f = first_fun case_type sigma in
     let args = all_but_last (all_args case_type sigma) in
     let constr_app = last (all_args case_type sigma) in
     let repaired_constr = repair_constructor env constr_app constructor_map sigma in
     apply_reduce reduce_term env f (snoc repaired_constr args) sigma

(*
 * Repair the type of the motive
 *)
let rec repair_motive_type env inds typ sigma =
  match kind sigma typ with
  | Constr.Prod (n, t, b) ->
     let t' = repair_inductive env inds t sigma in
     let env_b = push_local (n, t) env in
     mkProd (n, t', repair_motive_type env_b inds b sigma)
  | _ ->
     typ

(*
 * Update the environment containing hypotheses from the old induction
 * principle, so that it instead contains hypothese for the repaired
 * induction principle over the new inductive type that we will produce.
 *)
let repair_env env inds old_ip constructor_map sigma =
  let sigma, old_ip = expand_eta env old_ip sigma in
  let sigma, (_, proof) = Induction.of_ip env old_ip (fst inds) sigma in
  let npms = List.length proof.pms in
  let env_pms, old_ip_pms = push_n_locals_lambda npms env old_ip sigma in
  let (p_n, p_typ, b) = destLambda sigma old_ip_pms in
  let p_typ' = repair_motive_type env_pms inds p_typ sigma in
  let env_pms_p = push_local (p_n, p_typ') env_pms in
  let rec repair env elim i sigma =
    match kind sigma elim with
    | Constr.Lambda (n, t, b) ->
       let t' =
         if i < List.length proof.cases then
           repair_case_type env inds t constructor_map sigma
         else
           repair_inductive env inds t sigma
       in repair (push_local (n, t') env) b (i + 1) sigma
    | _ ->
       env
  in repair env_pms_p b 0 sigma

(*
 * Repair the induction principle.
 * I've implemented this for you, too.
 *)
let repair_induction env inds constructor_map (old_ip, new_ip) sigma =
  let env_rep = repair_env env inds old_ip constructor_map sigma in
  let sigma, (_, proof) = Induction.of_ip env_rep new_ip (snd inds) sigma in
  let pms = proof.pms in
  let p = proof.p in
  let proof_p_pms = mkAppl (new_ip, snoc p pms) in
  let sigma, (_, proof) = Induction.of_ip env_rep proof_p_pms (snd inds) sigma in
  let cases = repair_cases env_rep proof.cases constructor_map sigma in
  let args = proof.final_args in
  let proof_p_pms_cs_args = mkAppl (proof_p_pms, List.append cases args) in
  let _, induction_rep =
    reconstruct_lambda_n (Environ.nb_rel env) env_rep proof_p_pms_cs_args
  in sigma, induction_rep
   
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
let get_induction_map env map sigma : ((EConstr.t * EConstr.t) list) state =
  let sigma, constructor_map = get_constructor_map env map sigma in
  let sigma, inds = inductives_from_map env map sigma in
  let sigma, old_ips = Induction.principles env (fst inds) sigma in
  let sigma, new_ips = Induction.principles env (snd inds) sigma in
  let sigma, repaired_ips =
    map_state
      (repair_induction env inds constructor_map)
      (List.combine old_ips new_ips)
      sigma
  in sigma, List.combine old_ips repaired_ips

(* --- Profit --- *)

(*
 * I'm giving you an implementation of sub here so that you can use it
 * in the final command in g_tuto2.mlg without needing to go back
 * and finish the first tutorial.
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
 * though, like fixpoints and recursively repaired constants.
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
