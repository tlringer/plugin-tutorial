open EConstr
open Termutils
open Stateutils

(* TODO move these etc *)
type elim_app =
  {
    elim : EConstr.t;
    pms : EConstr.t list;
    p : EConstr.t;
    cs : EConstr.t list;
    final_args : EConstr.t list;
  }

(* TODO move, explain, clean *)
let constructor_body_typ_args env_c_body c_body sigma =
  let sigma, c_body_typ = reduce_type env_c_body c_body sigma in
  sigma, all_args c_body_typ sigma

(* TODO move, explain, clean *)
let constructor_body env c sigma =
  let open Environ in
  let sigma, c_typ = reduce_type env c sigma in
  let env_c_body, c_body = push_all_locals_prod env c_typ sigma in
  let nargs = nb_rel env_c_body - nb_rel env in
  sigma, (env_c_body, mkAppl (c, mk_n_args nargs))

(* TODO move, explain, clean *)
let inductives_from_map env map sigma =
  let sigma, map_type = normalize_type env map sigma in
  let rec get_inds env map_type sigma =
    match kind sigma map_type with
    | Constr.Prod (n, t, b) when isProd sigma b ->
       get_inds (push_local (n, t) env) b sigma
    | Constr.Prod (n, t, b) ->
       (first_fun t sigma, first_fun b sigma)
    | _ ->
       CErrors.user_err
         (Pp.str "Map function does not have type old_ind -> new_ind")
  in sigma, get_inds env map_type sigma
  
(* TODO explain, clean *)
let swap_constructor env f c sigma =
  let sigma, (env_c_body, c_body) = constructor_body env c sigma in
  let sigma, typ_args = constructor_body_typ_args env_c_body c_body sigma in
  let f_args = List.append typ_args [c_body] in
  let f_c = apply_reduce normalize_term env f f_args sigma in
  sigma, first_fun f_c sigma

(* TODO make exercise, explain, clean *)
let get_swap_map env map sigma =
  let sigma, (old_ind, _) = inductives_from_map env map sigma in
  map_constructors
    (fun old_c sigma ->
      let sigma, new_c = swap_constructor env map old_c sigma in
      sigma, (old_c, new_c))
    env
    (destInd sigma old_ind)
    sigma

(* TODO move, clean, etc *)
let index_of_constructor c sigma =
  snd (fst (destConstruct sigma c))

(* TODO move etc *)
let rec reconstruct_lambda_n env b i =
  let open Environ in
  if nb_rel env = i then
    b
  else
    let (n, _, t) = Context.Rel.Declaration.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_lambda_n env' (mkLambda (n, (EConstr.of_constr t), b)) i

(* TODO move etc *)
let reconstruct_lambda env b =
  reconstruct_lambda_n env b 0

(* TODO clean move etc *)
let shift_by n trm sigma =
  EConstr.of_constr (Constr.liftn n 0 (EConstr.to_constr sigma trm))

(* TODO clean move etc *)
let expand_eta env trm sigma =
  let sigma, typ = reduce_type env trm sigma in
  let curried_args = mk_n_args (arity typ sigma) in
  sigma, reconstruct_lambda
           (fst (push_all_locals_prod (Environ.empty_env) typ sigma))
           (mkAppl (shift_by (List.length curried_args) trm sigma, curried_args))

(* TODO *)
let type_of_inductive index mutind_body =
  let open Declarations in
  let ind_bodies = mutind_body.mind_packets in
  let ind_body = Array.get ind_bodies index in
  let univs = Declareops.inductive_polymorphic_context mutind_body in
  let univ_instance = Univ.make_abstract_instance univs in
  let mutind_spec = (mutind_body, ind_body) in
  EConstr.of_constr (Inductive.type_of_inductive (mutind_spec, univ_instance))

(* TODO *)     
let deconstruct_eliminator env app ind sigma =
  let open Environ in
  let open Declarations in
  let from_i = fst (fst (destInd sigma ind)) in
  let elim = first_fun app sigma in
  let ip_args = all_args app sigma in
  let sigma, ip_typ = reduce_type env elim sigma in
  let from_m = lookup_mind from_i env in
  let npms = from_m.mind_nparams in
  let from_arity = arity (type_of_inductive 0 from_m) sigma in
  let num_indices = from_arity - npms in
  let num_props = 1 in
  let num_constrs = arity ip_typ sigma - npms - num_props - num_indices - 1 in
  let (pms, pmd_args) = Collections.take_split npms ip_args in
  match pmd_args with
  | p :: cs_and_args ->
     let (cs, final_args) = Collections.take_split num_constrs cs_and_args in
     sigma, { elim; pms; p; cs; final_args }
  | _ ->
     failwith "can't deconstruct eliminator; no final arguments"

(* TODO explain move etc *)
let deconstruct_ip env ip ind sigma =
  let sigma, ip = expand_eta env ip sigma in
  let env_body, ip_body = push_all_locals_lambda env ip sigma in
  deconstruct_eliminator env_body ip_body ind sigma
    
(* TODO clean move etc *)
let applies f trm sigma =
  match kind sigma trm with
  | Constr.App (g, _) ->
     Constr.equal (EConstr.to_constr sigma f) (EConstr.to_constr sigma g)
  | _ ->
     false

(* TODO *)
let is_or_applies trm' trm sigma =
  applies trm' trm sigma || Constr.equal (EConstr.to_constr sigma trm') (EConstr.to_constr sigma trm)

(* TODO *)
let last (l : 'a list) : 'a =
  List.hd (List.rev l)

(* TODO *)
let all_but_last (l : 'a list) : 'a list =
  List.rev (List.tl (List.rev l))
  
 (* TODO make exercise, explain, clean *)
let get_swapped_induction_principles env map sigma =
  let sigma, swap_map = get_swap_map env map sigma in
  let sigma, (old_ind, new_ind) = inductives_from_map env map sigma in
  let sigma, old_ips = induction_principles env (destInd sigma old_ind) sigma in
  (* TODO explain, move etc *)
  let lift_cases cases sigma =
    List.map
      (fun (c_o, c_n) ->
        let i = index_of_constructor c_n sigma in
        List.nth cases (i - 1))
      swap_map
  in
  (* TODO *)
  let lift_inductive t sigma =
    if is_or_applies old_ind t sigma then
      let args = all_args t sigma in
      if List.length args = 0 then
        new_ind
      else
        reduce_term env (mkAppl (new_ind, args)) sigma
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
    snd (swap_map.(i - 1))
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
       reduce_term env (mkAppl (f, List.append args [arg'])) sigma
  in
  (* TODO explain, move, etc *)
  let lift_env env old_ip sigma =
    let sigma, old_ip = expand_eta env old_ip sigma in
    let sigma, old_ip_app = deconstruct_ip env old_ip old_ind sigma in
    let env_pms, old_ip_pms = push_n_locals_lambda (List.length old_ip_app.pms) env old_ip sigma in
    let (p_n, p_typ, b) = destLambda sigma old_ip_pms in
    let env_pms_p = push_local (p_n, lift_motive_type p_typ sigma) env_pms in
    (* TODO *)
    let rec lift env elim i sigma =
      match kind sigma elim with
      | Constr.Lambda (n, t, b) ->
         if i < List.length old_ip_app.cs then
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
    let sigma, new_ip_app = deconstruct_ip env_lifted new_ip new_ind sigma in
    let pms = new_ip_app.pms in
    let p = new_ip_app.p in
    let new_ip_p_pms = mkAppl (new_ip, List.append pms [p]) in
    let sigma, new_ip_p_pms_app = deconstruct_ip env_lifted new_ip_p_pms new_ind sigma in
    let cs = lift_cases new_ip_app.cs sigma in
    let args = new_ip_p_pms_app.final_args in
    let new_ip_p_pms_cs_args = mkAppl (new_ip_p_pms, List.append cs args) in
    sigma, reconstruct_lambda_n env_lifted new_ip_p_pms_cs_args (nb_rel env)
  in
  let sigma, new_ips = induction_principles env (destInd sigma new_ind) sigma in
  map_state
    (fun (old_ip, new_ip) sigma ->
      lift_induction env old_ip new_ip sigma)
    (List.combine old_ips new_ips)
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
