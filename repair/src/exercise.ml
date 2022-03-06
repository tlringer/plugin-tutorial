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
  
 (* TODO make exercise, explain, clean *)
let get_swapped_induction_principles env map sigma =
  let sigma, swap_map = get_swap_map env map sigma in
  let sigma, (old_ind, new_ind) = inductives_from_map env map sigma in
  let sigma, old_ips = induction_principles env (destInd sigma old_ind) sigma in
  (* TODO explain, move etc *)
  let initialize_dep_elim_cases env_dep_elim elim_p cases sigma =
    let swapped_cases =
      List.map
        (fun (c_o, c_n) ->
          let i = index_of_constructor c_n sigma in
          List.nth cases (i - 1))
        swap_map
    in
    snd
      (List.fold_left
         (fun (elim_c, swapped_cases) swapped_case ->
           let elim_c = apply_reduce reduce_term env_dep_elim elim_c [swapped_case] sigma in
           elim_c, List.append swapped_cases [swapped_case])
         (elim_p, [])
         swapped_cases)
  in
  (* TODO move etc *)
     let rec reconstruct_lambda_n env b i =
       let open Environ in
       if nb_rel env = i then
         b
       else
         let (n, _, t) = Context.Rel.Declaration.to_tuple @@ lookup_rel 1 env in
         let env' = pop_rel_context 1 env in
         reconstruct_lambda_n env' (mkLambda (n, (EConstr.of_constr t), b)) i
     in
     let reconstruct_lambda env b =
       reconstruct_lambda_n env b 0
     in
     (* TODO clean move etc *)
     let shift_by n trm sigma =
       EConstr.of_constr (Constr.liftn n 0 (EConstr.to_constr sigma trm))
     in
     (* TODO clean move etc *)
     let expand_eta env trm sigma =
       let sigma, typ = reduce_type env trm sigma in
       let curried_args = mk_n_args (arity typ sigma) in
       sigma, reconstruct_lambda
                (fst (push_all_locals_prod (Environ.empty_env) typ sigma))
                (mkAppl (shift_by (List.length curried_args) trm sigma, curried_args))
     in
     (* TODO *)
     let type_of_inductive index mutind_body =
       let open Declarations in
       let ind_bodies = mutind_body.mind_packets in
       let ind_body = Array.get ind_bodies index in
       let univs = Declareops.inductive_polymorphic_context mutind_body in
       let univ_instance = Univ.make_abstract_instance univs in
       let mutind_spec = (mutind_body, ind_body) in
       EConstr.of_constr (Inductive.type_of_inductive (mutind_spec, univ_instance))
     in
     (* TODO *)     
     let deconstruct_eliminator env app from_i sigma =
       let open Environ in
       let open Declarations in
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
     in
     (* TODO clean move etc *)
     let applies f trm sigma =
       let open EConstr in
       match kind sigma trm with
       | Constr.App (g, _) ->
          Constr.equal (EConstr.to_constr sigma f) (EConstr.to_constr sigma g)
       | _ ->
          false
     in
     let is_or_applies trm' trm sigma =
       applies trm' trm sigma || Constr.equal (EConstr.to_constr sigma trm') (EConstr.to_constr sigma trm)
     in
     let initialize_dep_elim_env env elim_rev from_i to_i sigma =
       let sigma, elim_rev_eta = expand_eta env elim_rev sigma in
       let env_elim_rev, elim_body_rev = push_all_locals_lambda env elim_rev_eta sigma in
       let sigma, elim_app_rev = deconstruct_eliminator env_elim_rev elim_body_rev from_i sigma in
       let env, elim_rev = push_n_locals_lambda (List.length elim_app_rev.pms) env elim_rev_eta sigma in
       let (p_n, p_typ, b) = destLambda sigma elim_rev in
       let rec init_p_typ env p_typ sigma =
         let open EConstr in
         match kind sigma p_typ with
         | Constr.Prod (n, t, b) ->
            let env_b = push_local (n, t) env in
            let sigma, b' = init_p_typ env_b b sigma in
            if is_or_applies (mkInd (from_i, 0)) t sigma then
              let args = all_args t sigma in
              let t' =
                if List.length args = 0 then
                  mkInd (to_i, 0)
                else
                  reduce_term env (mkAppl (mkInd (to_i, 0), args)) sigma
              in sigma, mkProd (n, t', b')
            else
              sigma, mkProd (n, t, b')
         | _ ->
            sigma, p_typ
       in
       let sigma, p_typ' = init_p_typ env p_typ sigma in
       let env_p = push_local (p_n, p_typ') env in
       let last (l : 'a list) : 'a =
         List.hd (List.rev l)
       in
       let all_but_last (l : 'a list) : 'a list =
         List.rev (List.tl (List.rev l))
       in
       (* TODO *)
       let rec init_case_typ env case_typ p from_i to_i swap_map sigma =
         let open EConstr in
         match kind sigma case_typ with
         | Constr.Prod (n, t, b) ->
            let env_b = push_local (n, t) env in
            let sigma, b' = init_case_typ env_b b (shift_by 1 p sigma) from_i to_i swap_map sigma in
            if is_or_applies (mkInd (from_i, 0)) t sigma then
              let args = all_args t sigma in
              let t' =
                if List.length args = 0 then
                  mkInd (to_i, 0)
                else
                  mkAppl (mkInd (to_i, 0), args)
              in sigma, mkProd (n, t', b')
            else
              sigma, mkProd (n, t, b')
         | _ ->
            let f = first_fun case_typ sigma in
            let args = all_but_last (all_args case_typ sigma) in
            let arg = last (all_args case_typ sigma) in
            let ((_, i), _) = destConstruct sigma (first_fun arg sigma) in
            let c_args = all_args arg sigma in
            let swap_map = Array.of_list swap_map in
            let (_, lifted_constr) = swap_map.(i - 1) in
            let arg' = reduce_term env (mkAppl (lifted_constr, c_args)) sigma in
            sigma, reduce_term env (mkAppl (f, List.append args [arg'])) sigma
       in
       let rec init env elim i from_i to_i swap_map sigma =
         let open EConstr in
         match kind sigma elim with
         | Constr.Lambda (n, t, b) ->
            if i < List.length elim_app_rev.cs then
              let sigma, t' = init_case_typ env t (mkRel (i + 1)) from_i to_i swap_map sigma in
              init (push_local (n, t') env) b (i + 1) from_i to_i swap_map sigma
            else if is_or_applies (mkInd (from_i, 0)) t sigma then
              let args = all_args t sigma in
              let sigma, t' =
                if List.length args = 0 then
                  sigma, mkInd (to_i, 0)
                else
                  sigma, mkAppl (mkInd (to_i, 0), args)
              in init (push_local (n, t') env) b (i + 1) from_i to_i swap_map sigma
            else
              init (push_local (n, t) env) b (i + 1) from_i to_i swap_map sigma
         | _ ->
            sigma, env
       in init env_p b 0 from_i to_i swap_map sigma
     in
     (* TODO explain, move, etc *)
     let initialize_dep_elim env elim elim_new from_i to_i sigma =
       let open Environ in
       let sigma, env_dep_elim = initialize_dep_elim_env env elim from_i to_i sigma in
       let sigma, elim_eta = expand_eta env_dep_elim elim_new sigma in
       let sigma, dep_elim =
         let npms =
           let env_elim, elim_body = push_all_locals_lambda env_dep_elim elim_eta sigma in
           let sigma, elim_app = deconstruct_eliminator env_elim elim_body from_i sigma in
           List.length elim_app.pms
         in
         let pms = List.map (fun t -> shift_by (nb_rel env_dep_elim - npms) t sigma) (mk_n_args npms) in
         let elim_pms = reduce_term env_dep_elim (mkAppl (elim_eta, pms)) sigma in
         let p = shift_by (nb_rel env_dep_elim - npms - 1) (mkRel 1) sigma in
         let elim_p = reduce_term env_dep_elim (mkAppl (elim_pms, [p])) sigma in
         let sigma, cs =
           let sigma, elim_eta = expand_eta env_dep_elim elim_p sigma in
           let env_elim, elim_body = push_all_locals_lambda env_dep_elim elim_eta sigma in
           let elim_body = reduce_term env_elim elim_body sigma in
           let sigma, elim_app = deconstruct_eliminator env_elim elim_body from_i sigma in
           sigma, initialize_dep_elim_cases env_dep_elim elim_p elim_app.cs sigma
         in
         let elim_cs = reduce_term env_dep_elim (mkAppl (elim_p, cs)) sigma in
         let final_args = mk_n_args (arity elim_cs sigma) in
         sigma, reduce_term env_dep_elim (mkAppl (elim_cs, final_args)) sigma
       in sigma, reconstruct_lambda_n env_dep_elim dep_elim (nb_rel env)
     in
     let sigma, new_ips = induction_principles env (destInd sigma new_ind) sigma in
     map_state
       (fun (old_ip, new_ip) sigma ->
         
         let (from_i, _) = fst (destInd sigma old_ind) in
         let (to_i, _) = fst (destInd sigma new_ind) in
         initialize_dep_elim env old_ip new_ip from_i to_i sigma
       )
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
