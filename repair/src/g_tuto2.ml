let __coq_plugin_name = "tuto2_plugin"
let _ = Mltop.add_known_module __coq_plugin_name

# 3 "src/g_tuto2.mlg"
 

(*
 * In this exercise, we will extend our Coq plugin from before!
 * Last time, we wrote a plugin that manipulates terms from Coq
 * and then defines new terms. This time, we'll use that same idea
 * to implement a form of proof repair!
 *
 * As always, this will be discussion-based, with the usual format.
 *)
open Stdarg
open Termutils
(*open Exercise*)

type elim_app =
  {
    elim : EConstr.t;
    pms : EConstr.t list;
    p : EConstr.t;
    cs : EConstr.t list;
    final_args : EConstr.t list;
  }


  
let print env t sigma = Printer.pr_econstr_env env sigma t


let () = Vernacextend.vernac_extend ~command:"SaveMap" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Map", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil)))))), 
         (let coqpp_body i o n e
         () = Vernacextend.VtDefault (fun () -> 
# 40 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in
     let sigma, old_ind = internalize env o sigma in
     let sigma, new_ind = internalize env n sigma in
     let sigma, map = internalize env e sigma in
     (* TODO move me, comment, etc *)
     let rec zoom_product_type env typ =
       let open EConstr in
       match kind sigma typ with
       | Constr.Prod (n, t, b) ->
          zoom_product_type (push_local (n, t) env) b
       | _ ->
          (env, typ)
     in
     (* TODO move me, comment, etc *)
     let reduce_type env trm sigma =
       let sigma, typ = Typing.type_of ~refresh:true env sigma trm in
       sigma, Reductionops.nf_betaiotazeta env sigma typ
     in
     (* TODO move me, comment, etc *)
     let unfold_args_app trm sigma =
       let open EConstr in
       let (f, args) = destApp sigma trm in
       let rec unfold trm sigma =
         match kind sigma trm with
         | Constr.App (f, args) ->
            List.append (unfold f sigma) (Array.to_list args)
         | _ ->
            [trm]
       in List.append (List.tl (unfold f sigma)) (Array.to_list args)
     in
     (* TODO move me, comment, etc *)
     let unfold_args trm sigma =
       let open EConstr in
       if isApp sigma trm then unfold_args_app trm sigma else []
     in
     (* TODO move me, comment, etc *)
     let rec first_fun trm sigma =
       let open EConstr in
       match kind sigma trm with
       | Constr.App (f, args) ->
          first_fun f sigma
       | _ ->
          trm
     in
     (* TODO mvoe, comment, etc *)
     let mk_n_rels n =
       let open EConstr in
       Array.of_list (List.map mkRel (List.rev (Collections.range 1 (n + 1))))
     in
     (* TODO move me, comment, etc *)
     let get_swap_map env old_ind (f : EConstr.t) (sigma : Evd.evar_map) =
       let open EConstr in
       let open Environ in
       let open Declarations in
       let ((i_o, ii_o), u_o) = destInd sigma old_ind in
       let m_o = lookup_mind i_o env in
       let b_o = m_o.mind_packets.(0) in
       let cs_o = b_o.mind_consnames in
       let ncons = Array.length cs_o in
       map_state
         (fun i sigma ->
           let c_o = mkConstructU (((i_o, ii_o), i), u_o) in
           let sigma, c_o_typ = reduce_type env c_o sigma in
           let env_c_o, c_o_typ = zoom_product_type env c_o_typ in
           let nargs = nb_rel env_c_o - nb_rel env in
           let c_o_args = mk_n_rels nargs in
           let c_o_app = mkApp (c_o, c_o_args) in
           let typ_args : EConstr.t list = unfold_args c_o_typ sigma in
           let c_o_lifted = mkApp (f, Array.of_list (List.append typ_args [c_o_app])) in
           let c_o_lifted_red = Reductionops.nf_all env sigma c_o_lifted in
           let swap = (c_o, first_fun c_o_lifted_red sigma) in
           let print env t sigma = Printer.pr_econstr_env env sigma t in
           Feedback.msg_notice (print env (fst swap) sigma);
           Feedback.msg_notice (print env (snd swap) sigma);
           Feedback.msg_notice (Pp.str ";");
           sigma, swap)
         (Collections.range 1 (ncons + 1))
         sigma
     in
     let sigma, swap_map = get_swap_map env old_ind map sigma in
     (* TODO explain move etc *)
     let type_eliminator env ind sigma =
       Evd.fresh_global env sigma (Indrec.lookup_eliminator env ind Sorts.InType)
     in
     let open EConstr in
     let sigma, old_elim = type_eliminator env (fst (destInd sigma old_ind)) sigma in
     let reduce_term env trm sigma =
       Reductionops.nf_betaiotazeta env sigma trm
     in
     (* TODO explain, move etc *)
     let initialize_dep_elim_cs env_dep_elim elim_p npms cs swap_map sigma =
       let swaps : (int * int) list =
         List.map
           (fun (c_o, c_n) ->
             let (((_, _), i_o), _) = destConstruct sigma c_o in
             let (((_, _), i_n), _) = destConstruct sigma c_n in
             (i_o, i_n))
           swap_map
       in 
       let cs =
         let cs_arr = Array.of_list cs in
         List.map
           (fun i -> cs_arr.(List.assoc i swaps - 1))
           (Collections.range 1 (List.length cs + 1))
       in
       bind
         (fold_left_state
            (fun (elim_c, cs) case sigma ->
              let elim_c = reduce_term env_dep_elim (mkApp (elim_c, Array.make 1 case)) sigma in
              sigma, (elim_c, List.append cs [case]))
            (elim_p, [])
            cs)
         (fun (_, cs) -> ret cs)
         sigma
     in
     (* TODO whatever *)
     let rec arity p sigma =
       let open EConstr in
       match kind sigma p with
       | Constr.Lambda (_, _, b) ->
          1 + arity b sigma
       | Constr.Prod (_, _, b) ->
          1 + arity b sigma
       | _ ->
          0
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
     let zoom_env zoom env trm =
       fst (zoom env trm)
     in
     (* TODO clean move etc *)
     let shift_by n trm sigma =
       EConstr.of_constr (Constr.liftn n 0 (EConstr.to_constr sigma trm))
     in
     (* TODO clean move etc *)
     let expand_eta env trm sigma =
       let sigma, typ = reduce_type env trm sigma in
       let curried_args = Array.to_list (mk_n_rels (arity typ sigma)) in
       sigma, reconstruct_lambda
                (zoom_env zoom_product_type (Environ.empty_env) typ)
                (mkApp (shift_by (List.length curried_args) trm sigma, Array.of_list curried_args))
     in
     (* TODO *)
     let rec zoom_lambda_term env trm sigma =
       let open EConstr in
       match kind sigma trm with
       | Constr.Lambda (n, t, b) ->
          zoom_lambda_term (push_local (n, t) env) b sigma
       | _ ->
          (env, trm)
     in
     (* TODO *)
     let type_of_inductive index mutind_body =
       let open Declarations in
       let open Environ in
       let ind_bodies = mutind_body.mind_packets in
       let ind_body = Array.get ind_bodies index in
       let univs = Declareops.inductive_polymorphic_context mutind_body in
       let univ_instance = Univ.make_abstract_instance univs in
       let mutind_spec = (mutind_body, ind_body) in
       EConstr.of_constr (Inductive.type_of_inductive (mutind_spec, univ_instance))
     in
     (* TODO *)
     let rec take_split (i : int) (l : 'a list) : ('a list * 'a list) =
       if i = 0 then
         ([], l)
       else
         match l with
         | [] ->
            ([], [])
         | h :: tl ->
            let (before, after) = take_split (i - 1) tl in
            (h :: before, after)
     in
     (* TODO *)     
     let deconstruct_eliminator env app from_i sigma =
       let open Environ in
       let open Declarations in
       let open Names in
       let elim = first_fun app sigma in
       let ip_args = unfold_args app sigma in
       let sigma, ip_typ = reduce_type env elim sigma in
       let from_m = lookup_mind from_i env in
       let npms = from_m.mind_nparams in
       let from_arity = arity (type_of_inductive 0 from_m) sigma in
       let num_indices = from_arity - npms in
       let num_props = 1 in
       let num_constrs = arity ip_typ sigma - npms - num_props - num_indices - 1 in
       let (pms, pmd_args) = take_split npms ip_args in
       match pmd_args with
       | p :: cs_and_args ->
          let (cs, final_args) = take_split num_constrs cs_and_args in
          sigma, { elim; pms; p; cs; final_args }
       | _ ->
          failwith "can't deconstruct eliminator; no final arguments"
     in
     (* TODO *)
     let rec zoom_n_lambda env npm typ sigma =
       let open EConstr in
       if npm = 0 then
         (env, typ)
       else
         match kind sigma typ with
         | Constr.Lambda (n1, t1, b1) ->
            zoom_n_lambda (push_local (n1, t1) env) (npm - 1) b1 sigma
         | _ ->
            failwith "more parameters expected"
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
       Feedback.msg_notice (print env elim_rev_eta sigma);
       let env_elim_rev, elim_body_rev = zoom_lambda_term env elim_rev_eta sigma in
       Feedback.msg_notice (print env_elim_rev elim_body_rev sigma);
       let sigma, elim_app_rev = deconstruct_eliminator env_elim_rev elim_body_rev from_i sigma in
       let env, elim_rev = zoom_n_lambda env (List.length elim_app_rev.pms) elim_rev_eta sigma in
       Feedback.msg_notice (print env elim_rev sigma);
       let (p_n, p_typ, b) = destLambda sigma elim_rev in
       let rec init_p_typ env p_typ sigma =
         let open EConstr in
         match kind sigma p_typ with
         | Constr.Prod (n, t, b) ->
            let env_b = push_local (n, t) env in
            let sigma, b' = init_p_typ env_b b sigma in
            if is_or_applies (mkInd (from_i, 0)) t sigma then
              let args = unfold_args t sigma in
              let t' =
                if List.length args = 0 then
                  mkInd (to_i, 0)
                else
                  reduce_term env (mkApp (mkInd (to_i, 0), Array.of_list args)) sigma
              in sigma, mkProd (n, t', b')
            else
              sigma, mkProd (n, t, b')
         | _ ->
            sigma, p_typ
       in
       let sigma, p_typ' = init_p_typ env p_typ sigma in
       Feedback.msg_notice (print env p_typ' sigma);
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
              let args = unfold_args t sigma in
              let t' =
                if List.length args = 0 then
                  mkInd (to_i, 0)
                else
                  mkApp (mkInd (to_i, 0), Array.of_list args)
              in sigma, mkProd (n, t', b')
            else if is_or_applies p t sigma then
              let open Environ in
              let t' =
                let f = first_fun t sigma in
                let args = all_but_last (unfold_args t sigma) in
                let arg = last (unfold_args t sigma) in
                let pms = mk_n_rels (List.length elim_app_rev.pms) in
                let pms = Array.map (fun t -> shift_by (nb_rel env - Array.length pms) t sigma) pms in
                reduce_term env (mkApp (f, Array.of_list (List.append args [arg]))) sigma
              in sigma, mkProd (n, t', b')
            else
              sigma, mkProd (n, t, b')
         | _ ->
            let f = first_fun case_typ sigma in
            let args = all_but_last (unfold_args case_typ sigma) in
            let arg = last (unfold_args case_typ sigma) in
            let ((_, i), _) = destConstruct sigma (first_fun arg sigma) in
            let c_args = unfold_args arg sigma in
            let swap_map = Array.of_list swap_map in
            let (_, lifted_constr) = swap_map.(i - 1) in
            let arg' = reduce_term env (mkApp (lifted_constr, Array.of_list c_args)) sigma in
            sigma, reduce_term env (mkApp (f, Array.of_list (List.append args [arg']))) sigma
       in
       let rec init env elim i from_i to_i swap_map sigma =
         let open EConstr in
         match kind sigma elim with
         | Constr.Lambda (n, t, b) ->
            if i < List.length elim_app_rev.cs then
              let sigma, t' = init_case_typ env t (mkRel (i + 1)) from_i to_i swap_map sigma in
              Feedback.msg_notice (print env t' sigma);
              init (push_local (n, t') env) b (i + 1) from_i to_i swap_map sigma
            else if is_or_applies (mkInd (from_i, 0)) t sigma then
              let args = unfold_args t sigma in
              let sigma, t' =
                if List.length args = 0 then
                  sigma, mkInd (to_i, 0)
                else
                  sigma, mkApp (mkInd (to_i, 0), Array.of_list args)
              in init (push_local (n, t') env) b (i + 1) from_i to_i swap_map sigma
            else
              init (push_local (n, t) env) b (i + 1) from_i to_i swap_map sigma
         | _ ->
            sigma, env
       in init env_p b 0 from_i to_i swap_map sigma
     in
     let mkAppl (f, args) = mkApp (f, Array.of_list args) in
     (* TODO explain, move, etc *)
     let initialize_dep_elim env elim elim_new from_i to_i sigma =
       let open Environ in
       let sigma, env_dep_elim = initialize_dep_elim_env env elim from_i to_i sigma in
       let sigma, elim_eta = expand_eta env_dep_elim elim_new sigma in
       Feedback.msg_notice (print env_dep_elim elim_eta sigma);
       let sigma, dep_elim =
         let npms =
           let env_elim, elim_body = zoom_lambda_term env_dep_elim elim_eta sigma in
           let sigma, elim_app = deconstruct_eliminator env_elim elim_body from_i sigma in
           List.length elim_app.pms
         in
         let pms = Array.map (fun t -> shift_by (nb_rel env_dep_elim - npms) t sigma) (mk_n_rels npms) in
         let elim_pms = reduce_term env_dep_elim (mkApp (elim_eta, pms)) sigma in
         let p = shift_by (nb_rel env_dep_elim - npms - 1) (mkRel 1) sigma in
         let elim_p = reduce_term env_dep_elim (mkAppl (elim_pms, [p])) sigma in
         let sigma, cs =
           let sigma, elim_eta = expand_eta env_dep_elim elim_p sigma in
           let env_elim, elim_body = zoom_lambda_term env_dep_elim elim_eta sigma in
           let elim_body = reduce_term env_elim elim_body sigma in
           let sigma, elim_app = deconstruct_eliminator env_elim elim_body from_i sigma in
           initialize_dep_elim_cs env_dep_elim elim_p npms elim_app.cs swap_map sigma
         in
         let elim_cs = reduce_term env_dep_elim (mkAppl (elim_p, cs)) sigma in
         let final_args =
           let nargs = arity elim_cs sigma in
           mk_n_rels nargs
         in sigma, reduce_term env_dep_elim (mkApp (elim_cs, final_args)) sigma
       in sigma, reconstruct_lambda_n env_dep_elim dep_elim (nb_rel env)
     in
     let sigma, new_elim =
       let _ = Feedback.msg_notice (print env new_ind sigma) in
       let sigma, new_elim_old = type_eliminator env (fst (destInd sigma new_ind)) sigma in
       Feedback.msg_notice (print env new_elim_old sigma);
       let (from_i, _) = fst (destInd sigma old_ind) in
       let (to_i, _) = fst (destInd sigma new_ind) in
       initialize_dep_elim env old_elim new_elim_old from_i to_i sigma
     in
     Feedback.msg_notice (print env old_elim sigma);
     Feedback.msg_notice (print env new_elim sigma);
     define i new_elim sigma;
     (* TODO define old and new eliminators *)
     ()
   
              ) in fun i
         o n e ?loc ~atts () -> coqpp_body i o n e
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"SwapCases" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Swap", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                    Vernacextend.TyNil))))))), 
         (let coqpp_body o n e i
         () = Vernacextend.VtDefault (fun () -> 
# 427 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in
     let sigma, old_ind = internalize env o sigma in
     let sigma, new_ind = internalize env n sigma in
     let sigma, trm = internalize env e sigma in
     (*
      * TODO: retrieve configuration (not in table, just get from scratch---note about table in exercise), pass to sub implementation
      *)
     ()
   
              ) in fun o
         n e i ?loc ~atts () -> coqpp_body o n e i
         (Attributes.unsupported_attributes atts)), None))]
