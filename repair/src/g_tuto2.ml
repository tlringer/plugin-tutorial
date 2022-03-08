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
open Exercise
open Stateutils



let () = Vernacextend.vernac_extend ~command:"DisplayInductives" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Display", 
                                     Vernacextend.TyTerminal ("Inductives", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil))), (let coqpp_body e
                                                            () = Vernacextend.VtDefault (fun () -> 
                                                                 
# 63 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in
     let sigma, map = internalize env e sigma in
     let sigma, inds = inductives_from_map env map sigma in
     Feedback.msg_notice
       (Pp.seq
          [Pp.str "This function maps: ";
           print env (fst inds) sigma;
           Pp.str " -> ";
           print env (snd inds) sigma])
   
                                                                 ) in fun e
                                                            ?loc ~atts ()
                                                            -> coqpp_body e
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"DisplayMap" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Display", 
                                     Vernacextend.TyTerminal ("Map", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil))), (let coqpp_body e
                                                            () = Vernacextend.VtDefault (fun () -> 
                                                                 
# 113 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in
     let sigma, map = internalize env e sigma in
     let sigma, constructor_map = get_constructor_map env map sigma in
     Feedback.msg_notice
       (Pp.seq
          [Pp.str "This function maps: ";
           Pp.prlist_with_sep
             (fun _ -> Pp.str ", ")
             (fun (c_o, c_n) ->
               Pp.prlist_with_sep
                 (fun _ -> Pp.str " -> ")
                 (fun t -> print env t sigma)
                 [c_o; c_n])
             constructor_map])
   
                                                                 ) in fun e
                                                            ?loc ~atts ()
                                                            -> coqpp_body e
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"DefineMap" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Define", 
                                     Vernacextend.TyTerminal ("Map", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil))))), 
         (let coqpp_body i e
         () = Vernacextend.VtDefault (fun () -> 
# 174 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in
     let sigma, map = internalize env e sigma in
     let sigma, ip_map = get_induction_map env map sigma in
     List.iter2
       (fun (_, ip) suffix ->
         let prefix = Names.Id.to_string i in
         let id = Names.Id.of_string (String.concat "_" [prefix; suffix]) in
         define id ip sigma)
       ip_map
       ["rect"; "rec"; "ind"] 
   
              ) in fun i
         e ?loc ~atts () -> coqpp_body i e
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Swap" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Swapped", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil))))), 
         (let coqpp_body i f e
         () = Vernacextend.VtDefault (fun () -> 
# 230 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in
     let sigma, map = internalize env f sigma in
     let sigma, trm = internalize env e sigma in
     (* call your code: *)
     let sigma, typ_map = inductives_from_map env map sigma in (* 1 *)
     let sigma, constructor_map = get_constructor_map env map sigma in (* 2 *)
     let sigma, ip_map = get_induction_map env map sigma in (* 3 *)
     let sigma, swapped =
       fold_left_state
         (fun subbed (src, dst) sigma ->
           (* substitute and reduce *)
           let sigma, subbed = sub env (src, dst) subbed sigma in
           sigma, reduce_term env subbed sigma)
         (unwrap_definition env trm sigma) (* unfold constant *)
         (List.append (typ_map :: constructor_map) ip_map) (* combine *)
         sigma
     in Termutils.define i swapped sigma (* Profit! *)
   
              ) in fun i
         f e ?loc ~atts () -> coqpp_body i f e
         (Attributes.unsupported_attributes atts)), None))]

