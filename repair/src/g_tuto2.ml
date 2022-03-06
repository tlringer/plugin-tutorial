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

(* TODO move etc *)
let print env t sigma = Printer.pr_econstr_env env sigma t


let () = Vernacextend.vernac_extend ~command:"DisplayMap" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Display", 
                                     Vernacextend.TyTerminal ("Map", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil))), (let coqpp_body e
                                                            () = Vernacextend.VtDefault (fun () -> 
                                                                 
# 30 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in
     let sigma, map = internalize env e sigma in
     let sigma, swap_map = get_swap_map env map sigma in
     Feedback.msg_notice
       (Pp.seq
          [Pp.str "This function maps: ";
           Pp.prlist_with_sep
             (fun _ -> Pp.str ", ")
             (fun (c_o, c_n) ->
               Pp.prlist_with_sep
                 (fun _ -> Pp.str " <-> ")
                 (Printer.pr_econstr_env env sigma)
                 [c_o; c_n])
             swap_map])
   
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
# 54 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in
     let sigma, map = internalize env e sigma in
     let sigma, swapped_ips = get_swapped_induction_principles env map sigma in
     List.iter2
       (fun ip suffix ->
         let prefix = Names.Id.to_string i in
         let id = Names.Id.of_string (String.concat "_" [prefix; suffix]) in
         define id ip sigma)
       swapped_ips
       ["ind"; "rec"; "rect"] 
   
              ) in fun i
         e ?loc ~atts () -> coqpp_body i e
         (Attributes.unsupported_attributes atts)), None))]

