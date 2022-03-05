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
open Pp
open Stdarg
open Termutils
open Exercise



let () = Vernacextend.vernac_extend ~command:"SaveMap" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Map", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil))))), 
         (let coqpp_body o n e
         () = Vernacextend.VtDefault (fun () -> 
# 29 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in
     let sigma, old_ind = internalize env o sigma in
     let sigma, new_ind = internalize env n sigma in
     let sigma, map = internalize env e sigma in
     (* TODO: invert map, save both directions to a table *)
     ()
   
              ) in fun o
         n e ?loc ~atts () -> coqpp_body o n e
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
# 48 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in
     let sigma, old_ind = internalize env o sigma in
     let sigma, new_ind = internalize env n sigma in
     let sigma, trm = internalize env e sigma in
     (*
      * TODO: retrieve map, configure swap transformation,
      * swap trm, define new term
      *)
     ()
   
              ) in fun o
         n e i ?loc ~atts () -> coqpp_body o n e i
         (Attributes.unsupported_attributes atts)), None))]

