let __coq_plugin_name = "tuto2_plugin"
let _ = Mltop.add_known_module __coq_plugin_name

# 3 "src/g_tuto2.mlg"
 

(*
 * In this exercise, we will implement a Coq plugin!
 * Our plugin will manipulate terms from Coq and define new terms.
 * As always, this will be discussion-based, with the usual format.
 *)
open Pp
open Stdarg
open Termutils
open Exercise



let () = Vernacextend.vernac_extend ~command:"MyDefine" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("MyDefine", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body i e
         () = Vernacextend.VtDefault (fun () -> 
# 38 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in (* get global state and environment *)
     let sigma, trm = internalize env e sigma in (* convert input term to internal representation *)
     define i trm sigma (* map input identifier to input term in the global environment *) 
   
              ) in fun i
         e ?loc ~atts () -> coqpp_body i e
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Count" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Count", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body src_e e
         () = Vernacextend.VtDefault (fun () -> 
# 76 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in (* get global state and environment *)
     let sigma, src = internalize env src_e sigma in (* convert to internal representation *)
     let sigma, trm = internalize env e sigma in (* convert to internal representation *)
     let sigma, count = count env src trm sigma in (* count occurrences of src in trm *)
     Feedback.msg_notice (strbrk (string_of_int count)) (* print the result *)
   
              ) in fun src_e
         e ?loc ~atts () -> coqpp_body src_e e
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Sub" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Sub", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                     Vernacextend.TyTerminal ("with", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                     Vernacextend.TyTerminal ("in", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                    Vernacextend.TyNil)))))))), 
         (let coqpp_body src_es dst_es e i
         () = Vernacextend.VtDefault (fun () -> 
# 104 "src/g_tuto2.mlg"
    
     let sigma, env = global_env () in
     let sigma, srcs = map_state (internalize env) src_es sigma in
     let sigma, dsts = map_state (internalize env) dst_es sigma in
     let sigma, trm = internalize env e sigma in
     let sigma, subbed =
       fold_left_state
         (fun subbed (src, dst) -> sub env (src, dst) subbed)
         trm
         (List.combine srcs dsts)
         sigma
     in Termutils.define i subbed sigma
   
              ) in fun src_es
         dst_es e i ?loc ~atts () -> coqpp_body src_es dst_es e i
         (Attributes.unsupported_attributes atts)), None))]

