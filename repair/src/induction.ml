
open Stateutils
open Environ
open EConstr
open Declarations
open Termutils
open Indrec
   
(*
 * A file full of useful functions for reasoning about inductive types
 * and inductive proofs inside of Coq.
 *)

(* --- Inductive Constructors --- *)

(*
 * Map a function f on all constructors of inductive type ind.
  *)
let map_constructors f env trm sigma =
  let ind = destInd sigma trm in
  let m_o = lookup_mind (fst (fst ind)) env in
  let b_o = m_o.mind_packets.(0) in
  let cs_o = b_o.mind_consnames in
  let ncons = Array.length cs_o in
  map_state
    (fun i -> f (mkConstructU ((fst ind, i), snd ind)))
    (Collections.range 1 (ncons + 1))
    sigma

(*
 * Get the index that corresponds to a constructor (0-indexed)
 *)
let index_of_constructor c sigma =
  try
    snd (fst (destConstruct sigma c)) - 1
  with _ ->
    failwith "not a constructor"

(* --- Induction Principles *)

(*
 * Get the induction principles from an inductive type
 *)
let principles env trm sigma =
  let ind = fst (destInd sigma trm) in
  map_state
    (fun t sigma -> fresh_global env sigma t)
    (List.map
       (lookup_eliminator env ind)
       [Sorts.InType; Sorts.InSet; Sorts.InProp])
    sigma

(* --- Inductive Proofs --- *)
  
(*
 * A nice useful representation of an inductive proof
 *)
type inductive_proof =
  {
    ip : EConstr.t; (* induction principle *)
    pms : EConstr.t list; (* polymorphic type parameters *)
    p : EConstr.t; (* inductive motive P *)
    cases : EConstr.t list; (* cases of the inductive proof *)
    final_args : EConstr.t list; (* any remaining arguments at the end *)
  }

(* Utility function for Coq boilerplate *)
let type_of_inductive index mutind_body =
  let ind_bodies = mutind_body.mind_packets in
  let ind_body = Array.get ind_bodies index in
  let univs = Declareops.inductive_polymorphic_context mutind_body in
  let univ_instance = Univ.make_abstract_instance univs in
  let mutind_spec = (mutind_body, ind_body) in
  EConstr.of_constr (Inductive.type_of_inductive (mutind_spec, univ_instance))
  
(*
 * Convert an applied term to an inductive_proof
 *)     
let of_application env app ind sigma =
  let from_i = fst (fst (destInd sigma ind)) in
  let ip = first_fun app sigma in
  let ip_args = all_args app sigma in
  let sigma, ip_typ = reduce_type env ip sigma in
  let from_m = lookup_mind from_i env in
  let npms = from_m.mind_nparams in
  let from_arity = arity (type_of_inductive 0 from_m) sigma in
  let num_indices = from_arity - npms in
  let num_props = 1 in
  let num_constrs = arity ip_typ sigma - npms - num_props - num_indices - 1 in
  let (pms, pmd_args) = Collections.take_split npms ip_args in
  match pmd_args with
  | p :: cs_and_args ->
     let (cases, final_args) = Collections.take_split num_constrs cs_and_args in
     sigma, { ip; pms; p; cases; final_args }
  | _ ->
     failwith "can't deconstruct eliminator; no final arguments"

(*
 * Convert the body of an induction principle to an inductive proof
 * Return the proof, and the environment in which it can be interpreted
 *)
let of_ip env ip ind sigma =
  let sigma, ip = expand_eta env ip sigma in
  let env_body, ip_body = push_all_locals_lambda env ip sigma in
  let sigma, proof = of_application env_body ip_body ind sigma in
  sigma, (env_body, proof)
