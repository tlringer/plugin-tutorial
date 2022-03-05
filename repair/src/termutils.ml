(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 * Utilities for the state monad were moved to stateutils.ml/stateutils.mli
 *)

open EConstr
open Declarations
open Environ
open Stateutils

(* --- Environments --- *)

(*
 * Environments in the Coq kernel map names (local and global variables)
 * to definitions and types. Here are a few utility functions for environments.
 *)
               
(*
 * This gets the global environment and the corresponding state:
 *)
let global_env () =
  let env = Global.env () in
  Evd.from_env env, env

(* Push a local binding to an environment *)
let push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env

(*
 * Push all local bindings in a product type to an environment, until the
 * conclusion is no longer a product type. Return the environment with all
 * of the bindings, and the conclusion type.
 *)
let rec push_all_locals_prod env typ sigma =
  match kind sigma typ with
  | Constr.Prod (n, t, b) ->
     push_all_locals_prod (push_local (n, t) env) b sigma
  | _ ->
     (env, typ)

(*
 * Like push_all_locals_prod, but for lambda terms
 *)
let rec push_all_locals_lambda env trm sigma =
  match kind sigma trm with
  | Constr.Lambda (n, t, b) ->
     push_all_locals_lambda (push_local (n, t) env) b sigma
  | _ ->
     (env, trm)

(*
 * Like push_all_locals_lambda, but only push the first nargs locals
 * If nargs is too large, then behave like push_all_locals_lambda
 *)
let rec push_n_locals_lambda nargs env trm sigma =
  if nargs <= 0 then
    (env, trm)
  else
    match kind sigma trm with
    | Constr.Lambda (n, t, b) ->
       push_n_locals_lambda (nargs - 1) (push_local (n, t) env) b sigma
    | _ ->
       env, trm

(* --- Definitions --- *)

(*
 * One of the coolest things about plugins is that you can use them
 * to define new terms. Here's a simplified (yes it looks terrifying,
 * but it really is simplified) function for defining new terms and storing them
 * in the global environment.
 *
 * This will only work if the term you produce
 * type checks in the end, so don't worry about accidentally proving False.
 * If you want to use the defined function later in your plugin, you
 * have to refresh the global environment by calling global_env () again,
 * but we don't need that in this plugin.
 *)
let define name body sigma =
  let udecl = UState.default_univ_decl in
  let scope = Locality.Global Locality.ImportDefaultBehavior in
  let kind = Decls.(IsDefinition Definition) in
  let cinfo = Declare.CInfo.make ~name ~typ:None () in
  let info = Declare.Info.make ~scope ~kind  ~udecl ~poly:false () in
  ignore (Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma)

(*
 * When you first start using a plugin, if you want to manipulate terms
 * in an interesting way, you need to move from the external representation
 * of terms to the internal representation of terms. This does that for you.
 *)
let internalize env trm sigma =
  Constrintern.interp_constr_evars env sigma trm

(* --- Equality --- *)
  
(*
 * This checks if there is any set of internal constraints in the state
 * such that trm1 and trm2 are definitionally equal in the current environment.
 *)
let equal env trm1 trm2 sigma =
  let opt = Reductionops.infer_conv env sigma trm1 trm2 in
  match opt with
  | Some sigma -> sigma, true
  | None -> sigma, false

(* --- Reduction --- *)

(*
 * Reduce/simplify a term
 *)
let reduce_term env trm sigma =
  Reductionops.nf_betaiotazeta env sigma trm
          
(*
 * Infer the type, then reduce/simplify the result
 *)
let reduce_type env trm sigma =
  let sigma, typ = Typing.type_of ~refresh:true env sigma trm in
  sigma, reduce_term env typ sigma

(* --- Functions and Application --- *)

(*
 * Get all arguments of a function, recursing into recursive applications
 * when functions have the form ((f x) y), to get both x and y, and so on.
 * Return list of arguments if it is a function application, and otherwise
 * return the empty list.
 *)
let all_args trm sigma =
  match kind sigma trm with
  | Constr.App (f, args) ->
     let rec unfold t =
       match kind sigma t with
       | Constr.App (f, args) ->
          List.append (unfold f) (Array.to_list args)
       | _ ->
          [t]
     in List.append (List.tl (unfold f)) (Array.to_list args)
  | _ ->
     []

(*
 * Like all_args, but rather than get [x y] for ((f x) y), get f,
 * the first function.
 *)
let rec first_fun trm sigma =
  match kind sigma trm with
  | Constr.App (f, args) ->
     first_fun f sigma
  | _ ->
     trm

(*
 * Make a list of n arguments, starting with the nth most recently bound
 * variable, and ending with the most recently bound variable
 *)
let mk_n_args n =
  List.map mkRel (List.rev (Collections.range 1 (n + 1)))

(*
 * Lift mkApp from arrays to lists
 *)
let mkAppl (f, args) = mkApp (f, Array.of_list args)

(* --- Inductive Types --- *)

(*
 * Map a function f on all constructors of inductive type ind.
 * Note that this does not handle mutually inductive types.
 *)
let map_constructors f env ind =
  let m = lookup_mind (fst (fst ind)) env in
  let b = m.mind_packets.(0) in
  let cs = b.mind_consnames in
  let ncons = Array.length cs in
  map_state
    (fun i -> f (mkConstructU ((fst ind, i), snd ind)))
    (Collections.range 1 (ncons + 1))
