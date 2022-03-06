(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 * Utilities for the state monad were moved to stateutils.ml/stateutils.mli
 * Utilities for inductive types & proofs are in induction.ml/induction.mli
 *)

open EConstr
open Environ

(* --- Debugging --- *)

(*
 * A convenient function for printing terms
 *)
let print env t sigma = Printer.pr_econstr_env env sigma t

(*
 * Same as above, but output to Coq rather than returning a Pp.t object
 *)
let print_message env t sigma = Feedback.msg_notice (print env t sigma) 

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

(* Push a let-in definition to an environment *)
let push_let_in (n, e, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalDef(n, e, t)) env
  
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

(*
 * Reconstruct a lambda term from an environment, removing those bindings
 * from the environment. Stop when there are n bindings left in the environment.
 *)
let rec reconstruct_lambda_n i env b =
  if nb_rel env = i then
    env, b
  else
    let (n, _, t) = Context.Rel.Declaration.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_lambda_n i env' (mkLambda (n, (EConstr.of_constr t), b))

(* Reconstruct a lambda from an environment, popping all local variables *)
let reconstruct_lambda = reconstruct_lambda_n 0

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

(*
 * Look up a definition from an environment
 *)
let lookup_definition env def sigma =
  match kind sigma def with
  | Constr.Const (c, u) ->
     let cb = lookup_constant c env in
     (match Global.body_of_constant_body Library.indirect_accessor cb with
      | Some(e, _, _) -> EConstr.of_constr e
      | None -> failwith "This term has no value")
  | _ -> failwith "not a definition"

(* Fully lookup a def in env, but return the term if it is not a definition *)
let rec unwrap_definition env trm sigma =
  try
    let body = lookup_definition env trm sigma in
    if Constr.equal (EConstr.to_constr sigma body) (EConstr.to_constr sigma trm) then
      trm
    else
      unwrap_definition env body sigma
  with _ ->
    trm

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
 * Fully normalize a term (apply all possible reduction rules)
 *)
let normalize_term env trm sigma =
  Reductionops.nf_all env sigma trm

(*
 * Reduce/simplify a term
 *)
let reduce_term env trm sigma =
  Reductionops.nf_betaiotazeta env sigma trm

(*
 * Infer the type, then normalize the result
 *)
let normalize_type env trm sigma =
  let sigma, typ = Typing.type_of ~refresh:true env sigma trm in
  sigma, normalize_term env typ sigma

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

(*
 * Apply, then reduce
 * If args are empty, then return f
 *)
let apply_reduce reducer env f args sigma =
  if List.length args = 0 then
    f
  else
    reducer env (mkAppl (f, args)) sigma

(*
 * Get the arity of the function/product
 *)
let rec arity f sigma =
  match kind sigma f with
  | Constr.Lambda (_, _, b) ->
     1 + arity b sigma
  | Constr.Prod (_, _, b) ->
     1 + arity b sigma
  | _ ->
     0

(*
 * Expand a partially applied curried function to take all arguments
 * explicitly. For example, (add 0) becomes (fun n => add 0 n).
 * This is known as eta-expansion.
 *)
let expand_eta env trm sigma =
  let shift_by n trm sigma =
    EConstr.of_constr (Constr.liftn n 0 (EConstr.to_constr sigma trm))
  in
  let sigma, typ = reduce_type env trm sigma in
  let curried_args = mk_n_args (arity typ sigma) in
  let _, expanded =
    reconstruct_lambda
      (fst (push_all_locals_prod (Environ.empty_env) typ sigma))
      (mkAppl (shift_by (List.length curried_args) trm sigma, curried_args))
  in sigma, expanded

(*
 * Return true if f is exactly the same as (syntactically) the first
 * function inside of term, and term is an application.
 *)
let applies f trm sigma =
  match kind sigma trm with
  | Constr.App (g, _) ->
     Constr.equal (EConstr.to_constr sigma f) (EConstr.to_constr sigma g)
  | _ ->
     false

(*
 * Check if trm' is exactly the same as (syntactically) the first
 * function inside of trm and trm is an application, or if trm' and trm
 * are equal to each other.
 *
 * If true, return Some list containing all arguments args to trm' (empty if
 * trm is exactly trm') such that trm' args = trm. Otherwise, return None.
 *)
let is_or_applies trm' trm sigma =
  let can_unify =
    applies trm' trm sigma ||
    Constr.equal (EConstr.to_constr sigma trm') (EConstr.to_constr sigma trm)
  in if can_unify then Some (all_args trm sigma) else None
