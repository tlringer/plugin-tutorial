(*
 * Utilities for dealing with Coq terms, to abstract away some pain for students
 * Utilities for the state monad were moved to stateutils.ml/stateutils.mli
 *)

open Evd
open Environ
open Constrexpr
open Stateutils

(* --- Debugging --- *)

(*
 * A convenient function for printing terms
 *)
val print :
  env -> (* environment *)
  EConstr.t -> (* term *)
  evar_map -> (* state *)
  Pp.t (* Coq printing object, to use with Feedback.msg_notice and so on *)

(*
 * Same as above, but output to Coq rather than returning a Pp.t object
 *)
val print_message :
  env -> (* environment *)
  EConstr.t -> (* term *)
  evar_map -> (* state *)
  unit
 
(* --- Environments --- *)

(*
 * Environments in the Coq kernel map names (local and global variables)
 * to definitions and types. Here are a few utility functions for environments.
 *)

(*
 * This gets the global environment the corresponding state:
 *)
val global_env : unit -> env state

(* Push a local binding to an environment *)
val push_local :
  Names.Name.t Context.binder_annot * EConstr.t -> (* id, typ *)
  env -> (* environment *)
  env (* updated environment *)

(* Push a let expression *)
val push_let_in :
  Names.Name.t Context.binder_annot * EConstr.t * EConstr.t -> (*id, trm, typ*)
  env -> (* environment *)
  env (* updated environment *)
  
(*
 * Push all local bindings in a product type to an environment, until the
 * conclusion is no longer a product type. Return the environment with all
 * of the bindings, and the conclusion type.
 *)
val push_all_locals_prod :
  env -> (* environment *)
  EConstr.t -> (* product type *)
  evar_map -> (* state *)
  env * EConstr.t (* updated environment, and conclusion of the product type *)
  
(*
 * Like push_all_locals_prod, but for lambda terms
 *)
val push_all_locals_lambda :
  env -> (* environment *)
  EConstr.t -> (* lambda term *)
  evar_map -> (* state *)
  env * EConstr.t (* updated environment, and conclusion of the lambda term *)

(*
 * Like push_all_locals_lambda, but only push the first n locals
 * If n is too large, then behave like push_all_locals_lambda
 *)
val push_n_locals_lambda :
  int -> (* number of locals to push *)
  env -> (* environment *)
  EConstr.t -> (* lambda term *)
  evar_map -> (* state *)
  env * EConstr.t (* updated environment, and updated lambda term *)

(*
 * Reconstruct a lambda term from an environment, removing those bindings
 * from the environment. Stop when there are n bindings left in the environment.
 *)
val reconstruct_lambda_n :
  int -> (* number of locals that should be left in the env at the end *)
  env -> (* environment *)
  EConstr.t -> (* body of the lambda to construct *)
  env * EConstr.t (* updated environment, and the resulting lambda term *)

(*
 * Reconstruct a lambda from an environment, popping all local variables
 *)
val reconstruct_lambda :
  env -> (* environment *)
  EConstr.t -> (* body of the lambda to construct *)
  env * EConstr.t (* updated environment, and the resulting lambda term *)

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
val define :
  Names.Id.t -> (* name of the new term *)
  EConstr.t -> (* the new term *)
  evar_map -> (* state *)
  unit

(*
 * When you first start using a plugin, if you want to manipulate terms
 * in an interesting way, you need to move from the external representation
 * of terms to the internal representation of terms. This does that for you.
 *)
val internalize :
  env -> (* environment *)
  constr_expr -> (* external representation *)
  evar_map -> (* state *)
  EConstr.t state (* stateful internal representation *)

(*
 * Fully look up a definition in an environment, recursively looking
 * up aliased terms. Return the original term if it is not a definition.
 *)
val unwrap_definition :
  env -> (* environment *)
  EConstr.t -> (* constant term *)
  evar_map -> (* state *)
  EConstr.t (* body of definition of term *)
  
(* --- Equality --- *)
  
(*
 * This checks if there is any set of internal constraints in the state
 * such that trm1 and trm2 are definitionally equal in the current environment.
 *)
val equal :
  env -> (* environment *)
  EConstr.t -> (* trm1 *)
  EConstr.t -> (* trm2 *)
  evar_map -> (* state *)
  bool state (* stateful (t1 = t2) *)

(* --- Reduction --- *)

(*
 * Fully normalize a term (apply all possible reduction rules)
 *)
val normalize_term :
  env -> (* environment *)
  EConstr.t -> (* term *)
  evar_map -> (* state *)
  EConstr.t (* normalized term *)
  
(*
 * Reduce/simplify a term
 * This defaults to the following reduction rules in this case:
 * 1. beta-reduction (applying functions to arguments)
 * 2. iota-reduction (simplifying induction principle applications)
 * 3. zeta-reduction (simplifying let expressions)
 *)
val reduce_term :
  env -> (* environment *)
  EConstr.t -> (* term *)
  evar_map -> (* state *)
  EConstr.t (* reduced term *)

(*
 * Infer the type, then normalize the result
 *)
val normalize_type :
  env -> (* environment *)
  EConstr.t -> (* term *)
  evar_map -> (* state *)
  EConstr.t state (* stateful normalized type of term *)
  
(*
 * Infer the type, then reduce/simplify the result
 *)
val reduce_type :
  env -> (* environment *)
  EConstr.t -> (* term *)
  evar_map -> (* state *)
  EConstr.t state (* stateful reduced type of term *)
  
(* --- Functions and Application --- *)

(*
 * Get all arguments of a function, recursing into recursive applications
 * when functions have the form ((f x) y), to get both x and y, and so on.
 * Return a list of arguments if it is a function application, and otherwise
 * return the empty list.
 *)
val all_args :
  EConstr.t -> (* term *)
  evar_map -> (* state *)
  EConstr.t list (* list of all arguments *)

(*
 * Like all_args, but rather than get [x y] for ((f x) y), get f,
 * the first function.
 *)
val first_fun :
  EConstr.t -> (* term *)
  evar_map -> (* state *)
  EConstr.t (* first function *)

(*
 * Make a list of n arguments, starting with the nth most recently bound
 * variable, and ending with the most recently bound variable.
 *)
val mk_n_args :
  int -> (* number of arguments *)
  EConstr.t list (* list of arguments *)

(*
 * Lift Coq's mkApp from arrays to lists
 *)
val mkAppl :
  (EConstr.t * EConstr.t list) -> (* (f, args) *)
  EConstr.t (* mkApp (f, Array.of_list args) *)

(*
 * Apply f to args, then reduce the result using the supplied reduction function
 * If args are empty, just return f
 *)
val apply_reduce :
  (env -> EConstr.t -> evar_map -> EConstr.t) -> (* reduction function *)
  env -> (* environment *)
  EConstr.t -> (* f *)
  EConstr.t list -> (* args *)
  evar_map -> (* state *)
  EConstr.t (* reduced (f args), or f is args is empty *)

(*
 * Get the arity (number of total possible arguments) of the function/product
 *)
val arity :
  EConstr.t -> (* function/product *)
  evar_map -> (* state *)
  int (* arity of function/product *)

(*
 * Expand a partially applied curried function to take all arguments
 * explicitly. For example, (add 0) becomes (fun n => add 0 n).
 * This is known as eta-expansion.
 *)
val expand_eta :
  env -> (* environment *)
  EConstr.t -> (* term *)
  evar_map -> (* state *)
  EConstr.t state (* stateful eta-expanded term *)

(*
 * Check  if the second term is either exactly (syntactically)
 * the same as the first term, or if the second term applies the first
 * term exactly to some arguments. 
 *
 * If true, return Some list containing all arguments args to trm' (empty if
 * trm is exactly trm') such that trm' args = trm. Otherwise, return None.
 *)
val is_or_applies :
  EConstr.t -> (* trm' *)
  EConstr.t -> (* trm *)
  evar_map -> (* state *)
  (EConstr.t list) option (* Some args or None *)
