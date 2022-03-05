
From Tuto2 Require Import Loader.

(*
 * TODO explain and test the map command
 *)
Module Old.
Inductive list (T : Type) : Type :=
| nil : list T
| cons : T -> list T -> list T.
End Old.

Module New.
Inductive list (T : Type) : Type :=
| cons : T -> list T -> list T
| nil : list T.
End New.

Require Import Coq.Program.Tactics.
Program Definition f T : Old.list T -> New.list T.
Proof.
  intros l. induction l.
  - apply New.nil.
  - apply New.cons; auto.
Defined.

Map new_list_rect Old.list New.list := f.

Print new_list_rect.

Require Import List.
Print app.

(*
 * TODO test composing with the sub command
 *)

Require Import Tuto1.Loader.

Sub Old.list Old.nil Old.cons Old.list_rect with New.list New.nil New.cons new_list_rect in
  (fun (T : Type) (l m : Old.list T) =>
    Old.list_rect
      T
      (fun _ => Old.list T -> Old.list T)
      (fun _ => m)
      (fun t l1 app_l1 _ => Old.cons T t (app_l1 m))   
      l
      m)
  as app.

Print app.


(* TODO some proofs etc *)

(* TODO try with larger inductive types etc, more swaps, to make sure *)


(*
 * TODO explain and test the swap command
 *)
