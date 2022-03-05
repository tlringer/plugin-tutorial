From Tuto1 Require Import Loader.
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

Map Old.list New.list := f.

(*
 * TODO test composing with the sub command
 *)

(*
 * TODO explain and test the swap command
 *)
