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

Map new_list_rect Old.list New.list := f.

Print new_list_rect.

(* (fun (P : Old.list T -> Type) (f : P (Old.nil T))
   (f0 : forall (t : T) (l : Old.list T), P l -> P (Old.cons T t l))
   (l : Old.list T) => Old.list_rect T P f f0 l)

(New.list T -> Type)

(fun (f : P (Old.nil T))
   (f0 : forall (t : T) (l : Old.list T), P l -> P (Old.cons T t l))
   (l : Old.list T) => Old.list_rect T P f f0 l)
(fun (f0 : forall (t : T) (l : Old.list T), P l -> P (Old.cons T t l))
   (l : Old.list T) => Old.list_rect T P f f0 l)


 *)

(*
 * TODO test composing with the sub command
 *)

(*
 * TODO explain and test the swap command
 *)
