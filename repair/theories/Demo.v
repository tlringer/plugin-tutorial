
From Tuto2 Require Import Loader.

(*
 * TODO explain and test the map command
 *)
Module New.
Inductive list (T : Type) : Type :=
| cons : T -> list T -> list T
| nil : list T.
End New.

Require Import Coq.Program.Tactics.
Program Definition f T : list T -> New.list T.
Proof.
  intros l. induction l.
  - apply New.nil.
  - apply New.cons; auto.
Defined.

Require Import Vector.
Check Vector.t_rect.

Print Vector.t.


Inductive vector (A : Type) : nat -> Type :=
| nilV : vector A 0 | consV : A -> forall n : nat, vector A n -> vector A (S n).

Inductive hector (A : Type) : nat -> Type :=
| consH : A -> forall n : nat, hector A n -> hector A (S n) | nilH : hector A 0.

Program Definition g T n : vector T n -> hector T n.
Proof.
  intros v. induction v.
  - apply nilH.
  - apply consH; auto.
Defined.

Inductive Enum : Set :=
| e1 : Enum
| e2 : Enum
| e3 : Enum
| e4 : Enum
| e5 : Enum.

Inductive Enum' : Set :=
| e1' : Enum'
| e2' : Enum'
| e3' : Enum'
| e4' : Enum'
| e5' : Enum'.

Program Definition Enum_Enum' : Enum -> Enum'.
Proof.
  intros e. induction e.
  - apply e5'.
  - apply e2'.
  - apply e4'.
  - apply e1'.
  - apply e3'.
Defined.

Display Inductives f.
Display Inductives g.
Check Enum'_rect.
Display Inductives Enum_Enum'.
Display Map Enum_Enum'.
Define Map new_enum := Enum_Enum'.

Display Map g.

Define Map new_vect := g.

Display Map f.

Define Map new_list := f.

Print new_list_rect.

Require Import List.
Print app.

(*
 * TODO test composing with the sub command at each step, so students see progress
 *)

Require Import Tuto1.Loader.

Sub list @nil @cons list_rect with New.list New.nil New.cons new_list_rect in
  (fun (T : Type) (l m : list T) =>
    list_rect
      (fun _ => list T -> list T)
      (fun _ => m)
      (fun t l1 app_l1 _ => cons t (app_l1 m))   
      l
      m)
  as appy.

Print appy.


(* TODO some proofs etc *)

(* TODO try with larger inductive types etc, more swaps, to make sure *)


(*
 * TODO explain and test the swap command
 *)

Print list.
Print New.list.

Definition app (T : Type) (l m : list T) :=
  list_rect
    (fun _ => list T -> list T)
    (fun _ => m)
    (fun t l1 app_l1 _ => t :: app_l1 m)   
    l
    m. 

Swapped app_swap := f app.

Check app.
Print list.
Check app_swap.
Print New.list.

Lemma app_swap_OK:
  forall (T : Type) (l m : list T),
    f T (app T l m) = app_swap T (f T l) (f T m).
Proof.
  intros T l m. induction l.
  - reflexivity.
  - replace (app_swap T (f T (a :: l)) (f T m))
       with (New.cons T a (app_swap T (f T l) (f T m)))
         by reflexivity.
    rewrite <- IHl.
    reflexivity.
Qed.

(*
 * Note that we don't yet recursively swap constants---my thesis work does :)
 * but this requires some caching and tracking state that is annoying,
 * so I omit it here for now. Instead, I inline app at the beginning.
 *) 
Lemma app_nil_r :
  forall (T : Type) (l : list T), app T l nil = l.
Proof.
  unfold app. simpl. intros T l. induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Swapped app_nil_r_swap := f app_nil_r.

Lemma app_nil_r_swapped :
  forall (T : Type) (l : New.list T), app_swap T l (New.nil T) = l.
Proof.
  apply app_nil_r_swap.
Qed.

(* yayyy *)