From Tuto2 Require Import Loader.
Require Import Coq.Program.Tactics.

(* --- Datatypes --- *)

(*
 * Let's define some datatypes. First, old and new list:
 *)

Print list.

Module New.
Inductive list (T : Type) : Type :=
| cons : T -> list T -> list T
| nil : list T.
End New.

(*
 * Second, old and new vector:
 *)
Inductive vector (A : Type) : nat -> Type :=
| nilV : vector A 0
| consV : A -> forall n : nat, vector A n -> vector A (S n).

Inductive hector (A : Type) : nat -> Type :=
| consH : A -> forall n : nat, hector A n -> hector A (S n)
| nilH : hector A 0.

(*
 * Third, old and new Enum:
 *)
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

(* --- Maps --- *)

(*
 * Now let's define some maps between versions of these datatypes.
 * These are what we'll pass to our repair command.
 *)

Program Definition f T : list T -> New.list T.
Proof.
  intros l. induction l.
  - apply New.nil.
  - apply New.cons; auto.
Defined.

Program Definition g T n : vector T n -> hector T n.
Proof.
  intros v. induction v.
  - apply nilH.
  - apply consH; auto.
Defined.

Program Definition Enum_Enum' : Enum -> Enum'.
Proof.
  intros e. induction e.
  - apply e5'.
  - apply e2'.
  - apply e4'.
  - apply e1'.
  - apply e3'.
Defined.

(* --- Exercise 1 tests! --- *)

(*
 * Cool, OK! The first thing we'll do is extract the datatypes from the maps
 * we've just defined.
 *)

(* Test 1: *)
Display Inductives f. (* <- should print "This function maps: list -> New.list" *)

(* Test 2: *)
Display Inductives g. (* <- should print "This function maps: vector -> hector" *)

(* Test 3: *)
Display Inductives Enum_Enum'. (* <- should print "This function maps: Enum -> Enum'" *)

(*
 * If these pass, congrats! You've already done something pretty cool IMO.
 * But I'm biased.
 *)

(* --- Exercise 2 tests! --- *)

(*
 * Next, let's extract the constructor maps from those maps.
 *)

(* Test 4: *)
Display Map f. (* <- should print "This function maps: @nil -> New.nil, @cons -> New.cons" *)

(* Test 5: *)
Display Map g. (* <- should print "This function maps: nilV -> nilH, consV -> consH" *)

(* Test 6: *)
Display Map Enum_Enum'. (* <- should print "This function maps: e1 -> e5', e2 -> e2', e3 -> e4', e4 -> e1', e5 -> e3'" *)

(*
 * Nice! This is already all of the interesting work needed to implement repair for
 * particular instances of each datatype.
 *)

(* --- Exercise 3 tests! --- *)

(*
 * Now the trickiest part, which is defining the updated induction principles, so that we can
 * repair induction principles by just substituting in the new one.
 *)
Define Map new_list := f.
Define Map new_vect := g.
Define Map new_enum := Enum_Enum'.

(* Test 7 *)
Lemma new_list_rect_OK:
  forall (A : Type) (P : New.list A -> Type),
    P (New.nil A) ->
    (forall (a : A) (l : New.list A), P l -> P (New.cons A a l)) ->
    forall l : New.list A, P l.
Proof.
  exact new_list_rect.
Qed.

(* Test 8 *)
Lemma new_vect_rect_OK:
  forall (A : Type) (P : forall n : nat, hector A n -> Type),
    P 0 (nilH A) ->
    (forall (a : A) (n : nat) (v : hector A n),
    P n v -> P (S n) (consH A a n v)) ->
    forall (n : nat) (v : hector A n), P n v.
Proof.
  exact new_vect_rect.
Qed.

Check new_enum_rect.

(* Test 9 *)
Lemma new_enum_rect_OK:
  forall (P : Enum' -> Type),
    P e5' ->
    P e2' ->
    P e4' ->
    P e1' ->
    P e3' ->
    forall e : Enum', P e.
Proof.
  exact new_enum_rect.
Qed.

(*
 * Mazal Tov!
 *)

(* --- Profit! --- *)

(*
 * Now that you've done all of that, we can use the combined results of this
 * and the sub implementation from the last tutorial to repair functions and proofs.
 * Let's repair a function first:
 *)

Definition app (T : Type) (l m : list T) :=
  list_rect
    (fun _ => list T -> list T)
    (fun _ => m)
    (fun t l1 app_l1 _ => cons t (app_l1 m))   
    l
    m. 

Swapped app_swap := f app.

(* Test 10: *)
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
 * Now, let's repair a proof!
 *
 * Note that we don't yet recursively repair constants---my thesis work does :)
 * but this requires some caching and tracking state that is annoying,
 * so I omit it here for now. Instead, I inline app at the beginning by unfolding it.
 *) 
Lemma app_nil_r :
  forall (T : Type) (l : list T),
    app T l nil = l.
Proof.
  unfold app. simpl. intros T l. induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Swapped app_nil_r_swap := f app_nil_r.

(* Test 11: *)
Lemma app_nil_r_swapped :
  forall (T : Type) (l : New.list T),
    app_swap T l (New.nil T) = l.
Proof.
  exact app_nil_r_swap.
Qed.

(* yayyy *)