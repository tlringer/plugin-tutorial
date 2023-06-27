From Tuto1 Require Import Loader.

(*** Defining terms ***)

(*
 * MyDefine works a lot like Definition.
 * Some examples:
 *)
My Definition n := 1.
Print n.

My Definition f := (fun (x : Type) => x).
Print f.

My Definition definition := 5.
Print definition.

My Definition foo := (fun (T : Type) => forall (P : T -> Type) (t : T), P t).
Print foo.

(*** Reasoning about terms ***)

(*
 * The Count command counts the occurrences
 * definitionally equal to the first term
 * inside of the second term. This makes some
 * simplifying assumptions about the format of terms.
 *)
Count2 nat in (foo nat). (* 1 *)
Count2 nat in (fun (n : nat) => n). (* 1 *)

(*
 * Since it's definitional equality, we don't need
 * to rely on syntax. We can define our own constant
 * wrapping nat, for example, and get the same behavior:
 *)
Definition my_nat := nat.
Count2 my_nat in (foo nat). (* 1 *)

(*
 * Similarly, since 8 is sugar for S (S (S ... 0)), 
 * we can count the occurrences of S in 8 to get 8.
 * Or, we can pass in (fun (n : nat) => 1 + n),
 * which is definitionally equal to S.
 *)
Count2 S in (8). (* 8 *)
Count2 (fun (n : nat) => 1 + n) in (8). (* 8 *)

(*** Both together ***)

(*
 * The fun part! The substitution command you will implement.
 *)

(*
 * Turn 4 (sugar for (S (S (S (S 0))))) into
 * [1; 1; 1; 1] (sugar for (cons 1 (cons 1 ... nil))).
 * Do this by substituting the constructors of nat
 * with the constructors of lists.  
 *)
Sub O S with (@nil nat) (cons 1) in (4) as list_4.
Lemma test1:
  list_4 = (cons 1 (cons 1 (cons 1 (cons 1 nil)))).
Proof.
  reflexivity.
Qed.

(*
 * Convert unary natural numbers to binary numbers!
 *)
Require Import Coq.NArith.BinNatDef Coq.NArith.BinNat.
Sub O S with N.zero N.succ in (256) as two_fifty_six_binary.
Lemma test2:
  two_fifty_six_binary = 256%N.
Proof.
  reflexivity.
Qed.

(*
 * Convert the addition function of unary into an addition
 * function defined over binary!
 *)
Sub nat nat_rec O S with N.t N.peano_rec N.zero N.succ in
  (fun (n m : nat) =>
     nat_rec
       (fun _ => nat -> nat)
       (fun m => m)
       (fun p add_p m => S (add_p m))
       n
       m)
   as add_bin.

Lemma test3:
  add_bin 128%N 12%N = 140%N.
Proof.
  reflexivity.
Qed.
