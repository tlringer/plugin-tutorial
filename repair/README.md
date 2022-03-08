**Note: The answer guide is in another castle. By which I mean another branch. Specifically, the answer-guide branch.**

This is the second part of the plugin tutorial for my [Proof Automation](https://dependenttyp.es/classes/598sp2022.html) class! The relevant class information is [here](https://dependenttyp.es/classes/artifacts/16-repair.html). I recommend doing the tutorial in the parent directory first! You have already done this if you are in my class.

In this plugin, we're going to implement a kind of proof repair based on my thesis work.
Specifically, through a sequence of commands, we'll eventually implement a command that,
given the old and new versions of a datatype where one is the other with some constructors
swapped and/or renamed, like list and:

```
Module New.
Inductive list (T : Type) : Type :=
| cons : T -> list T -> list T
| nil : list T.
End New.
```

and given some map from old to new, like:


```
Program Definition f T : list T -> New.list T.
Proof.
  intros l. induction l.
  - apply New.nil.
  - apply New.cons; auto.
Defined.
```

automatically repairs functions and proofs about the old datatype, like:

```
Definition app (T : Type) (l m : list T) :=
  list_rect
    (fun _ => list T -> list T)
    (fun _ => m)
    (fun t l1 app_l1 _ => cons t (app_l1 m))   
    l
    m.

Lemma app_nil_r :
  forall (T : Type) (l : list T),
    app T l nil = l.
Proof.
  unfold app. simpl. intros T l. induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.
```

to functions and proofs about the new datatype:

```
Swapped app_swap := f app.
Swapped app_nil_r_swap := f app_nil_r.

(*
 * Test that we repaired app correctly:
 *)
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
 * Test that we repaired app_nil_r correctly:
 *)
Lemma app_nil_r_swapped :
  forall (T : Type) (l : New.list T),
    app_swap T l (New.nil T) = l.
Proof.
  exact app_nil_r_swap.
Qed.
```

## Prerequisites

If you are not in my Proof Automation class, please first set up
Coq 8.14 and CoqIDE according to [these instructions](https://dependenttyp.es/classes/artifacts/6-languages.html). Please also set up emacs, and set up the plugin in the [parent directory](../) according to instructions in the corresponding [README](../README.md).

If you are in my Proof Automation class, you have already done this :).

## Installation

Configure your opam environment:

```
opam switch 4.12.0
eval $(opam env)
```

Build the plugin:

```
make .merlin
make
```

You will get an error at the very end when it builds the Coq file, but that's just
because you haven't implemented the commands yet :).

## Getting Started

Open [Demo.v](./theories/Demo.v) in CoqIDE, and open [g_tuto2.mlg](./src/g_tuto2.mlg)
in Emacs alongside it. Follow the instructions in [g_tuto2.mlg](./src/g_tuto2.mlg)
to familiarize yourself with plugin development, then implement the commands.
Have fun!



