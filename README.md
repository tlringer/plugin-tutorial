**Note: The answer guide is in another castle. By which I mean another branch. Specifically, the answer-guide branch.**

This is a fun plugin tutorial for my [Proof Automation](https://dependenttyp.es/classes/598sp2022.html) class! The relevant class information is [here](https://dependenttyp.es/classes/artifacts/14-mixed.html). There is a second tutorial in the [repair directory](./repair) for a subsequent class, which builds on this. I recommend doing this tutorial first!

This tutorial helps familiarize people with plugin development. The goal
is to implement a command with this syntax:

```
Sub src1 src2 ... srcn with dst1 dst2 ... dstn in trm as name. 
```

This command substitutes each subterm of `trm` that is definitionally equal to `srci`
with the corresponding term `desti`. Some tests in [Demo.v](./theories/Demo.v) that pass
after implementing `Sub` correctly:

```
(*
 * Turn 4 (sugar for (S (S (S (S 0))))) into
 * [1; 1; 1; 1] (sugar for (cons 1 (cons 1 ... nil))).
 * Do this by substituting the constructors of nat
 * with the constructors of lists.
 *)
Sub O S with (@nil nat) (cons 1) in 4 as list_4.
Lemma test1:
  list_4 = (cons 1 (cons 1 (cons 1 (cons 1 nil)))).
Proof.
  reflexivity.
Qed.

(*
 * Convert unary natural numbers to binary numbers!
 *)
Require Import Coq.NArith.BinNatDef Coq.NArith.BinNat.
Sub O S with N.zero N.succ in 256 as two_fifty_six_binary.
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
```

## Prerequisites

If you are not in my Proof Automation class, please first set up
Coq 8.14 and CoqIDE according to [these instructions](https://dependenttyp.es/classes/artifacts/6-languages.html). Please also set up emacs.

If you are in my Proof Automation class, you have already done this :).

## Installation

Configure your opam environment:

```
opam switch 4.12.0
eval $(opam env)
```

Set up OCaml development tools for plugin development:

```
opam install merlin
opam install tuareg
opam user-setup install
eval $(opam env)
```

Add this line to your .emacs to configure emacs to use those development tools:

```
(add-to-list 'auto-mode-alist '("\\.mlg$"      . tuareg-mode) t)
```

Build the plugin:

```
make .merlin
make
```

You will get an error at the very end when it builds the Coq file, but that's just
because you haven't implemented the command yet :).

## Getting Started

Open [Demo.v](./theories/Demo.v) in CoqIDE, and open [g_tuto1.mlg](./src/g_tuto1.mlg)
in Emacs alongside it. Follow the instructions in [g_tuto1.mlg](./src/g_tuto1.mlg)
to familiarize yourself with plugin development, then implement the `Sub` command.
Have fun!



