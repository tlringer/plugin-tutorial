**Note: This branch is the answer guide. The main branch contains the exercises without any answers.**

More coming soon!

## Prerequisites

If you are not in my Proof Automation class, please first set up
Coq 8.16 and CoqIDE according to [these instructions](https://dependenttyp.es/classes/artifacts/6-languages.html). Please also set up emacs, and set up the plugin in the [parent directory](../) according to instructions in the corresponding [README](../README.md).

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
because you haven't implemented the command yet :).

## Getting Started

Open [Demo.v](./theories/Demo.v) in CoqIDE, and open [g_tuto2.mlg](./src/g_tuto2.mlg)
in Emacs alongside it. Follow the instructions in [g_tuto2.mlg](./src/g_tuto2.mlg)
to familiarize yourself with plugin development, then implement the `Swap` command.
Have fun!



