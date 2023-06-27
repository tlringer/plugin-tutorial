From elpi Require Import elpi.

From Tuto1.Elpi Extra Dependency "tuto1.elpi" as tuto1.

Elpi Command Sub.
Elpi Accumulate File tuto1.
Elpi Accumulate lp:{{
  main Args :-
    parse-arguments Args Ts Ts' X Name, !,
    copy-all Ts Ts' X X',
    coq.env.add-const Name X' _ @transparent! _.
  
  main _ :- coq.error {std.string.concat "\n" ["command syntax error", {usage-msg}]}.

  pred usage-msg o:string.
  usage-msg U :-
    std.string.concat "\n" [
      "usage: Sub <t_1> ... <t_n> with <t_1'> ... <t_n'> in <x> as <name>.",
      "", "",
    ] U.
}}.
Elpi Typecheck.
Elpi Export Sub.
