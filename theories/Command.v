From elpi Require Import elpi.

From Tuto1.Elpi Extra Dependency "common.elpi" as common.
From Tuto1.Elpi Extra Dependency "sub.elpi" as sub.
From Tuto1.Elpi Extra Dependency "counter.elpi" as counter.

Elpi Command My.
Elpi Accumulate lp:{{
  main [const-decl Name (some Body) _] :-
    coq.env.add-const Name Body _ @transparent! _.
  
  main _ :- coq.error {std.string.concat "\n" ["command syntax error", {usage-msg}]}.

  pred usage-msg o:string.
  usage-msg U :-
    std.string.concat "\n" [
      "usage: My Definition <coq definition>.",
      "", "",
    ] U.
}}.
Elpi Export My.

Elpi Command Count.
Elpi Accumulate File common.
Elpi Accumulate lp:{{
  main [AX, str "in", AT] :-
    parse-term AX X,
    parse-term AT T,

    % this will count the terms convertible to X,
    % but requires a small patch to Coq-Elpi, does not work yet
    % cf https://github.com/LPCIC/coq-elpi/issues/472
    % (pi t n n1\ fold-map t n X n1 :- coq.unify-eq t X ok, !, n1 is n + 1) => fold-map T 0 _ N,

    % this counts the terms syntactically equal to X
    (pi n n1\ fold-map X n X n1 :- n1 is n + 1) => fold-map T 0 _ N,
    coq.say N.
  
  main _ :- coq.error {std.string.concat "\n" ["command syntax error", {usage-msg}]}.

  pred usage-msg o:string.
  usage-msg U :-
    std.string.concat "\n" [
      "usage: Count <x> in <t>.",
      "", "",
    ] U.
}}.
Elpi Typecheck.
Elpi Export Count.

Elpi Command Count2.
Elpi Accumulate File common.
Elpi Accumulate File counter.
Elpi Accumulate lp:{{
  main [AX, str "in", AT] :-
    parse-term AX X,
    parse-term AT T,
    counter.init Cnt,
    (copy X X :- counter.incr Cnt) => copy T _,
    counter.get Cnt I,
    coq.say I.
  
  main _ :- coq.error {std.string.concat "\n" ["command syntax error", {usage-msg}]}.

  pred usage-msg o:string.
  usage-msg U :-
    std.string.concat "\n" [
      "usage: Count2 <x> in <t>.",
      "", "",
    ] U.
}}.
Elpi Typecheck.
Elpi Export Count2.

Elpi Command Sub.
Elpi Accumulate File common.
Elpi Accumulate File sub.
Elpi Accumulate lp:{{
  main Args :-
    (pi s\ parse-term (str s) _ :- (s = "with" ; s = "in"), !, fail) =>
      parse-arguments Args Ts Ts' X Name, !,
    copy-all Ts Ts' X X',
    coq.env.add-const Name X' _ @transparent! _.
  
  main _ :- coq.error {std.string.concat "\n" ["command syntax error", {usage-msg}]}.

  pred parse-arguments i:list argument, o:list term, o:list term, o:term, o:string.
  parse-arguments Args Ts Ts' PX Name :-
    parse-terms Args Ts [str "with"|Args'],
    parse-terms Args' Ts' [str "in", X, str "as", str Name],
    parse-term X PX,
    std.assert! (not (Name = "")) "non-empty name required".

  pred usage-msg o:string.
  usage-msg U :-
    std.string.concat "\n" [
      "usage: Sub <t_1> ... <t_n> with <t_1'> ... <t_n'> in <x> as <name>.",
      "", "",
    ] U.
}}.
Elpi Typecheck.
Elpi Export Sub.
