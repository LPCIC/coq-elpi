From elpi Require Import elpi.

Elpi Db foo.db lp:{{ pred p o:int. }}.

Elpi File common.code lp:{{
  pred succ i:int, o:int.
  succ N M :- M is N + 1.
}}.

Set Warnings "+elpi".

Fail Elpi Accumulate foo.db lp:{{

p X :- succ 1 X. % type of succ not defined

}}.

Elpi Accumulate foo.db File Signature common.code.

Elpi Accumulate foo.db lp:{{

p X :- succ 1 X.

}}.

Elpi Command foo.
Elpi Accumulate File common.code.
Elpi Accumulate Db foo.db.
Elpi Accumulate lp:{{
  main [] :-
    std.findall (succ 1 _) L1, std.assert! (L1 = [succ 1 2]) "oops",
    std.findall (p _) L2, std.assert! (L2 = [p 2]) "oops".
}}.
Elpi foo.
