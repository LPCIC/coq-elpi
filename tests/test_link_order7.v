From elpi Require Import elpi.

Elpi Db foo.db lp:{{
  pred p o:int.    
}}.

Elpi Command foo.
Elpi Accumulate Db foo.db.
Elpi Accumulate lp:{{
  main [].
  main [_] :- coq.say {std.findall (p _)}.
}}.
Elpi Typecheck.

Elpi Command add.
Elpi Accumulate Db foo.db.
Elpi Accumulate lp:{{
  main [ int M ] :-
    std.iota M L,
    std.forall L (x\ sigma N\
      new_int N,
      %coq.say "accum" N,
      coq.elpi.accumulate execution-site "foo.db" (clause _ _ (p N)) ).
}}.
Elpi Typecheck.
Elpi add 5.
Elpi add 5.
Elpi Print foo "elpi.tests/test_link_order7".
