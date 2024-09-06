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
    std.map L (x\r\sigma N\
      new_int N,
      r =  (clause _ _ (p N))) C,
    coq.elpi.accumulate-clauses current "foo.db" C.
}}.
Elpi Typecheck.
Elpi add 10.
Elpi Print foo "elpi.tests/test_link_order2".

