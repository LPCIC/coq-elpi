From elpi Require Import elpi.

Elpi Db my_db lp:{{
  pred graft_me o:int.

  :name "graft_me0"
  graft_me 0.
}}.

Elpi Command test_wanted_order.
Elpi Accumulate Db my_db.
Elpi Accumulate lp:{{
  main L1 :-
    std.findall (graft_me _) L2,
    std.forall2 L1 L2 (x\y\ sigma X\ graft_me X = y, int X = x).
}}.
Elpi Typecheck.

Elpi test_wanted_order 0.

Elpi Query lp:{{
  coq.elpi.accumulate _ "my_db" (clause "graft_me2" (after "graft_me0") (graft_me 2)).
}}.

Elpi test_wanted_order 0 2.

Elpi Query lp:{{
  coq.elpi.accumulate _ "my_db" (clause "graft_me1" (before "graft_me2") (graft_me 1)).
}}.

Elpi test_wanted_order 0 1 2.

Elpi Query lp:{{
  coq.elpi.accumulate _ "my_db" (clause _ (replace "graft_me2") (graft_me 3)).
}}.

Elpi test_wanted_order 0 1 3.
