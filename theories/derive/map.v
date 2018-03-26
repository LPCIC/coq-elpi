Require Import elpi.

Elpi Db derive.map.db " type map-db term -> term -> term -> prop. ".

(** A map over a container. If the container has a parameter that is
    used to type an index, then such parameter is not mapped. E.g.
      Inductive I A B : A -> Type := K : forall a b, I A B a.
    Elpi derive.map I.
      Definition I_map A B C (f : B -> C) a : I A B a -> I A B a.
*)
Elpi Command derive.map.
Elpi Accumulate Db derive.map.db.
Elpi Accumulate File "derive/map.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, derive.map.main I O _.
  main [str I] :- !,
    coq.locate I T, term->gr T GR, O is {coq.gr->id GR} ^ ""_map"", derive.map.main I O _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.map <inductive type name> [<output name>]"".
".  
Elpi Typecheck.
