From elpi Require Import elpi.

(** derive.projK generates a projection for each argument of each constructor.
    the projection is expected to be applied to an explicit constructor. *)

Elpi Db derive.projK.db " type projK-db @gref -> int -> term -> prop. ".

Elpi Command derive.projK.
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File "derive/projK.elpi".
Elpi Accumulate "
  main [str I, str O] :- !, derive.projK.main I O _.
  main [str I] :- !, derive.projK.main I ""proj"" _.
  main _ :- usage.

  usage :- coq.error ""Usage: derive.projK <inductive type name> [<output prefix>]"".
".
Elpi Typecheck.
