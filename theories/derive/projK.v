From elpi Require Import elpi.

(** derive.projK generates a projection for each argument of each constructor.
    the projection is expected to be applied to an explicit constructor. *)

Elpi Command derive.projK.
Elpi Accumulate File "elpi-derive-projK.elpi".
Elpi Accumulate "
  main [str I] :- !,
    coq-locate I T,
    if (T = indt GR) (derive-projK GR) usage.
  main _ :- usage.

  usage :- coq-error ""Usage: derive.projK <inductive type name>"".

  typecheck.
".
Elpi Query "typecheck".
