From elpi Require Import elpi.

(* Test that Elpi database clauses are correctly substituted when a
   module type is sealed into a concrete module, per issue #989. *)

Elpi Db known.db lp:{{
  pred known o:gref.
}}.

Elpi Command register.
Elpi Accumulate Db known.db.
Elpi Accumulate lp:{{
  main [str S] :- coq.locate S GR,
    coq.elpi.accumulate _ "known.db" (clause _ _ (known GR)).
}}.

Elpi Command check.
Elpi Accumulate Db known.db.
Elpi Accumulate lp:{{
  main [str S] :-
    coq.locate S GR,
    std.assert! (known GR) "gref not registered after substitution".
}}.

(* Register an axiom inside a module type, then seal and verify the
   clause refers to the sealed module's definition rather than the
   stale module-type axiom. *)
Module Type MT.
  Parameter bar : nat.
  Elpi register "bar".
End MT.

Module M : MT.
  Definition bar := 42.
End M.

Elpi check "M.bar".

(* Also check that sealing via a functor-parameter signature works:
   inside the functor body, the parameter's gref is known. *)
Module Type DEP_SIG.
  Parameter dep : nat.
  Elpi register "dep".
End DEP_SIG.

Module F (D : DEP_SIG).
  Import D.
  Elpi check "dep".
End F.
