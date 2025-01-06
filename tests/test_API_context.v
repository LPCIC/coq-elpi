From elpi Require Import elpi.

Elpi Command context.
Elpi Accumulate lp:{{
  main [ctx-decl Ctx] :- !,
    coq.env.add-context Ctx.
}}.

Section CA.
  Elpi context Context (a : nat) [b : nat] {c : nat} (d : nat := 3) (e := 4).
  Check eq_refl : d = 3.
  Check eq_refl : e = 4.
  Definition foo := a + b + c + d + e.
End CA.
Print foo.

Elpi Query lp:{{
  coq.arguments.implicit {coq.locate "foo"} [[explicit, implicit, maximal]].
}}.
