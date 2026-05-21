From elpi Require Import elpi.

Elpi Command cmd.
Elpi Db db lp:{{
pred db? o:term.
}}.

Elpi Accumulate Db db.

#[synterp]
Elpi Accumulate cmd lp:{{
main _ :-
  coq.env.begin-section "Dummy",
  coq.env.end-section.
}}.
Elpi Accumulate cmd lp:{{
main _ :-
  coq.env.begin-section "Dummy",
  coq.env.add-section-variable "T" _ {{ Type }} T,
  coq.elpi.accumulate _ "db" (clause _ _ (db? (global (const T)))),
  coq.env.end-section.
}}.

Elpi cmd.

Section Dummy.
Variable (T : Type).

Fail Elpi Query cmd lp:{{
db? {{ T }}.
}}.

End Dummy.
