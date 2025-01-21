From elpi Require Import elpi.

Definition myType := Type.
Variant indd : myType := Indd : indd.

Definition myType_R u v := u -> v -> Type.

Elpi Command foo.
Elpi Accumulate "
main _ :-
  std.assert-ok! (coq.typecheck-indt-decl (inductive ""indt_R"" tt
    (arity {{ myType_R indd indd }})
    c1 \
      [ constructor ""Indd_R"" (arity {{ lp:c1 Indd Indd }}) ])) ""error"".
".
Elpi foo.
