Declare ML Module "coq-elpi-tc.plugin".
From elpi Require Import elpi.

Elpi Db typeclass.db lp:{{

% predicate [typeclass Ctx V Inferred Expected Res] used to add new typeclass, with
% - [Ctx] is the context
% - [V] is the value to be coerced
% - [Inferred] is the type of [V]
% - [Expected] is the type [V] should be coerced to
% - [Res] is the result (of type [Expected])
% Be careful not to trigger typeclass as this may loop.
pred typeclass i:goal-ctx, i:term, i:term, i:term, o:term.

}}.

Elpi Tactic typeclass.
Elpi Accumulate lp:{{

solve (goal Ctx _ Ty Sol [trm V, trm VTy]) _ :- typeclass Ctx V VTy Ty Sol.

}}.
Elpi Accumulate Db typeclass.db.
Elpi Typecheck.
Elpi TypeclassFallbackTactic typeclass.

Class a (N: nat).
Instance b : a 3. Qed.
Instance c : a 4. Qed.

Goal a 4. apply _. Qed.