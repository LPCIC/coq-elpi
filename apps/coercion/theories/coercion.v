Declare ML Module "rocq-elpi.coercion".
From elpi Require Import elpi.

Elpi Db coercion.db lp:{{

% predicate [coercion Ctx V Inferred Expected Res] used to add new coercion, with
% - [Ctx] is the context
% - [V] is the value to be coerced
% - [Inferred] is the type of [V]
% - [Expected] is the type [V] should be coerced to
% - [Res] is the result (of type [Expected])
% Be careful not to trigger coercion as this may loop.
pred coercion i:goal-ctx, i:term, i:term, i:term, o:term.

}}.

Elpi Tactic coercion.
Elpi Accumulate Db Header coercion.db.
Elpi Accumulate lp:{{

solve (goal Ctx _ Ty Sol [trm V, trm VTy]) _ :- coercion Ctx V VTy Ty Sol.

}}.
Elpi Accumulate Db coercion.db.

Elpi CoercionFallbackTactic coercion.
