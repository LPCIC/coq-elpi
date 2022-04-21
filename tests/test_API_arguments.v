From elpi Require Import elpi.

(***** Impargs *******************************)

Module X2.

Axiom imp : forall T (x:T), x = x -> Prop.
Arguments imp {_} [_] _ , [_] _ _ .

Elpi Query lp:{{
    coq.locate "imp" I,
    coq.arguments.implicit I
      [[maximal,implicit,explicit], [implicit,explicit,explicit]],
    @global! => coq.arguments.set-implicit I
      [[]],
    coq.arguments.implicit I
      [[explicit,explicit,explicit]]
}}.
End X2.
About X2.imp.

Module X3.
Definition foo (T : Type) (x : T) := x.
Arguments foo : clear implicits.

Fail Check foo 3.

Elpi Query lp:{{
  @global! => coq.arguments.set-default-implicit {coq.locate "foo"}
}}.

Check foo 3.

End X3.


(***** Argnames/scopes/simpl *******************************)

Definition f T (x : T) := x = x.

Elpi Query lp:{{
  coq.arguments.set-name     {coq.locate "f"} [some "S"],
  coq.arguments.name         {coq.locate "f"} [some "S"],
  coq.arguments.set-implicit {coq.locate "f"} [[implicit]],
  coq.arguments.set-scope    {coq.locate "f"} [some "type"],
  coq.arguments.scope        {coq.locate "f"} [some "type_scope"]
}}.
About f.
Check f (S:= bool * bool).

Elpi Query lp:{{
  coq.arguments.set-simplification {coq.locate "f"} (when [] (some 1))
}}.
About f.
Check f (S:= bool * bool).
Eval simpl in f (S := bool).
