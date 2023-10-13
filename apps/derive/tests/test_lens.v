From elpi.apps Require Import test_derive_stdlib derive.lens.

Import test_derive_stdlib.Coverage.

(* coverage *)
Module Coverage.
Elpi derive.lens fo_record.
Elpi derive.lens pa_record.
Elpi derive.lens pr_record.
Fail Elpi derive.lens dep_record.
Fail Elpi derive.lens sigma_bool.
End Coverage.

Import Coverage.

Check _f1 : Lens fo_record fo_record peano peano.
Check _f2 : Lens fo_record fo_record unit unit.
Check @_f3 : forall A, Lens (pa_record A) (pa_record A) peano peano.
Check @_f4 : forall A, Lens (pa_record A) (pa_record A) A A.
Check @_pf3 : forall A, Lens (pr_record A) (pr_record A) peano peano.
Check @_pf4 : forall A, Lens (pr_record A) (pr_record A) A A.
Goal forall A x, x = @_pf3 A.
intros; unfold _pf3.
match goal with
| |- x = {| over := fun f r => {| pf3 := f (_ r); pf4 := _ r |} ;
            view := _ |}
    => idtac "ok"
| |- _ => fail "not primitive"
end.
Abort.

#[projections(primitive=yes)]
Record R := MkR {
  proj : nat;
}.

Elpi derive.lens R "R__".

Lemma failing r :
  r.(proj) = 0 ->
  view R__proj r = r.(proj).
Proof.
  simpl.
  intros Hpr.
  rewrite Hpr.
  reflexivity.
Abort.

Lemma working r :
  match r with MkR r_proj => r_proj end = 0 ->
  view R__proj r = match r with MkR r_proj => r_proj end.
Proof.
  simpl.
  intros Hpr.
  rewrite Hpr.
  Fail reflexivity.
  unfold proj.
  rewrite Hpr.
  reflexivity.
Qed.
