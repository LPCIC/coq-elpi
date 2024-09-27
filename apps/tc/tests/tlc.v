(* Test inspired from tlc library *)
From elpi Require Import tc.

Module extensionability.
  Notation binary A := (A -> A -> Prop).
  Class Extensionality (T : Type).
  Global Instance Extensionality_pred_2 
    (A1 : Type) (A2 : forall (x1 : A1), Type):
    Extensionality (forall (x1:A1) (x2:A2 x1), Prop). Qed.

  Goal forall A, Extensionality (binary A).
    intros.
    apply _.
  Qed.
End extensionability.

Module SlowExecution.
  Set Implicit Arguments.

  Elpi Accumulate TC.Solver lp:{{
    % :after "normalize-ty" tc.link.scope-check _ _ :- !, true.
  }}.

  Class Extensionality (A:Type) := Extensionality_make {
    extensionality_hyp : A -> A -> Prop;
    extensionality : forall (x y : A), extensionality_hyp x y -> x = y }.

  Section FuncExtDep.
    Variables (A1 : Type).
    Variables (A2 : forall (x1 : A1), Type).
    Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).
    Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).
    Variables (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type).
    Variables (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

    Global Instance Extensionality_fun_1 :
      Extensionality (forall (x1:A1), A2 x1). Admitted.

  End FuncExtDep.

  Lemma eq_existT_same_eq (A : Type) (P : A -> Type) (p : A) (x y : P p):
    (existT P p x = existT P p y) = (x = y).
  Proof.
    Timeout 10 Fail refine (@extensionality _ _).
  Abort.
End SlowExecution.
