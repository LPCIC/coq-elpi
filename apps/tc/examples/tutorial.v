Require Import Bool.
From elpi.apps Require Import tc.

Class Eqb (T: Type) := {
  eqb : T -> T -> bool; 
  eqb_leibniz A B: eqb A B = true <-> A = B
}.

#[refine] Instance eqBool : Eqb bool := {
  eqb x y := if x then y else negb y
}.
Proof. intros [] []; intuition. Qed.

#[refine] Instance eqProd (A B : Type) : Eqb A -> Eqb B -> Eqb (A * B) := {
  eqb x y := eqb (fst x) (fst y) && eqb (snd x) (snd y)
}.
Proof.
  intros [] []. split. intros; simpl in H.
  * case (eqb a a0) eqn:aB, (eqb b b0) eqn:bB; try easy.
    apply pair_equal_spec; destruct e, e0; split.
    apply eqb_leibniz0; auto.
    apply eqb_leibniz1; auto.
  * intros. apply pair_equal_spec in H; destruct H; subst. simpl.
    apply andb_true_intro; destruct e, e0; split.
    apply eqb_leibniz0; auto.
    apply eqb_leibniz1; auto.
Qed.

TC.Print_instances.
TC.Get_class_info Eqb.

(* Abstraction of elpi context variable *)
Section Foo.
  Variable (A B: Type) (HA : Eqb A) (HB : Eqb B).
  #[refine] Global Instance eqProd' : Eqb (A * B) := {
    eqb x y := eqb (fst x) (fst y) && eqb (snd x) (snd y)
  }.
  Proof.
    intros [] []; simpl; split; intros.
    apply eqb_leibniz. destruct H.
    replace (eqb (a, b) (a0, b0)) with (eqb a a0 && eqb b b0); auto. admit.
    apply andb_true_intro; apply pair_equal_spec in H; split;
    apply eqb_leibniz; easy.
  Admitted.

  (* Here we see that HA and HB are compiled in elpi since their type is a class *)
  TC.Print_instances Eqb.

  (* The rules for eqProd' is as follows 

  shorten tc-tutorial.{tc-Eqb}.
  tc-Eqb {{prod A B}} {{eqProd'}}.

  Remark: Here A and B are not elpi variables, but the coq variables from the
          context
  *)

  Elpi Print TC.Solver "elpi.apps.tc.examples/TC.Solver".
End Foo.

(* 
  On section end the local instances are removed (i.e. HA and HB disappears)
  and eqProd' is recompiled
*)
TC.Print_instances Eqb.
(* 
  the rules for eqProd' is as follows

  shorten tc-tutorial.{tc-Eqb}.
  tc-Eqb {{prod lp:A lp:B}} {{eqProd' lp:A lp:B lp:PA lp:PB}} :-
    tc-Eqb A PA, tc-Eqb B PB.

  Remark: Here A and B are elpi variables and PA, PB are the proof that we can 
          prove {{Eqb lp:A}} and {{Eqb lp:B}}
*)

TC.Get_class_info Eqb.

Module Backtrack.

  #[no_backtrack] TC.Pending_attributes.
  Class NoBacktrack (n: nat).
  Class A (n: nat).

  Instance a0 : A 0. Qed.
  Instance nb0 : NoBacktrack 0. Qed.
  Instance nb1 : NoBacktrack 1. Qed.
  Instance a3 n : NoBacktrack n -> A n -> A 3. Qed.
  
  Goal A 3. Fail apply _. Abort.

  Elpi Print TC.Solver "elpi.apps.tc.examples/TC.Solver".
End Backtrack.

TC.Print_instances.
TC.Get_class_info DecidableClass.Decidable.
