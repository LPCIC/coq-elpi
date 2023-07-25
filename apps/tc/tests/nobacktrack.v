From elpi Require Import compiler.

Elpi Debug "simple-compiler".
Unset TC_NameFullPath.

Module A.

  Class C (n : nat) := {}.
  Local Instance c_1 : C 1 | 10 := {}.
  Local Instance c_2 : C 2 | 1 := {}.

  Class D (n : nat) := {}.
  Local Instance d_1 : D 1 := {}.

  Class E (n : nat) := {}.
  Local Instance foo {n} : C n -> D n -> E n := {}.

  (* Elpi AddAllInstances. *)
  Elpi AddClasses deterministic C.
  Elpi AddClasses D E.
  Elpi AddAllInstances.
  Elpi Override TC TC_solver All.

  Elpi Print TC_solver.

  Check (_ : E _).
End A.

Module B0.

  Class Persistent (A: Prop).
  Class Separable (A: Prop).
  Local Instance persistent_separable P: Persistent P -> Separable P | 10. Admitted.
  Local Instance and_persistent P Q : Persistent P -> Persistent Q -> Persistent (P /\ Q) | 0. Admitted.
  Local Instance and_separable P1 P2 : Separable P1 -> Separable P2 -> Separable (P1 /\ P2) | 0. Admitted.
  
  Elpi AddClasses Persistent Separable.
  Elpi AddAllInstances.

  Module B.
    Elpi Accumulate TC_solver lp:{{
      :after "firstHook"
      tc-Separable {{lp:A /\ lp:B)}} Sol :- !,
        tc-Separable A P1, !,
        tc-Separable B P2,
        Sol = {{@and_separable lp:A lp:B lp:P1 lp:P2}}.
    }}.
    Elpi Typecheck TC_solver.


    Elpi Override TC TC_solver None.
    Goal forall P Q, Persistent P -> Separable (P /\ P /\ P /\ P /\ P/\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P/\ P /\ P /\ P /\ Q).
      Time Fail apply _.
    Abort.

    Elpi Override TC TC_solver All.

    Goal forall P Q, Persistent P -> Separable (P /\ P /\ P /\ P /\ P/\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P /\ P/\ P /\ P /\ P /\ Q).
      Time Fail solve [unshelve (apply _)].
    Abort.

    Goal forall P, Persistent P -> Separable (P /\ P).
      Time apply _.
    Abort.

    Goal forall P Q, Persistent P -> Separable (P /\ Q).
      Time Fail solve [unshelve (apply _)].
    Abort.


    Goal forall (P Q: Prop), Persistent P -> Separable (P /\ Q).
      Time Fail solve [unshelve (apply _)].
    Abort.

    Goal forall (P Q: Prop), Persistent (Q /\ P) -> Separable (P /\ Q).
      intros.
      Fail apply _.
    Abort.

    Lemma forwRewrite {P Q}: Persistent (P /\ Q) -> Persistent P /\ Persistent Q. Admitted.

    Elpi AddForwardRewriting forwRewrite.

    Goal forall (P Q: Prop), Persistent (Q /\ P) -> Separable (P /\ Q).
      apply _. 
    Qed.

    Goal forall (P Q R: Prop), (Persistent ((P /\ Q /\ Q) /\ Q /\ P) -> Separable ((P /\ P) /\ (P /\ Q))).
      apply _.
    Qed.

    Goal forall (P Q R: Prop), (Persistent (P /\ Q /\ R) -> Separable (P /\ Q)).
      apply _. 
    Qed.

    Class C (A: Prop).

    Lemma foo: forall P, C P -> C (P /\ False) . Admitted.

    Lemma bar: forall P, C P -> Separable P. Admitted.

    Elpi AddForwardRewriting bar foo.

    Elpi Bound Steps 5000.
    Goal forall P, C P -> Separable (P /\ False).
      intros.
      Fail apply _.
    Abort.
  End B.
End B0.