From elpi Require Import compiler.

Elpi Debug "simple-compiler" "get-full-path".

Module A.

  Class C (n : nat) := {}.
  Local Instance c_1 : C 1 | 10 := {}.
  Local Instance c_2 : C 2 | 1 := {}.

  Class D (n : nat) := {}.
  Local Instance d_1 : D 1 := {}.

  Class E (n : nat) := {}.
  Local Instance foo {n} : C n -> D n -> E n := {}.

  Elpi AddAllInstances.

  Elpi Override TC TC_solver All.

  Elpi Accumulate TC_solver lp:{{
    tc {{:gref E}} {{E lp:N}} Sol :-
      tc {{:gref C}} {{C lp:N}} P1, !,
      tc {{:gref D}} {{D lp:N}} P2,
      Sol = {{foo lp:P1 lp:P2}}.
  }}.

  Check (_ : E _).
End A.

Module B.
  Class Persistent (A: Prop).
  Class Separable (A: Prop).
  Local Instance persistent_separable P: Persistent P -> Separable P | 10. Admitted.
  Local Instance and_persistent P Q : Persistent P -> Persistent Q -> Persistent (P /\ Q) | 0. Admitted.
  Local Instance and_persistent2 (P Q R: Prop) : Persistent P -> Persistent Q -> Persistent R -> Persistent (P /\ Q /\ R) | 0. Admitted.
  Local Instance and_separable P1 P2 : Separable P1 -> Separable P2 -> Separable (P1 /\ P2) | 0. Admitted.

  Elpi Override TC TC_solver None.

  Goal forall P Q, Persistent P -> Separable (P /\ Q).
    Time Fail apply _.
  Abort.

  Goal forall P, Persistent P -> Separable (P /\ P).
    Time apply _.
  Abort.

  Elpi Override TC TC_solver All.
  Elpi AddAllInstances.
  Goal forall P Q, Persistent P -> Separable (P /\ Q).
    Time Fail solve [unshelve (apply _)].
  Abort.


  Elpi Accumulate TC_solver lp:{{
    :replace "elpi.apps.tc.tests.nobacktrack.B.and_separable"
    tc {{:gref Separable}} {{Separable (lp:A /\ lp:B)}} Sol :- !,
      tc {{:gref Separable}} {{Separable lp:A}} P1,
      tc {{:gref Separable}} {{Separable lp:B}} P2,
      Sol = {{and_separable _ _ lp:P1 lp:P2}}.
  }}.


  Goal forall (P Q: Prop), Persistent P -> Separable (P /\ Q).
    Time Fail solve [unshelve (apply _)].
  Abort.

  Goal forall (P Q: Prop), Persistent (Q /\ P) -> Separable (P /\ Q).
    intros.
    Fail apply _.
  Abort.

  Lemma forwRewrite {P Q}: Persistent (P /\ Q) -> Persistent P /\ Persistent Q. Admitted.
  Lemma forwRewrite1 {P Q R}: Persistent (P /\ Q /\ R) -> Persistent P /\ Persistent Q /\ Persistent R. Admitted.

  Elpi Accumulate AddForwardRewriting lp:{{
    % pred forward2 i:term, o:term, o:list (pair (term -> term) term).

    % pred rec-split-and1 i:term, i:(term -> term), o:list (pair (term -> term) term).
    % rec-split-and1 {{lp:A /\ lp:B}} DL L :-
    %   % coq.say "AAA" B,
    %   % coq.typecheck A TyLeft ok, 
    %   % coq.typecheck B TyRight ok,
    %   % coq.say "BBB",
    %   LEFT = (x\ (y\ app [{{proj1}}, TyLeft, TyRight, x y])),
    %   LEFT_APP = LEFT DL,
    %   RIGHT = (x\ (y\ app [{{proj2}}, TyLeft, TyRight, x y])),
    %   RIGHT_APP = RIGHT DL,
    %   rec-split-and1 A LEFT_APP AL, 
    %   rec-split-and1 B RIGHT_APP BL,
    %   std.append AL BL L. 
    % rec-split-and1 A P [pr P A].
  }}.
Elpi Typecheck AddForwardRewriting.

  Elpi AddForwardRewriting forwRewrite1.

  Goal forall (P Q R: Prop), (Persistent ((P /\ Q /\ Q) /\ Q /\ R) -> Separable ((P /\ P) /\ (Q /\ Q))).
    apply _.
  Qed.

  Goal forall (P Q R: Prop), (Persistent (P /\ Q /\ R) -> Separable (P /\ Q)).
    apply _. 
  Qed.

  Elpi AddForwardRewriting forwRewrite.

  Goal forall (P Q: Prop), (Persistent ((P /\ Q /\ Q) /\ Q) -> Separable ((P /\ P) /\ (Q /\ Q))).
    apply _.
  Qed.
    
  Goal forall (P Q: Prop), (Persistent ((P /\ Q /\ Q) /\ Q) -> Separable ((P /\ P) /\ (Q /\ Q))).
     apply _.
  Qed.
  
  Goal forall (P Q: Prop), (Persistent (P /\ Q) -> Separable (P /\ Q)).
    apply _.
  Qed.

  Goal forall (P Q: Prop), Persistent (Q /\ P) -> Separable (P /\ Q).
    apply _.
  Qed.
End B.