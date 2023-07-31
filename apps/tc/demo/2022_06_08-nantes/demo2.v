From Coq Require Import Bool Setoid.
From elpi Require Import compiler.

Unset TC_NameFullPath.

Generalizable All Variables.

Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) :=
  inj x y : S (f x) (f y) -> R x y.

Definition compose {T1 T2 T3: Type} (g: T2 -> T3) (f : T1 -> T2) (x: T1) := g(f x).
Definition times2 x := x * 2.

Local Instance compose_inj {A B C} R1 R2 R3 (f : A -> B) (g : B -> C) :
  Inj R1 R2 f -> Inj R2 R3 g -> Inj R1 R3 (compose g f) | 10.
Admitted.

Local Instance times2_inj : Inj eq eq times2 | 10. Admitted.

Elpi Override TC TC_solver All.
Elpi AddClasses Inj.
Elpi AddInstances Inj.

Elpi Accumulate TC_solver lp:{{
  :after "firstHook"
  tc-Inj A A Eq Eq (app [global {{:gref compose}}, A, A, A, L, R]) Sol :-
    L = R, !,
    tc-Inj A A Eq Eq L InjL,
    Sol = app [global {{:gref compose_inj}}, A, A, A, Eq, Eq, Eq, L, R, InjL, InjL].
}}.
Elpi Typecheck TC_solver.

Goal Inj eq eq 
  (compose 
    (compose 
      (compose 
        (compose (compose times2 times2)(compose times2 times2))
        (compose (compose times2 times2)(compose times2 times2)))
      (compose 
        (compose (compose times2 times2)(compose times2 times2))
        (compose (compose times2 times2)(compose times2 times2))))
    (compose 
      (compose 
        (compose (compose times2 times2)(compose times2 times2))
        (compose (compose times2 times2)(compose times2 times2)))
      (compose 
        (compose (compose times2 times2)(compose times2 times2))
        (compose (compose times2 times2)(compose times2 times2))))). 
Proof. Time apply _. Qed.