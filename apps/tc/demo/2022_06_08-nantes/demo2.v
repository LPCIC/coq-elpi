From Coq Require Import Bool Setoid.
From elpi Require Import compiler.

Generalizable All Variables.

Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) :=
  inj x y : S (f x) (f y) -> R x y.

Definition compose {T1 T2 T3: Type} (g: T2 -> T3) (f : T1 -> T2) (x: T1) := g(f x).
Definition times2 x := x * 2.

Local Instance compose_inj {A B C} R1 R2 R3 (f : A -> B) (g : B -> C) :
  Inj R1 R2 f -> Inj R2 R3 g -> Inj R1 R3 (compose g f) | 10.
Admitted.

Local Instance times2_inj : Inj eq eq times2 | 10. Admitted.

Elpi Override TC TC_check All.
Elpi AddInstances Inj.

Elpi Accumulate TC_check lp:{{
  :after "1"
  tc {{:gref Inj}} {{Inj eq eq (compose lp:L lp:R)}} Sol :-
    L = R, !,
    tc {{:gref Inj}} {{Inj eq eq lp:L}} InjL,
    Sol = {{compose_inj eq eq eq lp:L lp:L lp:InjL lp:InjL }}.
}}.

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