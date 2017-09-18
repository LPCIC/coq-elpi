Cd "~/git/coq-elpi".

From elpi Require Import elpi.

Elpi Tactic param " typecheck. ".

Elpi Accumulate File "coq-param.elpi".
Elpi Run param "typecheck".

Fail Elpi Run param "derive-param ""plus""".

Inductive natR : nat -> nat -> Type :=
| O_R : natR 0 0
| S_R : forall (m n : nat), natR m n -> natR (S m) (S n).
Elpi Tactic param.
Elpi Accumulate "param {{nat}} {{nat}} {{@natR}}.".
Elpi Accumulate "param {{@O}} {{@O}} {{@O_R}}.".
Elpi Accumulate "param {{@S}} {{@S}} {{@S_R}}.".
Elpi Run param "param {{nat}} X Y".

Inductive eqR (A A1 : Type) (AR : A -> A1 -> Type) (x : A) (x1 : A1) (xR : AR x x1) :
  forall (x' : A) (x1' : A1), AR x' x1' -> Prop :=
eq_refl_R : @eqR _ _ _ _ _ xR _ _ xR.
Elpi Accumulate "param {{eq}} {{eq}} {{@eqR}}.".
Elpi Accumulate "param {{eq_refl}} {{eq_refl}} {{@eq_refl_R}}.".


Elpi Run param "derive-param ""pred""".

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.

Fail Elpi Run param "derive-param ""predn""".

Fixpoint prednR (n n0 : nat) (n1 : natR n n0) :=
 match
   n1 in (natR n2 n3)
   return
     (natR
        match n2 with
        | 0 => 0
        | S n5 =>
            S
              ((fix predn (n6 : nat) : nat :=
                  match n6 with
                  | 0 => 0
                  | S n7 => S (predn n7)
                  end) n5)
        end
        match n3 with
        | 0 => 0
        | S n5 =>
            S
              ((fix predn (n6 : nat) : nat :=
                  match n6 with
                  | 0 => 0
                  | S n7 => S (predn n7)
                  end) n5)
        end)
 with
 | O_R => O_R
 | S_R n2 n3 n4 =>
     S_R
       ((fix predn (n5 : nat) : nat :=
           match n5 with
           | 0 => 0
           | S n6 => S (predn n6)
           end) n2)
       ((fix predn (n5 : nat) : nat :=
           match n5 with
           | 0 => 0
           | S n6 => S (predn n6)
           end) n3) (prednR n2 n3 n4)
 end.

Fail Elpi Run param "derive-param ""plus""".
Fail Elpi Run param "derive-param ""eq_rect""".

Goal True.
