Cd "~/git/coq-elpi".

From elpi Require Import elpi.

Elpi Tactic param " typecheck. ".

Elpi Accumulate File "coq-param.elpi".
Elpi Run param "typecheck".

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

Class param X XR (x : X) (xR : XR).
(* Hint Extern 0 (param _ _ _ _) => *)
(*   match goal with param _ _ ?x _ => elpi "derive-param" *)

Definition nat2nat := nat -> nat.
Elpi Run param "env-add-param ""nat2nat"" ""nat2natR""".
Elpi Run param "env-add-param ""pred"" ""predR""".
Print predR.

Check (predR : nat2natR pred pred).

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.

Fail Elpi Run param "derive-param ""predn"" _ _".

Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).

Fail Elpi Run param "derive-param ""quasidn"" _ _".

Require Import ssreflect ssrfun ssrbool.

Definition M prednR (n n0 : nat) (n1 : natR n n0) :=  match
   n1 in (natR n2 n3)
   return
     (natR
        match n2 with
        | 0 => 0
        | S n5 => S (predn n5)
        end
        match n3 with
        | 0 => 0
        | S n5 => S (predn n5)
        end)
 with
 | O_R => O_R
 | S_R n2 n3 n4 =>
     S_R (predn n2) (predn n3) (prednR n2 n3 n4)
 end.

Fixpoint prednR' (n n0 : nat) (n1 : natR n n0) : natR (predn n) (predn n0).
Proof.
pose M := @M prednR' n n0 n1.
move: n0 n1 @M.
case: n=> [|n']; case=> [|n0'] n1 M; exact: M.
Defined.

Eval compute - [predn M] in prednR'.


Fixpoint prednR (n n0 : nat) (n1 : natR n n0) :=
 let M : (forall n n0 (n1 : natR n n0), natR
        match n with
        | 0 => 0
        | S n5 => S (predn n5)
        end
        match n0 with
        | 0 => 0
        | S n5 => S (predn n5)
        end) := fun n n0 n1 => match
   n1 in (natR n2 n3)
   return
     (natR
        match n2 with
        | 0 => 0
        | S n5 => S (predn n5)
        end
        match n3 with
        | 0 => 0
        | S n5 => S (predn n5)
        end)
 with
 | O_R => O_R
 | S_R n2 n3 n4 =>
     S_R (predn n2) (predn n3) (prednR n2 n3 n4)
 end in
match n as n2 return (forall n3 : nat, natR n2 n3 -> natR (predn n2) (predn n3)) with
         | 0 =>
             fun abs_n2 : nat =>
             match abs_n2 as n2 return (natR 0 n2 -> natR (predn 0) (predn n2)) with
             | 0 => M 0 0
             | S n0' => M 0 (S n0')
             end
         | S n' =>
             fun abs_n2 : nat =>
             match abs_n2 as n2 return (natR (S n') n2 -> natR (predn (S n')) (predn n2)) with
             | 0 =>  M (S n') 0
             | S n0' => M (S n') (S n0')
             end
         end n0 n1.



Fail Elpi Run param "derive-param ""plus"" _ _".
Fail Elpi Run param "derive-param ""eq_rect"" _ _".

Goal True.
