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

(* Fail Elpi Run param "derive-param ""predn"" _ _". *)

Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).

(* Fail Elpi Run param "derive-param ""quasidn"" _ _". *)

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

Fixpoint prednR (n n' : nat) (nR : natR n n') : natR (predn n) (predn n') :=
 let U n := match n with 0 => 0 | S n5 => S (predn n5) end in
 let U' n := match n with 0 => 0 | S n5 => S (predn n5) end in
 let FR n n' (nR : natR n n') : natR (U n) (U' n') :=
    match nR in natR n n' return natR (U n) (U' n') with
    | O_R => O_R
    | S_R n n' nR => S_R (predn n) (predn n') (prednR n n' nR)
    end in
 let F' n n' := match n' as n' return natR n n' -> natR (U n) (predn n') with
                  0 as n' | _ as n' => FR n n'
                  end in
 let F n := match n as n return forall n' : nat, natR n n' -> natR (predn n) (predn n') with
                  0 as n | _ as n => F' n end in
 F n n' nR.

Fail Elpi Run param "derive-param ""predn"" _ _".

Fixpoint weirdn n := match n with S (S n) => S (weirdn n) | _ => 0 end.

Fail Elpi Run param "derive-param ""weirdn"" _ _".

Lemma test n (U := fun n => match n with S (S n5) => S (weirdn n5) | _ => 0 end) : weirdn n = U n.
Proof. elim: n.

Fixpoint weirdnR (n n' : nat) (nR : natR n n') : natR (weirdn n) (weirdn n') :=
 let U n := match n with S (S n5) => S (weirdn n5) | _ => 0 end in
 let U' n := match n with S (S n5) => S (weirdn n5) | _ => 0 end in
 let FR n n' (nR : natR n n') : natR (U n) (U' n') :=
    match nR in natR n n' return natR (U n) (U' n') with
    | O_R => O_R
    | S_R _ _ nR => match nR in natR n n' return natR (U (S n)) (U' (S n')) with
                     | O_R => O_R
                     | S_R n n' nR => S_R (weirdn n) (weirdn n') (weirdnR n n' nR)
                     end
    end in
 let F' n n' := match n' as n' return natR n n' -> natR (U n) (weirdn n') with
                  0 as n' | _ as n' => FR n n'
                  end in
 let F n := match n as n return forall n' : nat, natR n n' -> natR (weirdn n) (weirdn n') with
                  0 as n | _ as n => F' n end in
 F n n' nR.

Fail Elpi Run param "derive-param ""weirdn"" _ _".

Elpi Run param "coq-locate ""weirdnR"" (const GR), coq-env-const GR _ _".

Fail Elpi Run param "derive-param ""plus"" _ _".
Fail Elpi Run param "derive-param ""eq_rect"" _ _".

Goal True.
