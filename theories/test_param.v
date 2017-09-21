Cd "~/git/coq-elpi".

From elpi Require Import elpi.

Class param_db {X X1 XR} (x : X) (x : X1) (xR : XR) := store_param {}.
Class param {X XR} (x : X) (xR : XR x x) := Param {}.

Elpi Tactic param " typecheck. ".
Elpi Accumulate File "coq-param.elpi".
Elpi Run param "typecheck".

Elpi Run param "env-add-param {{@nat}} ""natR""".

(* Fail Elpi Run param "param-indt ""nat"" X Y". *)
Elpi Run param "with-TC-param (param {{O}} X Y)".
Elpi Run param "with-TC-param (param {{S}} X Y)".

Inductive eqR (A A1 : Type) (AR : A -> A1 -> Type) (x : A) (x1 : A1) (xR : AR x x1) :
  forall (x' : A) (x1' : A1), AR x' x1' -> Prop :=
eq_refl_R : @eqR _ _ _ _ _ xR _ _ xR.
Elpi Tactic param.
Elpi Accumulate "param {{@eq}} {{@eq}} {{@eqR}}.".
Elpi Accumulate "param {{@eq_refl}} {{@eq_refl}} {{@eq_refl_R}}.".
Fail Elpi Run param "param-const {{@eq_rect}} _ _".

Elpi Run param "param {{Set}} _ _".

(* Goal forall U V W (x : U) (y : V) (r : W x y), param_db x y r -> False. *)
(*   intros  U V W x y r pr. *)
(*   assert {T : _ & {a : _ & @param _ T x a}}. *)
(*   eexists; eexists. *)
(*   Fail elpi param. *)
(*   Fail elpi param. *)

(*   assert (. *)
(*     exact 0. *)

(*   (* Unshelve. *) *)
(*   elpi param. *)
(*   Show Proof. *)
(*   shelve. *)


(*   exact  *)


(* Hint Extern 0 (query_param _ _ _ _) => *)
(*   match goal with query_param _ _ ?x _ => *)
(*     elpi "" *)

Elpi Run param "with-TC {{@param_db}} retrieve-param (param {{nat}} X Y)".

Definition nat2nat := nat -> nat.
Definition nat2nat2nat := nat -> nat -> nat.
Elpi Run param "env-add-param {{@nat2nat}} ""nat2natR""".
Elpi Run param "env-add-param {{@nat2nat2nat}} ""nat2nat2natR""".
Elpi Run param "env-add-param {{@pred}} ""predR""".
Print predR.
Check (predR : nat2natR pred pred).

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.
Elpi Run param "env-add-param {{@predn}} ""prednR""".
Elpi Run param "env-add-param {{@plus}} ""plusR""".

Print plusR.
Print prednR.

Check (prednR : nat2natR predn predn).
Check (plusR : nat2nat2natR plus plus).


Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).
Elpi Run param "param-const {{@quasidn}} _ _ _ _ _".

Fixpoint weirdn n := match n with S (S n) => S (weirdn n) | _ => 0 end.
Elpi Run param "param-const {{@weirdn}} _ _ _ _ _".

From Coq Require Vector.

Inductive bla : nat -> Type := Bla : nat -> bla 0 | Blu n : bla n -> bla 1.
Elpi Run param "env-add-param {{@bla}} ""blaR"")".
Inductive vec (A : Type) : nat -> Type :=
    nil : vec A 0 | cons : A -> forall n : nat, vec A n -> vec A (S n).
Fail Elpi Run param "env-add-param {{@vec}} ""vecR"")".
(*^^^^ strange bug: who called the extra param in the end ?? *)

Elpi Run param "coq-TC-db-for {term->gr {{@param_db}}} _".
