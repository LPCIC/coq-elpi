From elpi Require Import elpi.

(* Examples of core tactics to be invoked by the user *)

Elpi Tactic intro "
  solve [str S] G GS :- !, coq.string->name S Name, apply G (intro Name) GS.
  solve Args _ _ :- coq.error ""intro expects a name, you passed:"" Args.
".
Elpi Typecheck.

Example test_intro : True -> True.
Proof.
Fail elpi intro x y.
Fail elpi intro.
elpi intro x.
exact x.
Qed.


Elpi Tactic assumption "
  solve [] G GS :- !, apply G assumption GS.
  solve Args _ _ :- coq.error ""assumption expects no arguments, you passed:"" Args.
".
Elpi Typecheck.

Example test_assumption : True -> True.
Proof.
elpi intro x.
Fail elpi assumption x y.
elpi assumption.
Qed.


Elpi Tactic constructor "
  solve [] G GS :- !, apply G constructor GS.
  solve Args _ _ :- coq.error ""constructor expects no arguments, you passed:"" Args.
".
Elpi Typecheck.


Example test_constructor : Type -> True * Type.
Proof.
elpi intro x.
Fail elpi constructor x y.
elpi constructor.
- elpi constructor.
- Fail elpi constructor.
  elpi assumption.
Qed.


(* Examples of tacticals *)


Elpi Tactic crush "
  solve _ G [] :- apply G (repeat (or [intro `x`, constructor, assumption])) [].
".
Elpi Typecheck.

Example test_crush : False -> True * False * (Type -> Type).
Proof.
elpi crush.
Qed.


