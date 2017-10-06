From elpi Require Import elpi.

Section foo.

Variables n m : nat.
Let o := m.

Elpi Tactic print.goal "

  solve [goal L X T As] :-
    coq-say ""Goal: "", coq-say As, coq-say ""\n"",
    coq-say L,
    coq-say ""------------"",
    coq-say {pp T},
    coq-say {{n + m + o}}.

  typecheck.

".


Lemma test_print (T : Type) (x : forall y : T, Type) (w : T) :
  forall e : x w = Type, forall j : x w, exists a : x w, a = a.
Proof.

 elpi run print.goal "typecheck".

 elpi print.goal.

 intros; unshelve(eexists ?[foo]).

 elpi print.goal.

 all: cycle 1; elpi print.goal; shelve_unifiable.

 exact (refl_equal j).
Qed.

End foo.

Elpi Tactic id "

  solve [goal _ Solution T _] :- Solution = hole.
".

Elpi Tactic intro "

  solve [goal _ Solution Type _Attributes] :-
    Solution = lam _ hole x\ hole.

".

Elpi Tactic refl "

  solve [goal _ Solution Type _Attributes] :-
    Solution = {{refl_equal _}}.

".

Lemma test_tactics (T : Type) (x : T) : forall e : x=x, e = e.
Proof.
  elpi id.
  elpi intro. 
  elpi refl. 
Qed.

(* A wrong implementation of a tactic that does not
   declare _FRESH in the constraint set as a typed evar,
   hence Coq can't read the term back *)

Elpi Program wrong.
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate " 

  solve [goal _ S _ _] :-
    S = app[{{S}}, _FRESH],
    evar _X {{nat}},
    evar _XX {{nat -> bool}},
    $print_constraints.

".

Lemma wrong : nat.
Proof.
  Fail elpi wrong.
Abort.

