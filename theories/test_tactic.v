From elpi Require Import elpi.

Elpi Tactic print.goal "

  type $$`: A -> B -> C.
  pred ctx i:term, o:A.
  ctx (?? _ L) TS :- map L (x\y\sigma T\ $is_name x, of x T x, y = ({pp x} `: {pp T})) TS.
  solve [goal X T As] :- ctx X L,
    coq-say ""Goal: "", coq-say As, coq-say ""\n"",
    coq-say L,
    coq-say ""------------"",
    coq-say {pp T}.
  typecheck.

".


Lemma test_print (T : Type) (x : forall y : T, Type) (w : T) :
  forall e : x w = Type, forall j : x w, exists a : x w, a = a.
Proof.

 elpi run print.goal "typecheck".
 elpi print.goal.

 intros; unshelve(eexists ?[foo]).

 elpi print.goal; shelve_unifiable.

 all: cycle 1; elpi print.goal; shelve_unifiable.

 exact (refl_equal j).
Qed.


Elpi Tactic id "

  solve [goal Solution T _] :- 
    of hole T X, X = Solution.
".

Elpi Tactic intro "

  solve [goal Solution Type _Attributes] :-
    of (lam _ hole x\ hole) Type X, X = Solution.

".

Elpi Tactic refl "

  solve [goal Solution Type _Attributes] :-
    of {{refl_equal _}} Type X, X = Solution.

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

  coq-declare-evar X T G :- coq-evar X T, G.
  solve [goal S _ _] :-
    S = app[{{S}}, _FRESH],
    coq-evar _X {{nat}},
    coq-evar _XX {{nat -> bool}},
    $print_constraints.

".

Lemma wrong : nat.
Proof.
  Fail elpi wrong.
Abort.