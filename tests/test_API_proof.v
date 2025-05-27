From elpi Require Import elpi.

Elpi Command lemma.
Elpi Accumulate lp:{{
  main-interp-proof [str S, str ":", trm T] _ T S.
}}.

#[proof="begin"]
Elpi Export lemma.

Elpi Command qed.
Elpi Accumulate lp:{{
  main-interp-qed _ _ IT S :-
    if (var S) (S = "xx") true,
    coq.env.add-const S IT _ _ _.
}}.

#[proof="end"]
Elpi Export qed.

Fail qed.

lemma it : (True).
exact I.
qed.

Print it.

Lemma foo : True.
trivial.
qed. (* ugly, wrong name, "foo" is in the cinfo, not in the generic data *)

lemma foo : (True).
trivial.
Qed. (* ugly, wrong name, the cinfo contains "elpi" *)