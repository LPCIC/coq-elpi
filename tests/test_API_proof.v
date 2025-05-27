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

Succeed Print it.

lemma it2 : (True /\ _).
Succeed Show. (* yes! *)
split.
exact I.
exact I.
qed.

Succeed Print it2.

Lemma foo : True.
trivial.
qed.

lemma foo2 : (True).
trivial.
Qed.

Elpi Command lemma_if.
Elpi Accumulate lp:{{
  main-interp-proof [str S, str ":", trm T] _ T S. /* 9.1 */
  main _.
}}.

#[proof(begin_if="interactive")]
Elpi Export lemma_if.

#[interactive]
lemma_if it3 : (True).
Succeed Show.
Abort.

lemma_if it4 : (True).
Fail Show.


