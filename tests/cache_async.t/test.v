From elpi Require Import elpi.

Elpi Command x.
Elpi Accumulate lp:{{ main _ :- true. }}.

(* trigger compilation *)
Elpi x.

(* delegated proof *)
Lemma x : True. Proof. auto. Qed.
