From elpi Require Import elpi.
Elpi File myfile lp:{{
  pred locate?! i:id, i:A -> located, o:A.  % Locate or fail (rather than panic)
  locate?! Name Pat Val :-
    std.mem! {coq.locate-all Name} (Pat Tmp),
    ( ground_term Tmp, !, Val = Tmp
    ; fail ).
}}.

Elpi Command C1.
Elpi Accumulate File myfile.
Elpi Accumulate lp:{{  }}.

Elpi Command C2.
Elpi Accumulate File myfile.
Elpi Accumulate lp:{{  }}. (* Error: todbl: term contains spill: coq.locate-all Name *)

#[phase="interp"] Elpi Program foo lp:{{ pred p i:gref. main _ :- coq.say "hello". }}.