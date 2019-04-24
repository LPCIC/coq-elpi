From elpi Require Import elpi.


Elpi Command hello "

  main [] :- coq.say ""hello wolrd"".
  main [str S] :- Msg is ""hello "" ^ S, coq.say Msg.

".

Elpi hello.
Elpi hello "Coq".




Elpi Command print "

  pp (indt GR) :-
    coq.env.indt GR _ _ _ _ K _,
    coq.say K.

  pp (const GR) :-
    coq.env.const GR BO _,
    coq.say BO.

  main [str X] :- coq.locate X T, pp T.
".

Elpi print "nat".
Elpi print "plus".



From elpi Require Import derive.

Elpi derive list.

Inductive tree := Leaf | Node : list tree -> tree.
Elpi derive tree.

Print Module tree.
Check tree.eq.OK.
Print axiom.


About tree_ind.
Check tree.induction.
Print tree.eq.OK.
Print tree.eq.correct.

