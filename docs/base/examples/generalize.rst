Generalize
==========

Abstracting a term over a subterm, like the ``generalize`` tactic does.

.. rocqtop:: in reset

   From elpi Require Import elpi.

.. rocqtop:: all

   Elpi Command generalize.
   Elpi Accumulate lp:{{

   % we add a new constructor to terms to represent terms to be abstracted
   symb abs : int -> term.

   % bind back abstracted subterms
   pred bind int, term -> term.
   bind M T T1 :- M > 0,
     T1 = {{ fun x => lp:(B x) }},   % we build a Rocq "fun .. => "
     N is M - 1,
     pi x\                           % we allocate the fresh symbol for (abs M)
       (copy (abs M) x :- !) ==>     % we schedule the replacement (abs M) -> x
       bind N T (B x).
   bind 0 T T1 :- copy T T1.         % we perform all the replacements

   main [trm T] :- std.do! [
     % example rule, abstracts all 1s.
     ((pi N M\ fold-map {{ 1 }} N (abs M) M :- !, M is N + 1) ==> fold-map T 0 T1 NVars),
     bind NVars T1 T2,
     coq.say {coq.term->string T} "becomes" {coq.term->string T2},
   ].

   }}.

   Elpi generalize (3 + 7).
