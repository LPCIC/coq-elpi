Require Import elpi.elpi.
Require Import elpi.tests.dummy.

Elpi Command program.
Elpi Accumulate lp:{{
pred p.
     main _ :- coq.say "program", std.findall p L, coq.say L. }}.
Elpi Export program.