From elpi.tests Require Import test_File1.

Elpi File file2 lp:{{ main _ :- coq.say "hello3". }}.

Elpi Command c.
Elpi Accumulate lp:{{ main _ :- coq.say "hello1". }}.
Elpi Accumulate File file1.
Elpi Accumulate File file2.
Elpi Accumulate lp:{{ main _ :- coq.say "hello4". }}.

Elpi c.




