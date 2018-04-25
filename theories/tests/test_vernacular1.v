Require Import elpi.


Elpi Command test.program1.
Elpi Accumulate "
  main X :- coq.say ""test1"", foo X.
".

Elpi Command test.program2.
Elpi Accumulate "
  main _ :- coq.say ""test2"".
".

Elpi Command test.program1.
Elpi Accumulate "
  foo [S] :- coq.say S.
  foo [X,Y] :- coq.say X, coq.say Y.
  foo _ :- coq.say ""too many arguments"".
".

Elpi test.program2.
Elpi test.program1 "hello".
Elpi test.program1 "hello" -my.
Elpi test.program1 "hello my" Dear.
Elpi test.program1 "hello" too many args.

Elpi Command test.program3 "
  main.
".

Fail Elpi Typecheck.