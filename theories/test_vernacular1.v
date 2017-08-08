Require Import elpi.

Elpi Init "-I" ".".

Elpi Program test.program1.
Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq-lib.elpi".
Elpi Accumulate "
  main X :- coq-say ""test1"", foo X.
".

Elpi Program test.program2.
Elpi Accumulate "
  accumulate pervasives, coq-lib.
  main _ :- coq-say ""test2"".
".

Elpi Program test.program1.
Elpi Accumulate "
  foo [S] :- coq-say S.
  foo [X,Y] :- coq-say X, coq-say Y.
  foo _ :- coq-say ""too many arguments"".
".

Elpi test.program2.
Elpi test.program1 "hello".
Elpi test.program1 "hello" -my.
Elpi test.program1 "hello" Dear.
Elpi test.program1 "hello" too many args.