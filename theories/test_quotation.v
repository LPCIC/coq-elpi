From elpi Require Import elpi.

Elpi Init "./" "../elpi/".

Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq-lib.elpi".

(****** Notations **********************************)

Elpi Accumulate "
test-env-const :-
  coq-locate ""plus"" (const GR),
  coq-env-const GR BO TY,
  TY = {{ nat -> nat -> nat }},
  BO = (fix _ 0 TY add\
         lam _ {{nat}} n\ lam _ {{nat}} m\
         match n {{fun _ : nat => nat}}
         [ m
         , lam _ {{nat}} w\ app[ {{S}}, app[add,w,m]]]).
".
Elpi Run "test-env-const".

Elpi Accumulate "
test-env-const1 :-
  coq-locate ""plus"" (const GR),
  coq-env-const GR BO TY,
  TY = {{ nat -> nat -> nat }},
  BO1 = (fix _ 0 TY add\
         {{ fun n m => match n with
              | O => m
              | S p => lp:"" app[add, {{p}}, {{m}}]  ""  
            end }}),
  coq-say BO1,
  coq-elaborate BO1 BO2 TY2,
  coq-say BO2.
".
Elpi Run "test-env-const1".

Require Vector.

Elpi Run "
  T = {{ fun v : Vector.t nat 2 =>
           match v with
           | Vector.nil _ => 0
           | Vector.cons _ _ _ _ => 1
           end }},
  coq-say T,
  coq-elaborate T T1 _TY,
  coq-say T1.
".