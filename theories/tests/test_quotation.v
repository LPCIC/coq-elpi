From elpi Require Import elpi.

Elpi Command test.quotations.

(****** Notations **********************************)

Elpi Accumulate "
test-env-const :-
  coq.locate ""plus"" (const GR),
  coq.env.const GR BO TY,
  TY = {{ nat -> nat -> nat }},
  BO = (fix _ 0 TY add\
         lam _ {{nat}} n\ lam _ {{nat}} m\
         match n {{fun _ : nat => nat}}
         [ m
         , lam _ {{nat}} w\ app[ {{S}}, app[add,w,m]]]).
".
Elpi Query "test-env-const".

Elpi Accumulate "
test-env-const1 :-
  coq.locate ""plus"" (const GR),
  coq.env.const GR _BO TY,
  TY = {{ nat -> nat -> nat }},
  BO1 = (fix _ 0 TY add\
         {{ fun n m => match n with
              | O => m
              | S p => lp:"" app[add, {{p}}, {{m}}] ""  
            end }}),
  coq.say BO1,
  coq.elaborate BO1 BO2 _TY2,
  coq.say BO2.
".
Elpi Query "test-env-const1".

Require Vector.

Elpi Query "
  T = {{ fun v : Vector.t nat 2 =>
           match v with
           | Vector.nil _ => 0
           | Vector.cons _ _ _ _ => 1
           end }},
  coq.say T,
  coq.elaborate T T1 _TY,
  coq.say T1.
".

Elpi Query "{{ lp:X }} = 3, coq.say X".

Elpi Query "{{ fun x => lp:X x }} = Y, coq.say Y".

Elpi Accumulate "
test :- X = {{ fun (r : nat) (p : forall y : nat, y = 0 :> nat) (q : bool) => lp:""{coq.typecheck {{p}} }"" }}, coq.say X.
".

Elpi Query "test.".


