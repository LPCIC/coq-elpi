From elpi Require Import elpi.

Elpi Command test.quotations.

(****** Notations **********************************)

Elpi Query lp:{{
  coq.locate "plus" (const GR),
  coq.env.const GR BO TY,
  TY = {{ nat -> nat -> nat }},
  BO = (fix _ 0 TY add\
         fun _ {{nat}} n\ fun _ {{nat}} m\
         match n {{fun _ : nat => nat}}
         [ m
         , fun _ {{nat}} w\ app[ {{S}}, app[add,w,m]]]).
}}.

Elpi Query lp:{{
  coq.locate "plus" (const GR),
  coq.env.const GR _BO TY,
  TY = {{ nat -> nat -> nat }},
  BO1 = (fix _ 0 TY add\
         {{ fun n m => match n with
              | O => m
              | S p => lp:{{ app[add, {{p}}, {{m}}] }}  
            end }}),
  coq.say BO1,
  coq.elaborate BO1 _TY2 BO2,
  coq.say BO2.
}}.

Require Vector.

Elpi Query lp:{{
  T = {{ fun v : Vector.t nat 2 =>
           match v with
           | Vector.nil _ => 0
           | Vector.cons _ _ _ _ => 1
           end }},
  coq.say T,
  coq.elaborate T _TY T1,
  coq.say T1.
}}.

Elpi Query lp:{{ {{ lp:X }} = 3, coq.say X}}.

Elpi Query lp:{{ {{ fun x => lp:X x }} = Y, coq.say Y}}.

Elpi Query lp:{{
X = {{ fun (r : nat) (p : forall y : nat, y = 0 :> nat) (q : bool) => lp:{{ {coq.typecheck {{p}} } }} }}, coq.say X.
}}.



