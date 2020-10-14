From elpi Require Import elpi.

Elpi Command test.quotations.

(****** Notations **********************************)

Elpi Query lp:{{
  coq.locate "plus" (const GR),
  coq.env.const GR _ (some BO) TY,
  TY = {{ nat -> nat -> nat }},
  BO = (fix _ 0 TY add\
         fun _ {{nat}} n\ fun _ {{nat}} m\
         match n {{fun _ : nat => nat}}
         [ m
         , fun _ {{nat}} w\ app[ {{S}}, app[add,w,m]]]).
}}.

Elpi Query lp:{{
  coq.locate "plus" (const GR),
  coq.env.const GR _ _BO TY,
  TY = {{ nat -> nat -> nat }},
  BO1 = (fix _ 0 TY add\
         {{ fun n m : nat => match n with
              | O => m
              | S p => lp:{{ app[add, {{p}}, {{m}}] }}  
            end }}),
  coq.say BO1,
  coq.typecheck BO1 _TY2 ok,
  coq.say BO1.
}}.

Require Vector.

Elpi Query lp:{{
  T = {{ fun v : Vector.t nat 2 =>
           match v with
           | Vector.nil _ => 0
           | Vector.cons _ _ _ _ => 1
           end }},
  coq.say T,
  coq.typecheck T _TY ok,
  coq.say T.
}}.

Elpi Query lp:{{ {{ lp:X }} = 3, coq.say X}}.

Elpi Query lp:{{ {{ fun x => lp:X x }} = Y, coq.say Y}}.
Elpi Program xxx lp:{{
pred of i:term, o:term.
of X T :- coq.typecheck X T ok.
}}.
Elpi Query lp:{{
X = {{ fun (r : nat) (p : forall y : nat, y = 0 :> nat) (q : bool) => lp:{{ {of {{p}} } }} }}, coq.say X.
}}.



