From elpi Require Import elpi.

Elpi Command test.quotations.

(****** Notations **********************************)

Elpi Query lp:{{
  coq.locate "plus" (const GR),
  coq.env.const GR (some BO) TY,
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

Local Notation inlined_sub_rect :=
  (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px).

Unset Auto Template Polymorphism.
Record is_SUB (T : Type) (P : T -> bool) (sub_sort : Type) := SubType {
    val : sub_sort -> T;
    Sub : forall x, P x = true -> sub_sort;
    Sub_rect : forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
    (* SubK : forall x Px, val (@Sub x Px) = x *)
}.
Axiom leq : nat -> nat -> bool.

Structure ord u := Ord { oval : nat; prop : leq oval u = true }.

Check fun u => SubType _ _ _ (oval u) _ inlined_sub_rect.

Elpi Query lp:{{ std.do! [
  T = {{ fun u => SubType _ _ _ (oval u) _ inlined_sub_rect }},
  std.assert-ok! (coq.elaborate-skeleton T _ T1) "does not typecheck",
  T1 = {{ fun u => SubType _ _ _ _ (lp:K u) _ }},
  std.assert! (K = global GR, coq.locate "Ord" GR) "not the right constructor"
]
}}.

(* unfortunately the error message does not mention "unknown_inductive" *)
Fail Elpi Query lp:{{ std.do! [
  T = {{ fun u => SubType _ _ _ (oval u) _ inlined_sub_rect }},
  std.assert-ok! (coq.typecheck T _) "does not typecheck",
]
}}.

Section A.
Variable A : Type.
Check 1.
Elpi Accumulate lp:{{

pred p i:term.
p {{ A }}.

}}.
End A.