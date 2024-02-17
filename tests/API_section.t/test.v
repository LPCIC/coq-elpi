From elpi Require Import elpi.

Elpi Command section.

(* section *)

Section SA.
Unset Auto Template Polymorphism.
Variable a : nat.
Inductive ind := K.
Section SB.
Variable b : nat.
Let c := b.
Elpi Query lp:{{
  coq.env.section [CA, CB, CC],
  coq.locate "a" (const CA),
  coq.locate "b" (const CB),
  coq.locate "c" (const CC),
  coq.env.const CC (some (global (const CB))) _,
  coq.env.add-section-variable "d" {{ nat }} _,
  coq.env.add-section-variable "d1" {{ nat }} _,
  @local! => coq.env.add-const "e" {{ 3 }} {{ nat }} _ _.
}}.
About d.
Definition e2 := e.
End SB.
Fail Check d.
Fail Check d1.
Check eq_refl : e2 = 3.
End SA.

Elpi Query lp:{{
  std.do! [ coq.env.begin-section "Foo", coq.env.end-section ]  
}} lp:{{
  coq.env.begin-section "Foo",
  coq.env.add-section-variable "x" {{ nat }} X,
  coq.env.section [X],
  coq.env.add-const "fx" (global (const X)) _ _ _,
  coq.env.end-section.
}}.

Check fx : nat -> nat.

Elpi Query lp:{{
  coq.env.add-const "opaque_3" {{ 3 }} _ @opaque! _
}}.

About opaque_3.

Fail Elpi Query lp:{{
  coq.env.add-const "opaque_illtyped" {{ 3 3 }} _ @opaque! _
}}.
Fail Elpi Query lp:{{
  coq.env.add-const "opaque_illtyped" {{ S True }} _ @opaque! _
}}.

(************* using ********************)
Section Using.
Variable A : bool.
Elpi Query lp:{{ coq.env.add-const "foo" {{ 3 }} {{ nat }} @transparent! _ }}.
Elpi Query lp:{{ @using! "All" => coq.env.add-const "bar" {{ 3 }} {{ nat }} @transparent! _ }}.
End Using.
Check foo : nat.
Check bar : bool -> nat.

