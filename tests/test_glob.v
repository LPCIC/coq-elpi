From elpi Require Import elpi.

Definition d1 := 3.
Inductive i1 : Prop := k1.
Record r1 : Type := { f1 : nat; _ : f1 = 1 }.
Section A. Variable v : nat. End A.
Module N1. End N1. Module M1 := N1.

Elpi Command test.
#[synterp] Elpi Accumulate lp:{{
  main _ :- std.do! [ coq.env.begin-section "A", coq.env.end-section, coq.env.begin-module "N2" none, coq.env.end-module _].
}}.
Elpi Accumulate lp:{{
    main _ :-
      coq.env.add-const "d2" {{ 3 }} _ _ _,
      coq.env.add-indt (inductive "i2" tt (arity {{ Prop }}) i\[constructor "k2" (arity i) ]) _,
      coq.env.add-indt (record "r2" {{ Type }} "_" (
        field _ "f2" {{ nat }} f2\
        field _ _ {{ @eq nat lp:f2 1 }} _\
        end-record)) _,
      coq.env.begin-section "A",
      coq.env.add-section-variable "v" {{ nat }} _,
      coq.env.end-section,
      coq.env.begin-module "N2" none,
      coq.env.end-module _,
      true.
}}.
Elpi Typecheck.
Elpi Export test.
test.
Check d1. Check d2.
Check i1. Check i2.
Check k1. Check k2.
Check r1. Check r2.
Check f1. Check f2. 
Module M2 := N2.
