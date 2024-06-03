From Coq Require Import Bool.
From elpi Require Import elpi.

Elpi Command foo.
#[synterp] Elpi Accumulate lp:{{ main-synterp X X :- coq.say "synterp" X.  }}.
Elpi Accumulate lp:{{ main-interp X Y :- coq.say "interp" X, std.assert! (X = Y) "bug". }}.
Elpi Typecheck.

Elpi foo X.
Elpi foo 1.
Elpi foo (1).
Elpi foo Definition x (P Q : bool) : nat := 0.
Elpi foo Axiom x (P Q : bool) : nat.
Elpi foo Record x (P Q : bool) := K { f1 : nat; f2 : f1 = f1 }.
Elpi foo Inductive x (P : bool) | (Q : bool)  : nat -> Type := K : nat -> x Q 3 | R (w : bool) : x Q 1 .
Elpi foo Context (A : nat) (B : bool).

Elpi Export foo.

foo X.
foo 1.
foo (1).
foo Definition x (P Q : bool) : nat := 0.
foo Axiom x (P Q : bool) : nat.
foo Record x (P Q : bool) := K { f1 : nat; f2 : f1 = f1 }.
foo Inductive x (P : bool) | (Q : bool)  : nat -> Type := K : nat -> x Q 3 | R (w : bool) : x Q 1 .
foo Context (A : nat) (B : bool).

Elpi Command start.
#[synterp] Elpi Accumulate lp:{{
  main-synterp [str X] _ :- coq.env.begin-module X none.
}}.
Elpi Accumulate lp:{{
  main [str X] :- coq.env.begin-module X _.
}}.

Elpi Command stop.
#[synterp] Elpi Accumulate lp:{{
  main-synterp [str X] _ :- coq.env.end-module _.
}}.
Elpi Accumulate lp:{{
  main [str X] :- coq.env.end-module _.
}}.
Elpi start "X".
Definition a:= 1.
About a.
(* End X. bug vernacextend push/pop *)
Elpi stop "X".


Elpi Command module.
#[synterp] Elpi Accumulate lp:{{
  main [str X] :- coq.env.begin-module X none, coq.env.end-module _.
}}.
Elpi Accumulate lp:{{
  main [str X] :- coq.env.begin-module X _, coq.env.add-const "a" {{1}} _ _ _, coq.env.end-module _.
}}.
Elpi module "A".

Print Module X.
Print Module A.

Elpi Command err.
Elpi Accumulate lp:{{
  main [str X] :- coq.env.begin-module X none, coq.env.end-module _.
}}.
Fail Elpi err "C".




Elpi Command module2.
#[synterp] Elpi Accumulate lp:{{
  main [str X, str Y] :- 
      coq.env.begin-module X none,
      coq.env.end-module M,
      coq.env.import-module M,
      coq.env.begin-module Y none,
      coq.env.end-module _.
}}.
Elpi Accumulate lp:{{
  main [str X, str Y] :-
    coq.env.begin-module X _,
      coq.env.add-const "a" {{1}} _ _ _,
    coq.env.end-module M,
    coq.env.import-module M,
    coq.env.begin-module Y _,
    coq.env.end-module _.

}}.
Elpi Typecheck.
Elpi module2 "B" "C".
Check a.

#[both] Elpi Db acc.db lp:{{
pred p o:int.
}}.
Elpi Command acc.
#[both] Elpi Accumulate Db acc.db.
#[synterp] Elpi Accumulate lp:{{
  main [int N] :-
    @local! => coq.elpi.accumulate _ "acc.db" (clause _ _ (p N)),
    coq.env.begin-module "TMP" none,
    true
    .
}}.
#[interp] Elpi Accumulate lp:{{
  main _ :-
    coq.env.begin-module "TMP" none,
    true.
}}.
Elpi Export acc.

Elpi Command pr.
#[both] Elpi Accumulate Db acc.db.
#[synterp] Elpi Accumulate lp:{{
  main [int N] :-
    std.findall (p X_) L, coq.say "L=" L, std.assert! (std.length L N) "wtf",
    coq.env.end-module _,
    true.
}}.
#[interp] Elpi Accumulate lp:{{
  main _ :-
    coq.env.end-module _,
    true.
}}.
Elpi Export pr.

acc 1.
pr 1.

(* ********************************************* *)

Elpi Command test_data.
#[synterp] Elpi Accumulate lp:{{
  type foo int.
  main-synterp _ R :- R = foo. % std.do!.
}}.
#[interp] Elpi Accumulate lp:{{
  type foo int.
  main-interp _ R :- std.assert! (std.any->string R "foo") "bug".
}}.
Elpi Typecheck.
Elpi Export test_data.

test_data.



Elpi Db db1 lp:{{ pred x i:int. }}.
#[synterp] Elpi Db db2 lp:{{ pred x i:int. }}.
Elpi Command bug.
Elpi Accumulate Db db1.
#[synterp] Elpi Accumulate Db db2.

Elpi Accumulate lp:{{ main _. }}.
#[synterp] Elpi Accumulate lp:{{ main _. }}.

Elpi Typecheck.

(* ********************************************* *)

Set Implicit Arguments.
Elpi Command foo3.
Elpi Accumulate lp:{{
  main _ :-
    D = (record "foo" {{ Type }} "mkfoo" (field [] "f" {{ Type }} _\end-record)),
    coq.typecheck-indt-decl D ok,
    coq.env.add-indt D I, coq.env.begin-module "x" none, coq.env.end-module _.
}}.
#[synterp] Elpi Accumulate lp:{{
  main _ :- coq.env.begin-module "x" none, coq.env.end-module _.
}}.
Elpi foo3.

(* The example below is taken from https://github.com/LPCIC/coq-elpi/issues/618.
   It tests that the initial synterp state during the interp phase corresponds
   to the initial synterp state as opposed to the final synterp state. *)

Class c := C {}.
Definition h : c := C.

Elpi Command ElpiStart.
#[synterp] Elpi Accumulate lp:{{/*(*/
    main _ :-
        coq.env.begin-section "A".
/*)*/}}.
Elpi Accumulate lp:{{/*(*/
    main _ :-
        coq.env.begin-section "A".
/*)*/}}.
Elpi Typecheck.
Elpi Export ElpiStart.

Elpi Command ElpiTCEnd.
#[synterp] Elpi Accumulate lp:{{/*(*/
    main _ :-
        coq.env.end-section.
/*)*/}}.
Elpi Accumulate lp:{{/*(*/
    main _ :-
        coq.locate "h" I,
        @global! => coq.TC.declare-instance I 0,
        coq.env.end-section.
/*)*/}}.
Elpi Typecheck.
Elpi Export ElpiTCEnd.

ElpiStart.

ElpiTCEnd.
