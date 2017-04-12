From elpi Require Import elpi.

Elpi Init "./" "../elpi/".

Elpi Accumulate File "pervasives.elpi".
Elpi Accumulate File "coq-lib.elpi".

(****** say *************************************)

Elpi Accumulate "
test-hello :-
  coq-say ""hello world"". 
".
Elpi Run "test-hello".

(****** locate **********************************)

(* nametab *)
Elpi Accumulate "
test-locate-nat :-
  coq-locate ""nat"" (indt GR),
  coq-locate ""Datatypes.nat"" (indt GR),
  coq-locate ""Init.Datatypes.nat"" (indt GR),
  coq-locate ""Coq.Init.Datatypes.nat"" (indt GR).
".
Elpi Run "test-locate-nat".

Elpi Accumulate "
test-locate-foobar :-
  coq-locate ""foobar"" _.
".
Fail Elpi Run "test-locate-foobar".

(* syndef *)
Elpi Accumulate "
test-syndef :-
  coq-locate ""plus"" (const GR),
  coq-locate ""Nat.add"" (const GR).
".
Elpi Run "test-syndef".

(****** env **********************************)

Elpi Accumulate "
test-env-const :-
  coq-locate ""plus"" (const GR),
  coq-env-const GR BO TY,
  coq-locate ""nat"" Nat,
  coq-locate ""S"" Succ,
  TY = (prod _ Nat _\ prod _ Nat _\ Nat),
  BO = (fix _ 0 TY add\
         lam _ Nat n\ lam _ Nat m\
         match n (lam _ Nat _\ Nat)
         [ m
         , lam _ Nat w\ app[Succ, app[add,w,m]]]).
".
Elpi Run "test-env-const".

Axiom empty_nat : nat.

Elpi Run "coq-locate ""empty_nat"" (const GR),
          coq-env-const GR axiom TY.
".

Require Vector.

Elpi Accumulate "
test-env-indt :-
  coq-locate ""Vector.t"" Vect, Vect = indt GR,
  coq-locate ""Vector.nil"" Vnil,
  coq-locate ""Vector.cons"" Vcons,
  coq-locate ""nat"" Nat,
  coq-locate ""O"" Zero,
  coq-locate ""S"" Succ,
  coq-env-indt GR tt 1 1 TY [Vnil,Vcons] [Tnil,Tcons],
  TY = (prod _ (sort _) _\ prod _ Nat _\ (sort _)),
  Tnil = (prod _ (sort _) a\ app [Vect,a,Zero]),
  Tcons = (prod _ (sort _) a\
           prod _ a v\
           prod _ Nat n\
           prod _ (app[Vect,a,n]) v\
            app[Vect,a,app[Succ,n]]).
".
Elpi Run "test-env-indt".


Elpi Accumulate "
test-env-indc :-
  coq-locate ""nat"" Nat,
  coq-locate ""S"" Succ,
  coq-locate ""Vector.t"" Vect,
  coq-locate ""Vector.cons"" (indc GR),
  coq-env-indc GR 1 1 
          (prod _ (sort _) a\
           prod _ a v\
           prod _ Nat n\
           prod _ (app[Vect,a,n]) v\
            app[Vect,a,app[Succ,n]]).
".
Elpi Run "test-env-indc".

Elpi Accumulate "
test-env-indc1 :-
  coq-locate ""Vector.nil"" (indc GR),
  coq-env-indc GR 1 0 _.
".
Elpi Run "test-env-indc1".

Section Test.

Variable A : nat.

Elpi Run "
  coq-locate ""Vector.nil"" (indc GR1),
  coq-locate ""nat"" (indt GR2),
  coq-locate ""A"" (const GR3),
  coq-env-typeof-gr GR1 _,
  coq-env-typeof-gr GR2 _,
  coq-env-typeof-gr GR3 _.
".

End Test.

Elpi Accumulate "
test-env-add-const :-
  coq-locate ""plus"" (const GR),
  coq-env-const GR BO TY,
  coq-string-of-gr GR S,
  Name is S ^ ""_equal"",
  coq-env-add-const Name BO TY (const NGR),
  coq-env-const NGR BO _,
  coq-string-of-gr NGR ""add_equal"".
".
Elpi Run "test-env-add-const".

Check add_equal.

(****** typecheck **********************************)

Elpi Accumulate "
test-typecheck-const :-
  coq-locate ""plus"" (const GR),
  coq-env-const GR BO TY,
  coq-typecheck BO TY.
".
Elpi Run "test-typecheck-const".

(****** elaborate **********************************)

Require Import List.

Elpi Accumulate "
test-elaborate-list :-
  coq-locate ""cons"" Cons,
  coq-locate ""nil"" Nil,
  coq-locate ""nat"" Nat,
  coq-locate ""O"" Zero,
  coq-locate ""list"" List,
  L  = app [ Cons, hole, Zero, app [ Nil, hole ]],
  LE = app [ Cons, Nat, Zero, app [ Nil, Nat ]],
  coq-elaborate L LE (app [ List, Nat ]).
".
Elpi Run "test-elaborate-list".

