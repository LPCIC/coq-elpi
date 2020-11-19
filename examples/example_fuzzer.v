From elpi Require Import elpi.

(** Intrinsically typed data type and semantics, from software foundations.

   We devise a command to fuzz the semantics by flipping some operators.
   We do it by locally checking that the fuzzing produces welltyped terms,
   reducing a bit the nondeterminism of the fuzzer.
*)

Inductive ty := B | N.

Inductive Exp : ty -> Type :=
| NUM  : nat -> Exp N
| BOOL  : bool -> Exp B
| PLUS : Exp N -> Exp N -> Exp N
| AND : Exp B -> Exp B -> Exp B
| OR : Exp B -> Exp B-> Exp B
| EQ : Exp N -> Exp N -> Exp B.

Inductive Val : ty -> Set :=
   | iNv : nat -> Val N
   | iBv : bool -> Val B.

Inductive eval  : forall {T: ty}, Exp  T -> Val T -> Prop :=
   | E_Num n :
       eval (NUM  n) (iNv n)
   | E_Bool b :
       eval (BOOL  b) (iBv b)
   | E_Plus e1 e2 n1 n2 :
       eval e1 (iNv n1) ->
       eval e2 (iNv n2) ->
       eval (PLUS e1 e2) (iNv (n1 + n2))
   | E_AND e1 e2 b1 b2 :
       eval e1 (iBv b1) ->
       eval e2 (iBv b2) ->
       eval (AND e1 e2) (iBv (b1 && b2))
   | E_OR e1 e2 b1 b2 :
       eval e1 (iBv b1) ->
       eval e2 (iBv b2) ->
       eval (OR e1 e2) (iBv (b1 || b2))
  | E_EQ e1 e2 n1 n2 :
       eval e1 (iNv n1) ->
       eval e2 (iNv n2) ->
       eval (EQ e1 e2) (iBv (Nat.eqb n1 n2)).

Elpi Command fuzz.
Elpi Accumulate lp:{{

pred fuzz i:term, o:term.

% fuzzin rule: we look for a Coq term (?Op ?A ?B) and we turn it in (AND ?A ?B)
% only if the new term is well typed.
fuzz {{ lp:Op lp:A lp:B }} Fuzzed :-
  coq.say "DEBUG: attempt at fuzzing binary op:" Op,
  fuzz A A1, fuzz B B1,
  Fuzzed = {{ AND lp:A1 lp:B1 }},
  coq.typecheck Fuzzed _ ok, % we don't care about the type, only that it is ok
  coq.say "DEBUG: fuzzed!".

% rule for the dependent function space
fuzz (prod N S T) (prod N S1 T1) :-
  fuzz S S1,
  % we load the context with types for x and y, as well as the fact that
  % we fuzz x to y
  pi x y\ decl x N S => decl y N S1 => fuzz x y => fuzz (T x) (T1 y).

% rule for application
fuzz (app L) (app L1) :- std.map L fuzz L1.

% rule for global constants
fuzz (global GR UI) (global GR UI).

% TODO: we should have clauses for all other type formers...

pred rename-constructors i:constructor, o:pair constructor string.
rename-constructors C (pr C C1) :-
  coq.gref->id (indc C) S,
  C1 is S ^ "1".

main [str IN, str OUT ] :-
  % locate the inductive
  coq.locate IN (indt I),
  % fetch all its data, in particulat the types of the constructors
  coq.env.indt I _ B NP NPU A KN KT,
  % fuzz all constructor types
  std.map KT fuzz KT1,
  % we rename them, otherwise Coq complains the names are already used
  std.map KN rename-constructors KN1,
  % declare the new inductive
  coq.build-indt-decl (pr I OUT) B NP NPU A KN1 KT1 Decl,
  coq.env.add-indt Decl _.

}}.
Elpi Typecheck.

Elpi fuzz eval eval1.

(* let's print our new, broken, semantics ;-) *)
Print eval1.