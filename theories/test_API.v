From elpi Require Import elpi.
From Coq Require Vector.


(****** say *************************************)

Elpi Command test.API.

Elpi Accumulate "
test-hello :-
  coq-say ""hello world"",
  coq-warn ""this is a warning"". 
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

Elpi Run "coq-locate-module ""Init.Datatypes"" MP".

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
  coq-gr->id GR S,
  Name is S ^ ""_equal"",
  coq-env-add-const Name BO TY (const NGR),
  coq-env-const NGR BO _, coq-say {coq-gr->id NGR},
  caml-regexp-match ""add_equal"" {coq-gr->id NGR}.
". 
Elpi Run "test-env-add-const".

Check add_equal.

Elpi Run " coq-gr->string ""toto"" ""toto"". ".

Elpi Accumulate "
test-env-add-axiom :-
  coq-locate ""False"" F,
  coq-env-add-const ""myfalse"" axiom F GR,
  coq-say GR.
".
Elpi Run "test-env-add-axiom".

Check myfalse.

Section Dummy.
Variable dummy : nat.

Elpi Command indtest "

main _ :-
  DECL = 
      (parameter ""T"" (sort prop) t\
         parameter ""x"" t x\
           inductive ""myind"" (prod {{:name w}} t _\ sort prop)
             i\ [ constructor ""K1""
                    (prod {{:name y}} t y\ prod _ (app[i,t,x,y]) _\app[i,t,x,x])
                , constructor ""K2""
                    (app[i,t,x,x]) 
                ]
            ),
 coq-env-add-indt DECL (indt GR),
 coq-env-indt GR tt Lno ULno Ty KNames KTypes,
 coq-env-indt->decl Ty Lno (indt GR) KNames KTypes DECL1,
 rename DECL1 NEWDECL,
 coq-env-add-indt NEWDECL _
.

rename (parameter N T F) (parameter N T F1) :-
  pi p\ rename (F p) (F1 p).
rename (inductive Nx T F) (inductive N1 T F1) :-
  N1 is Nx ^ ""1"",
  pi i\ map (F i) (x\r\sigma n n2 t\
        x = constructor n t,
        n2 is n ^ ""1"", r = constructor n2 t) (F1 i).

whd X [] X [].
unwind X [] X.

". 
Elpi Run indtest " true ".
Elpi Run indtest " main _ ".

End Dummy.

Print myind.
Print myind1.

Elpi Run "coq-locate-module ""Datatypes"" MP, coq-env-module MP L".

Module X.
  Inductive i := .
  Definition d := i.
  Module Y.
    Inductive i := .
    Definition d := i.
  End Y.
End X.

Elpi Run "
  coq-locate-module ""X"" MP,
  coq-env-module MP [
    (indt Xi), (const _), (const _), (const _), 
    (const _),
    (indt XYi), (const _), (const _), (const _), 
    (const _)
  ],
  caml-regexp-match ""\\(Top\\|elpi.test_API\\)\\.X\\.i"" {coq-gr->string Xi},
  caml-regexp-match ""\\(Top\\|elpi.test_API\\)\\.X\\.Y\\.i"" {coq-gr->string XYi}
".

Elpi Run "
 do! [
   coq-env-begin-module-type ""TA"",
     coq-env-add-const ""z"" axiom {{nat}} _,
     coq-env-add-const ""i"" axiom {{Type}} _,
   coq-env-end-module-type MP_TA,
   coq-env-begin-module ""A"" MP_TA,
     coq-env-add-const ""x"" {{3}} hole _,
       coq-env-begin-module ""B"" _NoGivenModType,
         coq-env-add-const ""y"" {{3}} hole GRy,
       coq-env-end-module _,
     coq-env-add-const ""z"" GRy hole _,
     coq-env-add-indt (inductive ""i1"" {{Type}} i\ []) I,
     coq-env-add-const ""i"" I hole _, % silly limitation in Coq
   coq-env-end-module MP,
   coq-env-module MP L
   %coq-env-module-type MP_TA [TAz,TAi] % @name is broken wrt =, don't use it!
 ]
".
Print A.
Check A.z.
Check A.i.
Print A.i.
Fail Check A.i1_ind.

Elpi Run "
  coq-env-begin-module ""IA"" _,
  coq-env-include-module {coq-locate-module ""A""},
  coq-env-end-module _.  
".

Print IA.

Elpi Run "
  coq-env-begin-module-type ""ITA"",
  coq-env-include-module-type {coq-locate-module-type ""TA""},
  coq-env-end-module-type _.  
".

Print ITA.

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

(****** TC **********************************)

Require Import Classes.RelationClasses.

Axiom T : Type.
Axiom R : T -> T -> Prop.
Axiom Rr : forall x : T, R x x.

Definition myi : Reflexive R.
Proof.
exact Rr.
Defined.

Check (_ : Reflexive R).

Elpi Run "coq-locate ""myi"" (const GR), coq-TC-declare-instance GR 10 tt.".

Check (_ : Reflexive R).

Elpi Run "coq-TC-db L".
Elpi Run "coq-locate ""RewriteRelation"" (indt GR), coq-TC-db-for GR L".
Elpi Run "coq-locate ""RewriteRelation"" (indt GR), coq-TC-is-class GR".
Elpi Run "coq-locate ""True"" (indt GR), not(coq-TC-is-class GR)".

(****** CS **********************************)

Structure eq := mk_eq { carrier : Type; eq_op : carrier -> carrier -> bool }.

Axiom W : Type.
Axiom Z : W -> W -> bool.
Axiom t : W.

Definition myc : eq := mk_eq W Z.

Fail Check (eq_op _ t t).

Elpi Run "coq-locate ""myc"" (const GR), coq-CS-declare-instance GR.".

Check (eq_op _ t t).

Elpi Run " coq-CS-db L ".

(****** Coercions **********************************)

Axiom C1 : Type.
Axiom C2 : Type.
Axiom c12 : C1 -> C2.
Axiom c1t : C1 -> Type.
Axiom c1f : C1 -> nat -> nat.

Elpi Run "coq-locate ""c12"" (const GR1),
          coq-locate ""c1t"" (const GR2),
          coq-locate ""c1f"" (const GR3),
          coq-locate ""C1""  C1,
          coq-locate ""C2""  C2,
          coq-coercion-declare GR1 C1 C2 tt,
          coq-coercion-declare GR2 C1 (sort _) tt,
          coq-coercion-declare GR3 C1 (prod _ _ _) tt.
	  ".

Check (fun x : C1 => (x : C2)).
Check (fun x : C1 => fun y : x => true).
Check (fun x : C1 => x 3).

(***** Univs *******************************)

Elpi Run "coq-univ-print-constraints.".
Elpi Run "coq-univ-new [] X".
Elpi Run "coq-univ-leq X Y".
Elpi Run "coq-univ-eq X Y".
Elpi Run "coq-univ-max X Y Z".
Elpi Run "coq-univ-sup X Y".





