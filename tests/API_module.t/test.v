From elpi Require Import elpi.

Elpi Command modules.

(* module *)

Elpi Query lp:{{ coq.locate-module "Datatypes" MP, coq.env.module MP L }}.

Module X.
  Unset Auto Template Polymorphism.
  Inductive i := .
  Definition d := i.
  Module Y.
    Inductive i := .
    Definition d := i.
  End Y.
End X.

Elpi Query lp:{{
  coq.locate-module "X" MP,
  coq.env.module MP L,
  std.assert! (L = [
    gref (indt Xi), gref (const _), gref (const _), gref (const _), gref (const _),
    gref (const _),
    submodule _ [
      gref (indt XYi), gref (const XYr), gref (const _), gref (const _), gref (const _),
    gref (const _)]
  ]) "bad module",
  coq.say {coq.gref->string (indt Xi)},
  rex_match "\\(Top.\\|.*test_API_module\\)\\.X\\.i$" {coq.gref->string (indt Xi)},
  rex_match "\\(Top.\\|.*test_API_module\\)\\.X\\.Y\\.i$" {coq.gref->string (indt XYi)},
  (coq.gref->path (indt XYi) ["test_API_module", "X", "Y" ] ;
   coq.gref->path (indt XYi) ["elpi", "tests", "test_API_module", "X", "Y" ] ;
   coq.gref->path (indt XYi) ["Top",           "test_API_module", "X", "Y" ]),
   coq.say {coq.gref->path (indt XYi)},
   coq.say {coq.gref->path (const XYr)},
  (coq.gref->path (const XYr) ["test_API_module", "X", "Y" ] ;
   coq.gref->path (const XYr) ["elpi", "tests", "test_API_module", "X", "Y" ] ;
   coq.gref->path (const XYr) ["Top",           "test_API_module", "X", "Y" ] )
}}.

Module Y.
  Inductive i := with j := Kj.
End Y.

Elpi Query lp:{{ 
    coq.locate-module "Y" MP,
    coq.env.module MP [gref (indt I), gref (indt J), |_],
    coq.gref->path (indt I) P,
    coq.gref->id (indt J) ID
}}.

Elpi Query lp:{{
  std.do! [
    coq.env.begin-module-type "TA",
    coq.env.end-module-type Mp_ta,
    coq.env.begin-module "A" (some Mp_ta),
      coq.env.begin-module "B" none,
      coq.env.end-module _,
    coq.env.end-module _,
   ]
}} lp:{{
 std.do! [
   coq.env.begin-module-type "TA",
     coq.env.add-axiom "z" {{nat}} _,
     coq.env.add-axiom "i" {{Type}} _,
   coq.env.end-module-type MP_TA,
   coq.env.begin-module "A" _,
     coq.env.add-const "x" {{3}} _ _ _,
       coq.env.begin-module "B" _,
         coq.env.add-const "y" {{3}} _ _ GRy,
       coq.env.end-module _,
     coq.env.add-const "z" (global (const GRy)) _ _ _,
     coq.env.add-indt (inductive "i1" _ (arity {{Type}}) i\ []) I,
     coq.env.add-const "i" (global (indt I)) _ _ _, % silly limitation in Coq
   coq.env.end-module MP,
   coq.env.module MP L
   %coq.env.module-type MP_TA [TAz,TAi] % name is broken wrt =, don't use it!
 ]
}}.
Print A.
Check A.z.
Check A.i.
Print A.i.
Fail Check A.i1_ind.

Elpi Query lp:{{
  coq.locate-module-type "TA" MP_TA,
  std.do! [
    coq.env.begin-module-type "TF",
    coq.env.end-module-type TF,
    coq.env.begin-module-functor "F" (some TF) [pr "a" MP_TA, pr "b" MP_TA],
      coq.locate-module "a" A,
      coq.env.import-module A,
    coq.env.end-module _,
  ]
}} lp:{{
 std.do! [
   coq.env.begin-module-type "TF",
     coq.env.add-axiom "w" {{nat}} _,
   coq.env.end-module-type MP_TF,
   coq.locate-module-type "TA" MP_TA,
   coq.env.begin-module-functor "F" _ _,
   coq.env.import-module {coq.locate-module "a"},
   coq.env.add-const "w" (global {coq.locate "z"}) _ _ _,
   coq.env.end-module _
 ]
}}.
Print F.
Module B := F A A.
Print B.
Print B.w.

Elpi Query lp:{{
  coq.locate-module-type "TA" MP_TA,
  std.do! [
    coq.env.begin-module-type-functor "TB" [pr "A" MP_TA],
    coq.env.end-module-type _,
  ]  
}} lp:{{
 std.do! [
   coq.env.begin-module-type-functor "TB" _,
   coq.env.end-module-type _
 ]
}}.
Print TB.

Elpi Query lp:{{ std.do! [
  coq.locate-module "A" A,
  coq.env.begin-module "IA" none,
  coq.env.include-module A _,
  coq.env.end-module _,
]
}} lp:{{
  coq.env.begin-module "IA" _,
  coq.env.include-module {coq.locate-module "A"} _,
  coq.env.end-module _.
}}.

Print IA.

Module Tmp.
Elpi Query
lp:{{
  std.do! [coq.env.import-module { coq.locate-module "IA" }]
}} lp:{{
  coq.env.import-module { coq.locate-module "IA" }
}}.
Check i.
End Tmp.

Elpi Query lp:{{
  std.do! [
    coq.env.begin-module-type "ITA",
    coq.env.include-module-type {coq.locate-module-type "TA"} (coq.inline.at 2),
    coq.env.end-module-type _,
  ]
}} lp:{{
  coq.env.begin-module-type "ITA",
  coq.env.include-module-type {coq.locate-module-type "TA"} _,
  coq.env.end-module-type _.  
}}.

Print ITA.


Module R.
  Module S.
    Definition x := 3.
  End S.
  Module Type P1.
    Parameter x : nat.
  End P1.
  Module Type P2.
    Parameter y : nat.
  End P2.
  Module F(A : P1)(B : P2).
    Definition z := A.x + B.y.
  End F.
  Module Type FT(A : P2)(B : P1).
    Definition z := A.y + B.x.
  End FT.
  Definition a := 1.
End R.

Elpi Query lp:{{
  coq.locate-module "R" R,
  coq.locate-module "R.S" S,
  coq.locate-module-type "R.P1" P1,
  coq.locate-module-type "R.P2" P2,
  coq.locate-module "R.F" F,
  coq.locate-module-type "R.FT" FT,
  coq.env.module R L,
  std.assert! (L = [
    submodule S [gref (const _)], 
    module-type P1, 
    module-type P2, 
    module-functor F [P1,P2],
    module-type-functor FT [P2,P1], 
    gref (const _)
  ]) "bad module"
}}.
