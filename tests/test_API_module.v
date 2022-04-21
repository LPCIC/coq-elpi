From elpi Require Import elpi.

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
  coq.env.module MP [
    (indt Xi), (const _), (const _), (const _), (const _),
    (const _),
    (indt XYi), (const XYr), (const _), (const _), (const _),
    (const _)
  ],
  coq.say {coq.gref->string (indt Xi)},
  rex_match "\\(Top.\\|.*test_API\\)\\.X\\.i$" {coq.gref->string (indt Xi)},
  rex_match "\\(Top.\\|.*test_API\\)\\.X\\.Y\\.i$" {coq.gref->string (indt XYi)},
  (coq.gref->path (indt XYi) ["test_API", "X", "Y" ] ;
   coq.gref->path (indt XYi) ["elpi", "tests", "test_API", "X", "Y" ] ;
   coq.gref->path (indt XYi) ["Top",           "test_API", "X", "Y" ]),
   coq.say {coq.gref->path (indt XYi)},
   coq.say {coq.gref->path (const XYr)},
  (coq.gref->path (const XYr) ["test_API", "X", "Y" ] ;
   coq.gref->path (const XYr) ["elpi", "tests", "test_API", "X", "Y" ] ;
   coq.gref->path (const XYr) ["Top",           "test_API", "X", "Y" ] )
}}.


Elpi Query lp:{{
 std.do! [
   coq.env.begin-module-type "TA",
     coq.env.add-axiom "z" {{nat}} _,
     coq.env.add-axiom "i" {{Type}} _,
   coq.env.end-module-type MP_TA,
   coq.env.begin-module "A" (some MP_TA),
     coq.env.add-const "x" {{3}} _ _ _,
       coq.env.begin-module "B" none,
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
 std.do! [
   coq.env.begin-module-type "TF",
     coq.env.add-axiom "w" {{nat}} _,
   coq.env.end-module-type MP_TF,
   coq.locate-module-type "TA" MP_TA,
   coq.env.begin-module-functor "F" (some MP_TF) [pr "a" MP_TA, pr "b" MP_TA],
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
 std.do! [
   coq.locate-module-type "TA" MP_TA,
   coq.env.begin-module-type-functor "TB" [pr "A" MP_TA],
   coq.env.end-module-type _
 ]
}}.
Print TB.

Elpi Query lp:{{
  coq.env.begin-module "IA" none,
  coq.env.include-module {coq.locate-module "A"} _,
  coq.env.end-module _.
}}.

Print IA.

Module Tmp.
Elpi Query lp:{{ coq.env.import-module { coq.locate-module "IA" } }}.
Check i.
End Tmp.

Elpi Query lp:{{
  coq.env.begin-module-type "ITA",
  coq.env.include-module-type {coq.locate-module-type "TA"} (coq.inline.at 2),
  coq.env.end-module-type _.  
}}.

Print ITA.

