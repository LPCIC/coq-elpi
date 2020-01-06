From elpi Require Import elpi.
From Coq Require Vector.

Elpi Command test.API.

(****** typecheck **********************************)

Elpi Query lp:{{
  coq.locate "plus" (const GR),
  coq.env.const GR (some BO) TY,
  coq.typecheck BO TY.
}}.

Elpi Query lp:{{
  pi x w z\
    decl x `x` {{ nat }} =>
    def z `z` {{ nat }} x =>
    (coq.say z,
     coq.typecheck z T,
     coq.say T,
     coq.say {coq.term->string z},
     coq.say {coq.term->string T}).
}}.

Elpi Query lp:{{
  pi x w z\
    decl x `x` {{ nat }} =>
    decl w `w` {{ nat }} =>
    def z `z` {{ nat }} w =>
    (coq.say z,
     coq.typecheck z T,
     coq.say T,
     coq.say {coq.term->string z},
     coq.say {coq.term->string T}).
}}.


Elpi Query lp:{{
  coq.version V MA MI P,
  std.assert! (MA = 8 ; MA = 9) "Coq major version not 8 or 9",
  std.assert! (MI >= 0 ; MI < 20) "Coq minor version not in 0 - 20",
  % std.assert! (P >= 0 ; P > -5) "Coq never made so many betas",
  coq.say "Coq version:" V "=" MA "." MI "." P.
}}.


(****** say *************************************)

Elpi Query lp:{{
  coq.say "hello world"
}}.

Elpi Query lp:{{
  coq.warn "this is a warning". 
}}.

(****** locate **********************************)

(* nametab *)
Elpi Query lp:{{
  coq.locate "nat"                    (indt GR),
  coq.locate "Datatypes.nat"          (indt GR),
  coq.locate "Init.Datatypes.nat"     (indt GR),
  coq.locate "Coq.Init.Datatypes.nat" (indt GR).
}}.

Fail Elpi Query lp:{{
  coq.locate "foobar" _.
}}.

Elpi Query lp:{{
  coq.locate "plus"    (const GR),
  coq.locate "Nat.add" (const GR),
  coq.locate-module "Init.Datatypes" MP.
}}.

(****** env **********************************)

(* constant *)

Elpi Query lp:{{
  coq.locate "plus" (const GR),
  coq.env.const GR (some BO) TY,
  coq.locate "nat" GRNat, Nat = global GRNat,
  coq.locate "S" GRSucc, Succ = global GRSucc,
  TY = (prod _ Nat _\ prod _ Nat _\ Nat),
  BO = (fix _ 0 TY add\
         fun _ Nat n\ fun _ Nat m\
         match n (fun _ Nat _\ Nat)
         [ m
         , fun _ Nat w\ app[Succ, app[add,w,m]]]).
}}.

Axiom empty_nat : nat.

Elpi Query lp:{{
  coq.locate "empty_nat" (const GR),
  coq.env.const GR none TY.
}}.

Section Test.

Variable A : nat.

Elpi Query lp:{{
  coq.locate "Vector.nil" GR1,
  coq.locate "nat"        GR2,
  coq.locate "A"          GR3,
  coq.env.typeof-gr GR1 _,
  coq.env.typeof-gr GR2 _,
  coq.env.typeof-gr GR3 _.
}}.

End Test.

Elpi Query lp:{{
  coq.locate "plus" (const GR),
  coq.env.const GR (some BO) TY,
  coq.gr->id (const GR) S,
  Name is S ^ "_equal",
  coq.env.add-const Name BO TY @opaque! _ NGR,
  coq.env.const-opaque? NGR,
  coq.env.const NGR none _, coq.say {coq.gr->id (const NGR)},
  coq.env.const-body NGR (some BO),
  rex_match "add_equal" {coq.gr->id (const NGR)}.
}}.

About add_equal.

(* axiom *)

Elpi Query lp:{{
  coq.locate "False" F,
  coq.env.add-const "myfalse" _ (global F) _ _ GR,
  coq.env.const-opaque? GR,
  coq.env.const GR none _,
  coq.env.const-body GR none,
  coq.say GR.
}}.

Check myfalse.

(* record *)
Set Printing Universes.
Elpi Query lp:{{
  DECL = 
    (parameter `T` {{Type}} t\
       record "eq_class" {{Type}} "mk_eq_class" (
            field @coercion! "eq_f"     {{bool}} f\
            field _          "eq_proof" {{lp:f = lp:f :> bool}} _\
       end-record)),
 coq.say DECL,
 coq.env.add-indt DECL GR.
}}.

Print eq_class.
Check (fun x : eq_class nat => (x : bool)).


(* inductive *)

Section Dummy.
Variable dummy : nat.

Elpi Command indtest.
Elpi Accumulate lp:{{
shorten std.{ map }.
main _ :-
  DECL = 
      (parameter `T` (sort prop) t\
         parameter `x` t x\
           inductive "myind" 0 (prod `w` t _\ sort prop)
             i\ [ constructor "K1"
                    (prod `y` t y\ prod _ (app[i,y]) _\app[i,x])
                , constructor "K2"
                    (app[i,x]) 
                ]
            ),
 coq.env.add-indt DECL GR,
 coq.env.indt GR IsInd Lno ULno Ty KNames KTypes,
 std.map KNames rename KNames1,
 coq.env.indt->decl (pr GR "myind1") IsInd Lno ULno Ty KNames1 KTypes DECL1,
  coq.say DECL1,
 coq.env.add-indt DECL1 _
.

pred rename i:@constructor, o:pair @constructor string.
rename C (pr C S) :-
  coq.gr->id (indc C) K,
  S is K ^ "1".
}}.
Elpi Query indtest lp:{{ main _ }}.

End Dummy.

Print myind.
Print myind1.

Elpi Query lp:{{
  coq.env.add-indt (parameter `X` {{Type}} x\
                      inductive "nuind" 1 {{ forall n : nat, bool -> Type }} i\
                       [constructor "k1" (prod `n` {{nat}} n\ (app[i,n,{{true}}]))
                       ,constructor "k2" (prod `n` {{nat}} n\
                                             prod `x` (app[i,{{1}},{{false}}]) _\
                                              (app[i,n,{{false}}]))
                       ]) _.
                       

}}.


Check fun x : nuind nat 3 false =>
       match x in nuind _ _ b return @eq bool b b with
       | k1 _ _ => (eq_refl : true = true)
       | k2 _ _ x => (fun w : nuind nat 1 false => (eq_refl : false = false)) x
       end.

Fail Check fun x : nuind nat 3 false =>
       match x in nuind _ i_cannot_name_this b return @eq bool b b with
       | k1 _ _ => (eq_refl : true = true)
       | k2 _ _ x => (fun w : nuind nat 1 false => (eq_refl : false = false)) x
       end.

Elpi Query lp:{{
  pi x\ decl x `x` {{ nat }} => coq.elaborate x T (R x), coq.say x (R x).
}}.


Elpi Query lp:{{
  D = (parameter `A` {{ Type }} a\
     inductive "tx" 1 {{ nat -> bool -> Type }} t\
       [ constructor "K1x" {{ forall y : nat,
           forall (x : lp:a) (n : nat) (p : @eq nat (S n) y) (e : lp:t n true),
           lp:t y true }}
       , constructor "K2x" {{ forall y : nat,
           lp:t y false }} ]),
  coq.elaborate-indt-decl D D1,
  coq.env.add-indt D1 _.
}}.

(*
Inductive t (A : Type) (y : nat) : bool -> Type :=
    K1x (x : A) n (p : S n = y) (e : t A n true) : t A y true
  | K2x : t A y false.
*)

(* module *)

Elpi Query lp:{{ coq.locate-module "Datatypes" MP, coq.env.module MP L }}.

Module X.
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
    (indt Xi), (const _), (const _), (const _), 
    (const _),
    (indt XYi), (const _), (const _), (const _), 
    (const _)
  ],
  rex_match "\\(Top\\|elpi.tests.test_API\\)\\.X\\.i" {coq.gr->string (indt Xi)},
  rex_match "\\(Top\\|elpi.tests.test_API\\)\\.X\\.Y\\.i" {coq.gr->string (indt XYi)},
  (coq.gr->path (indt XYi) ["elpi", "tests", "test_API", "X", "Y", "i" ] ;
   coq.gr->path (indt XYi) ["Top",           "test_API", "X", "Y", "i" ])
}}.

Elpi Query lp:{{
 std.do! [
   coq.env.begin-module-type "TA",
     coq.env.add-const "z" _ {{nat}} _ _ _,
     coq.env.add-const "i" _ {{Type}} _ _ _,
   coq.env.end-module-type MP_TA,
   coq.env.begin-module "A" (some MP_TA),
     coq.env.add-const "x" {{3}} _ _ _ _,
       coq.env.begin-module "B" none,
         coq.env.add-const "y" {{3}} _ _ _ GRy,
       coq.env.end-module _,
     coq.env.add-const "z" (global (const GRy)) _ _ _ _,
     coq.env.add-indt (inductive "i1" 0 {{Type}} i\ []) I,
     coq.env.add-const "i" (global (indt I)) _ _ _ _, % silly limitation in Coq
   coq.env.end-module MP,
   coq.env.module MP L
   %coq.env.module-type MP_TA [TAz,TAi] % @name is broken wrt =, don't use it!
 ]
}}.
Print A.
Check A.z.
Check A.i.
Print A.i.
Fail Check A.i1_ind.

Elpi Query lp:{{
  coq.env.begin-module "IA" none,
  coq.env.include-module {coq.locate-module "A"},
  coq.env.end-module _.  
}}.

Print IA.

Module Tmp.
Elpi Query lp:{{ coq.env.import-module { coq.locate-module "IA" } }}.
Check i.
End Tmp.

Elpi Query lp:{{
  coq.env.begin-module-type "ITA",
  coq.env.include-module-type {coq.locate-module-type "TA"},
  coq.env.end-module-type _.  
}}.

Print ITA.

(* section *)

Section SA.
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
  coq.env.add-const "d" _ {{ nat }} _ @local! _,
  coq.env.add-const "e" {{ 3 }} {{ nat }} _ @local! _.
}}.
About d.
Definition e2 := e.
End SB.
Fail Check d.
Check eq_refl : e2 = 3.
End SA.

Elpi Query lp:{{
  coq.env.begin-section "Foo",
  coq.env.add-const "x" _ {{ nat }} _ @local! X,
  coq.env.section [X],
  coq.env.add-const "fx" (global (const X)) _ _ _ _,
  coq.env.end-section.
}}.

Check fx : nat -> nat.


(****** elaborate **********************************)

Require Import List.

Elpi Query lp:{{
  coq.locate "cons" GRCons, Cons = global GRCons,
  coq.locate "nil" GRNil, Nil = global GRNil,
  coq.locate "nat" GRNat, Nat = global GRNat,
  coq.locate "O" GRZero, Zero = global GRZero,
  coq.locate "list" GRList, List = global GRList,
  L  = app [ Cons, _, Zero, app [ Nil, _ ]],
  LE = app [ Cons, Nat, Zero, app [ Nil, Nat ]],
  coq.elaborate L (app [ List, Nat ]) LE.
}}.

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

Elpi Query lp:{{coq.locate "myi" GR, coq.TC.declare-instance GR 10 tt. }}.

Check (_ : Reflexive R).

Elpi Query lp:{{coq.TC.db L}}.
Elpi Query lp:{{coq.locate "RewriteRelation" GR, coq.TC.db-for GR L}}.
Elpi Query lp:{{coq.locate "RewriteRelation" GR, coq.TC.class? GR}}.
Elpi Query lp:{{coq.locate "True" GR, not(coq.TC.class? GR)}}.

(****** CS **********************************)

Structure eq := mk_eq { carrier : Type; eq_op : carrier -> carrier -> bool; _ : nat }.

Axiom W : Type.
Axiom Z : W -> W -> bool.
Axiom t : W.

Definition myc : eq := mk_eq W Z 3.

Fail Check (eq_op _ t t).

Elpi Query lp:{{coq.locate "myc" GR, coq.CS.declare-instance GR.}}.

Check (eq_op _ t t).

Elpi Query lp:{{ coq.CS.db L }}.

Elpi Query lp:{{
  coq.locate "eq" (indt I),
  coq.CS.canonical-projections I [some P1, some P2, none],
  coq.locate "carrier" (const P1),
  coq.locate "eq_op" (const P2)
}}.

(****** Coercions **********************************)

Axiom C1 : Type.
Axiom C2 : Type.
Axiom c12 : C1 -> C2.
Axiom c1t : C1 -> Type.
Axiom c1f : C1 -> nat -> nat.

Elpi Query lp:{{
  coq.locate "c12" GR1,
  coq.locate "c1t"   GR2,
  coq.locate "c1f"   GR3,
  coq.locate "C1"    C1,
  coq.locate "C2"    C2,
  coq.coercion.declare (coercion GR1 _ C1 (grefclass C2)) tt,
  coq.coercion.declare (coercion GR2 _ C1 sortclass) tt,
  coq.coercion.declare (coercion GR3 _ C1 funclass) tt.
}}.

Check (fun x : C1 => (x : C2)).
Check (fun x : C1 => fun y : x => true).
Check (fun x : C1 => x 3).

Elpi Query lp:{{coq.coercion.db L}}.

(***** Syndef *******************************)

Elpi Query lp:{{
    coq.notation.add-abbreviation "abbr" 2
      {{ fun x _ => x = x }} tt tt
}}.

About abbr.
Check abbr 4 3.

Elpi Query lp:{{
  coq.notation.add-abbreviation "abbr2" 1
    {{ fun x _ => x = x }} tt tt
}}.

About abbr2.
Check abbr2 2 3.

(***** Impargs *******************************)

Module X2.

Axiom imp : forall T (x:T), x = x -> Prop.
Arguments imp {_} [_] _ , [_] _ _ .

Elpi Query lp:{{
    coq.locate "imp" I,
    coq.arguments.implicit I
      [[maximal,implicit,explicit], [implicit,explicit,explicit]],
    coq.arguments.set-implicit I 
      [[]] 
       tt,
    coq.arguments.implicit I
      [[explicit,explicit,explicit]]
}}.
End X2.
About X2.imp.

(***** Argnames/scopes/simpl *******************************)

Definition f T (x : T) := x = x.

Elpi Query lp:{{
  coq.arguments.set-name     {coq.locate "f"} [some "S"] _,
  coq.arguments.name         {coq.locate "f"} [some "S"],
  coq.arguments.set-implicit {coq.locate "f"} [[implicit]] _,
  coq.arguments.set-scope    {coq.locate "f"} [some "type"] _,
  coq.arguments.scope        {coq.locate "f"} [some "type_scope"]
}}.
About f.
Check f (S:= bool * bool).

Elpi Query lp:{{
  coq.arguments.simplification {coq.locate "f"} [] _ [],
  coq.arguments.set-simplification {coq.locate "f"} [] (some 1) [] _
}}.
About f.
Check f (S:= bool * bool).


(***** Univs *******************************)

Elpi Query lp:{{coq.univ.print}}.
Elpi Query lp:{{coq.univ.new [] X}}.
Elpi Query lp:{{coq.univ.leq X Y}}.
Elpi Query lp:{{coq.univ.eq X Y}}.
Elpi Query lp:{{coq.univ.max X Y Z}}.
Elpi Query lp:{{coq.univ.sup X Y}}.


(***** Univs *******************************)
 
Elpi Db test.db lp:{{type foo string -> prop.}}.
Elpi Command test.use.db.
Elpi Accumulate Db test.db.
Elpi Accumulate lp:{{
  main [] :-
    coq.elpi.accumulate _ "test.db"
      (clause _ _ (pi x\ foo x :- x = "here")),
    coq.env.begin-module "test_db_accumulate" none,
    coq.elpi.accumulate current "test.db"
      (clause _ _ (pi x\ foo x :- x = "there")),
    coq.env.end-module _.
}}.

Fail Elpi Query lp:{{foo _}}.
Elpi test.use.db.
Elpi Query lp:{{foo "here"}}.

Fail Elpi Query lp:{{foo "there"}}.
Import test_db_accumulate.
Elpi Query lp:{{foo "there"}}.





