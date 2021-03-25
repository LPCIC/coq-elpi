From elpi Require Import elpi.
From Coq Require Vector.

Elpi Command test.API.

Elpi Query lp:{{
  coq.version V MA MI P,
  std.assert! (MA = 8 ; MA = 9) "Coq major version not 8 or 9",
  std.assert! (MI >= 0 ; MI < 20) "Coq minor version not in 0 - 20",
  % std.assert! (P >= 0 ; P > -5) "Coq never made so many betas",
  coq.say "Coq version:" V "=" MA "." MI "." P.
}}.

(****** typecheck **********************************)

Elpi Query lp:{{
  coq.locate "plus" (const GR),
  coq.env.const GR (some BO) TY,
  coq.typecheck BO TY ok.
}}.

Elpi Query lp:{{
  pi x w z\
    decl x `x` {{ nat }} =>
    def z `z` {{ nat }} x =>
    (coq.say z,
     coq.typecheck z T ok,
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
     coq.typecheck z T ok,
     coq.say T,
     coq.say {coq.term->string z},
     coq.say {coq.term->string T}).
}}.

Elpi Query lp:{{

  coq.typecheck {{ Prop Prop }} _ (error E),
  coq.say E.

}}.


Elpi Query lp:{{
  coq.unify-leq {{ bool }}  {{ nat }} (error Msg),
  coq.say Msg.
}}.

(****** elaborate *******************************)
Module elab.
Axiom T1 : Type.
Axiom T2 : nat -> Type.
Axiom T3 : nat -> Type.

Axiom f1 : T1 -> Type.
Axiom f3 : forall b, T3 b -> Type.

Axiom g1 : T1 -> nat -> nat.
Axiom g3 : forall b, T3 b -> nat -> nat.

Axiom h : forall n , T2 n -> T3 n.

Coercion f1 : T1 >-> Sortclass.
Coercion f3 : T3 >-> Sortclass.
Coercion g1 : T1 >-> Funclass.
Coercion g3 : T3 >-> Funclass.
Coercion h : T2 >-> T3.

Elpi Query lp:{{

  std.assert-ok! (coq.elaborate-skeleton {{ fun n (t : T2 n) (x : t) => t 3 }} TY E) "that was easy",
  coq.env.add-const "elab_1" E TY tt _

}}.

Class foo (n : nat).
Definition bar n {f : foo n} := n = n.
Instance xxx : foo 3. Defined.

Elpi Query lp:{{

  std.assert-ok! (coq.elaborate-ty-skeleton {{ bar _ }} TY E) "that was easy",
  coq.env.add-const "elab_2" E (sort TY) tt _

}}.

Structure s := { field : Type; #[canonical=no] op : field -> field; }.
Canonical c := {| field := nat; op := (fun x => x) |}.

Elpi Query lp:{{

  std.assert-ok! (coq.elaborate-skeleton {{ op _ 3 }} TY E) "that was easy",
  coq.env.add-const "elab_3" E TY tt _

}}.

Elpi Accumulate lp:{{
  main [indt-decl D] :-
    std.assert-ok! (coq.elaborate-indt-decl-skeleton D D1) "illtyped",
    coq.env.add-indt D1 _.
  main [const-decl N (some BO) TYA] :- std.spy-do! [
    coq.arity->term TYA TY,
    std.assert-ok! (coq.elaborate-ty-skeleton TY _ TY1) "illtyped",
    std.assert-ok! (coq.elaborate-skeleton BO TY1 BO1) "illtyped",
    coq.env.add-const N BO1 TY1 @transparent! _,
  ].
}}.
Elpi Typecheck.

Elpi test.API Inductive ind1 (A : T1) :=
  K1 : ind1 A | K2 : A -> ind1 A.

Elpi test.API Record ind2 (A : T1) := {
   fld1 : A;
   fld2 : fld1 = fld1;
}.

Elpi test.API Record ind3 := {
  fld3 :> Type;
  fld4 : forall x : fld3, x = x;
}.

Check (forall x : ind3, x -> Prop).

Elpi test.API Definition def1 A := fun x : A => x.

Elpi Query lp:{{

  std.assert-ok! (coq.elaborate-skeleton {{ op lib:elpi.hole 3 }} TY E) "that was easy 2",
  coq.env.add-const "elab_4" E TY tt _

}}.

Elpi Tactic test.
Elpi Accumulate lp:{{
solve _ _ _ :-
  coq.term->string X S,
  X = global (indc Y),
  coq.say S.
}}.
Goal True.
Fail elpi test.
Abort.

Elpi Tactic test2.
Elpi Accumulate lp:{{
solve _ _ _ :-
  coq.term->string (global (indc Y)) S,
  coq.say S.
}}.
Goal True.
elpi test2.
Abort.

End elab.
(****** say *************************************)

Elpi Query lp:{{
  coq.say "hello world"
}}.

Elpi Query lp:{{
  coq.warn "this is a generic warning",
  coq.warning "category" "name"  "this is a warning with a name an category".
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

Notation succ x := (S x).

Elpi Query lp:{{ std.do! [
  coq.locate-all "plus"    X1, X1 = [loc-gref (const GR)],
  coq.locate-all "Nat.add" X2, X2 = [loc-gref (const GR)],
  coq.locate-all "succ"    X3, X3 = [loc-abbreviation A],
  coq.locate-all "Init.Datatypes" X4, X4 = [loc-modpath MP],
  coq.locate-all "fdsfdsjkfdksljflkdsjlkfdjkls" [],
].
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
  coq.env.typeof GR1 _,
  coq.env.typeof GR2 _,
  coq.env.typeof GR3 _.
}}.

End Test.

Elpi Query lp:{{
  coq.locate "plus" (const GR),
  coq.env.const GR (some BO) TY,
  coq.gref->id (const GR) S,
  Name is S ^ "_equal",
  coq.env.add-const Name BO TY @opaque! NGR,
  coq.env.const-opaque? NGR,
  coq.env.const NGR none _, coq.say {coq.gref->id (const NGR)},
  coq.env.const-body NGR (some BO),
  rex_match "add_equal" {coq.gref->id (const NGR)}.
}}.

About add_equal.

(* axiom *)

Elpi Query lp:{{
  coq.locate "False" F,
  coq.env.add-axiom "myfalse" (global F) GR,
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
    (parameter "T" _ {{Type}} t\
       record "eq_class" {{Type}} "mk_eq_class" (
            field [canonical ff, coercion tt]     "eq_f"     {{bool}} f\
            field _ "eq_proof" {{lp:f = lp:f :> bool}} _\
       end-record)),
 coq.say DECL,
 coq.env.add-indt DECL GR.
}}.

Print eq_class.
Check (fun x : eq_class nat => (x : bool)).
Axiom b : bool.
Axiom p : b = b.
Canonical xxx := mk_eq_class bool b p.
Print Canonical Projections.
Fail Check eq_refl _ : eq_f bool _ = b.

Elpi Query lp:{{
  DECL = 
    (parameter "T" _ {{Type}} t\
       record "prim_eq_class" {{Type}} "mk_prim_eq_class" (
            field [canonical ff, coercion tt]     "prim_eq_f"     {{bool}} f\
            field _ "prim_eq_proof" {{lp:f = lp:f :> bool}} _\
       end-record)),
 @primitive! => coq.env.add-indt DECL GR,
 coq.CS.canonical-projections GR [some _, some _].
}}.

(* primitive records have eta *)
Check fun r : prim_eq_class nat =>
  eq_refl _ : r = mk_prim_eq_class _ (prim_eq_f _ r) (prim_eq_proof _ r).

Module II.
Arguments prim_eq_f : default implicits.
Elpi Query lp:{{
  coq.say {{ fun r : prim_eq_class nat => r.(prim_eq_f) }}
}}.

Definition pc (r : prim_eq_class nat) := r.(prim_eq_f).

Elpi Query lp:{{
  coq.locate "pc" (const C),
  coq.env.const C (some (fun _ _ r\ app[global _, _, r])) _
}}.

Elpi Command primp.
Elpi Accumulate lp:{{
  main [const-decl _ (some (fun _ _ r\ app[global _, _, r])) _].
}}.
Elpi primp Definition pc (r : prim_eq_class nat) := r.(prim_eq_f).

End II.

(* inductive *)

Section Dummy.
Variable dummy : nat.

Elpi Command indtest.
Elpi Accumulate lp:{{
main _ :-
  DECL =
      (parameter "T" maximal {{Type}} t\
         parameter "x" _ t x\
           inductive "myind" _ (arity (prod `w` t _\ sort prop))
             i\ [ constructor "K1"
                   (arity (prod `y` t y\ prod _ (app[i,y]) _\app[i,x]))
                , constructor "K2"
                    (arity (app[i,x]))
                ]
            ),
 coq.env.add-indt DECL _,
 coq.rename-indt-decl rename rename rename DECL DECL1,
 coq.env.add-indt DECL1 _.

pred rename i:id, o:id.
rename K S :- S is K ^ "1".
}}.
Elpi Query indtest lp:{{ main _ }}.

Check myind true false : Prop.
Check K2 true : myind true true.
Check myind1 true false : Prop.
Check K21 true : myind1 true true.

End Dummy.

Elpi Query lp:{{
  coq.env.add-indt (parameter "X" _ {{Type}} x\
                      inductive "nuind" _ (parameter "n" _ {{ nat }} _\ arity {{ bool -> Type }}) i\
                       [constructor "k1" (parameter "n" _ {{nat}} n\ arity (app[i,n,{{true}}]))
                       ,constructor "k2" (parameter "n" _ {{nat}} n\
                                             arity (prod `x` (app[i,{{1}},{{false}}]) _\
                                              (app[i,n,{{false}}])))
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
  pi x\ decl x `x` {{ nat }} => coq.typecheck x T ok, coq.say x T.
}}.


Elpi Query lp:{{
  D = (parameter "A" _ {{ Type }} a\
     inductive "tx" _ (parameter "y" _ {{nat}} _\ arity {{ bool -> Type }}) t\
       [ constructor "K1x" (parameter "y" _ {{nat}} y\ arity {{
           forall (x : lp:a) (n : nat) (p : @eq nat (S n) lp:y) (e : lp:t n true),
           lp:t lp:y true }})
       , constructor "K2x" (parameter "y" _ {{nat}} y\ arity {{
           lp:t lp:y false }}) ]),
  coq.typecheck-indt-decl D ok,
  coq.env.add-indt D _.
}}.

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
    (indt Xi), (const _), (const _), (const _), (const _),
    (const _),
    (indt XYi), (const _), (const _), (const _), (const _),
    (const _)
  ],
  rex_match "^\\(Top\\|elpi.tests.test_API\\)\\.X\\.i$" {coq.gref->string (indt Xi)},
  rex_match "^\\(Top\\|elpi.tests.test_API\\)\\.X\\.Y\\.i$" {coq.gref->string (indt XYi)},
  (coq.gref->path (indt XYi) ["elpi", "tests", "test_API", "X", "Y", "i" ] ;
   coq.gref->path (indt XYi) ["Top",           "test_API", "X", "Y", "i" ])
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
  coq.env.begin-section "Foo",
  coq.env.add-section-variable "x" {{ nat }} X,
  coq.env.section [X],
  coq.env.add-const "fx" (global (const X)) _ _ _,
  coq.env.end-section.
}}.

Check fx : nat -> nat.


(****** typecheck **********************************)

Require Import List.

Elpi Query lp:{{
  coq.locate "cons" GRCons, Cons = global GRCons,
  coq.locate "nil" GRNil, Nil = global GRNil,
  coq.locate "nat" GRNat, Nat = global GRNat,
  coq.locate "O" GRZero, Zero = global GRZero,
  coq.locate "list" GRList, List = global GRList,
  L  = app [ Cons, _, Zero, app [ Nil, _ ]],
  LE = app [ Cons, Nat, Zero, app [ Nil, Nat ]],
  coq.typecheck L (app [ List, Nat ]) ok.
}}.

Definition nat1 := nat.

Elpi Query lp:{{ coq.typecheck {{ 1 }} {{ nat1 }} ok }}.

Definition list1 := list.

Elpi Query lp:{{ coq.typecheck {{ 1 :: nil }} {{ list1 lp:T }} ok, coq.say T }}.

Elpi Query lp:{{ coq.typecheck-ty {{ nat }} (typ U) ok, coq.say U }}.

Elpi Query lp:{{ coq.typecheck-ty {{ nat }} prop (error E), coq.say E }}.


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

Elpi Query lp:{{coq.locate "myi" GR, coq.TC.declare-instance GR 10. }}.

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

Axiom W1 : Type.
Axiom Z1 : W1 -> W1 -> bool.
Axiom t1 : W1.

Definition myc1 : eq := mk_eq W1 Z1 3.

Section CStest.
Elpi Query lp:{{ coq.locate "myc1" GR, @local! => coq.CS.declare-instance GR. }}.

Check (eq_op _ t1 t1).

Elpi Query lp:{{ coq.locate "eq_op" P, coq.CS.db-for P _ [_,_] }}.

Elpi Query lp:{{ coq.locate "W" W, coq.CS.db-for _ (cs-gref W) [_] }}.

Elpi Query lp:{{ coq.locate "eq_op" P, coq.locate "Z1" W, coq.CS.db-for P (cs-gref W) L, coq.say L, L = [cs-instance P (cs-gref W) {{myc1}}] }}.

Elpi Query lp:{{ coq.locate "eq_op" P, coq.locate "nat" W, coq.CS.db-for P (cs-gref W) [] }}.


End CStest.

Fail Check (eq_op _ t1 t1).


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
  % coq.locate "C2"    C2,
  @global! => coq.coercion.declare (coercion GR1 _ _ _),
  @global! => coq.coercion.declare (coercion GR2 _ C1 sortclass),
  @global! => coq.coercion.declare (coercion GR3 _ C1 funclass).
}}.

Check (fun x : C1 => (x : C2)).
Check (fun x : C1 => fun y : x => true).
Check (fun x : C1 => x 3).

Elpi Query lp:{{coq.coercion.db L}}.

(***** Syndef *******************************)

Elpi Query lp:{{
    coq.notation.add-abbreviation "abbr" 2
      {{ fun x _ => x = x }} tt A,
    coq.say A
}}.

About abbr.
Check abbr 4 3.

Elpi Query lp:{{
  coq.notation.add-abbreviation "abbr2" 1
    {{ fun x _ => x = x }} tt _
}}.

About abbr2.
Check abbr2 2 3.

Elpi Query lp:{{
  coq.notation.abbreviation {coq.locate-abbreviation "abbr2"} [{{ fun x => x }}] T,
  coq.say T.
}}.

Elpi Query lp:{{
  coq.notation.abbreviation-body {coq.locate-abbreviation "abbr2"} 1
    (fun _ _ x\ fun _ _ _\ app[_,_,x,x]).
}}.

(***** Impargs *******************************)

Module X2.

Axiom imp : forall T (x:T), x = x -> Prop.
Arguments imp {_} [_] _ , [_] _ _ .

Elpi Query lp:{{
    coq.locate "imp" I,
    coq.arguments.implicit I
      [[maximal,implicit,explicit], [implicit,explicit,explicit]],
    @global! => coq.arguments.set-implicit I
      [[]],
    coq.arguments.implicit I
      [[explicit,explicit,explicit]]
}}.
End X2.
About X2.imp.

Module X3.
Definition foo (T : Type) (x : T) := x.
Arguments foo : clear implicits.

Fail Check foo 3.

Elpi Query lp:{{
  @global! => coq.arguments.set-default-implicit {coq.locate "foo"}
}}.

Check foo 3.

End X3.


(***** Argnames/scopes/simpl *******************************)

Definition f T (x : T) := x = x.

Elpi Query lp:{{
  coq.arguments.set-name     {coq.locate "f"} [some "S"],
  coq.arguments.name         {coq.locate "f"} [some "S"],
  coq.arguments.set-implicit {coq.locate "f"} [[implicit]],
  coq.arguments.set-scope    {coq.locate "f"} [some "type"],
  coq.arguments.scope        {coq.locate "f"} [some "type_scope"]
}}.
About f.
Check f (S:= bool * bool).

Elpi Query lp:{{
  coq.arguments.set-simplification {coq.locate "f"} (when [] (some 1))
}}.
About f.
Check f (S:= bool * bool).
Eval simpl in f (S := bool).


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


Elpi Command export.me.
Elpi Accumulate lp:{{ main _ :- coq.say "hello". }}.
Elpi Typecheck.

Elpi Export export.me.

export.me 1 2 (nat) "x".

Elpi Command halt.
Elpi Accumulate lp:{{
  main _ :- std.assert! (3 = 2) "ooops".
}}.
Fail Elpi halt.

(**********************************************)

Elpi Command test.pp.
Elpi Accumulate lp:{{
main _ :- std.do! [
  P = coq.pp.box (coq.pp.hv 2) [coq.pp.str "Module", coq.pp.spc, coq.pp.str "Foo", coq.pp.spc, coq.pp.str":=", coq.pp.brk 1 0, coq.pp.str "body", coq.pp.spc, coq.pp.str "End Foo."],
  coq.say P,
  @ppwidth! 15 => coq.say {coq.pp->string P},
  @ppall! => coq.say {coq.term->string {{ fix foo x y {struct x} := match x in bool with false => y | true => 3 end }} },
  @ppmost! => coq.say {coq.term->string {{ fix foo x y {struct x} := match x in bool with false => y | true => 3 end }} },
].
}}.
Elpi Typecheck.
Elpi test.pp.

(************* using ********************)
Section Using.
Variable A : bool.
Elpi Query lp:{{ coq.env.add-const "foo" {{ 3 }} {{ nat }} @transparent! _ }}.
Elpi Query lp:{{ @using! "All" => coq.env.add-const "bar" {{ 3 }} {{ nat }} @transparent! _ }}.
End Using.
Check foo : nat.
Check bar : bool -> nat.
