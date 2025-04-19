From elpi Require Import elpi.
From elpi_stdlib Require Vector.

(****** env **********************************)
Elpi Command test.

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
  coq.env.opaque? NGR,
  coq.env.const NGR none _, coq.say {coq.gref->id (const NGR)},
  coq.env.const-body NGR (some BO),
  rex_match "add_equal" {coq.gref->id (const NGR)}.
}}.

About add_equal.

(* axiom *)

Elpi Query lp:{{
  coq.locate "False" F,
  coq.env.add-axiom "myfalse" (global F) GR,
  coq.env.opaque? GR,
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
            field [canonical ff, coercion regular]     "eq_f"     {{bool}} f\
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
            field [canonical ff, coercion reversible]     "prim_eq_f"     {{bool}} f\
            field _ "prim_eq_proof" {{lp:f = lp:f :> bool}} _\
       end-record)),
 (@primitive! => coq.env.add-indt DECL GR),
 coq.env.projections GR [some _, some _].
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
  coq.env.const C (some (fun _ _ r\ app[primitive _, r])) _
}}.

Elpi Command primp.
Elpi Accumulate lp:{{
  main [const-decl _ (some (fun _ _ r\ app[primitive _, r])) _].
}}.
Elpi primp Definition pc (r : prim_eq_class nat) := r.(prim_eq_f).

End II.

(* inductive *)

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
  pi x\ (decl x `x` {{ nat }} => coq.typecheck x T ok), coq.say x T.
}}.


Elpi Query lp:{{
  D = (parameter "A" _ {{ Type }} a\
     inductive "tx" _ (parameter "y" _ {{nat}} _\ arity {{ bool -> Type }}) t\
       [ constructor "K1x" (parameter "y" _ {{nat}} y\ arity {{
           forall (x : lp:a) (n : nat) (p : @eq nat (S n) lp:y) (e : lp:t n true),
           lp:t lp:y true }})
       , constructor "K2x" (parameter "y" _ {{nat}} y\ arity {{
           lp:t lp:y false }}) ]),
  std.assert-ok! (coq.typecheck-indt-decl D) "illtyped",
  coq.env.add-indt D _.
}}.

Module HOAS.

Inductive ind1 (A : Type) (a : A) | (B : Type) (b : B) : forall C : Type, C -> Type :=
  | k1 : forall bb, ind1 (B * B)%type bb bool true -> ind1 B b unit tt
  | k2 : ind1 B b nat 1.

Elpi Query lp:{{

  coq.locate "ind1" (indt I),
  coq.env.indt-decl I D,
  D1 =
    (parameter "A" explicit (sort (typ UA)) c0 \
     parameter "a" explicit c0 c1 \
       inductive "ind1" tt 
          (parameter "B" explicit (sort (typ UB1)) c2 \
           parameter "b" explicit c2 c3 \
           arity
             (prod `C` (sort (typ UC)) c4 \ prod `_` c4 c5 \ sort (typ U)))
       c2 \
   [constructor "k1"
     (parameter "B" explicit (sort (typ UB2)) c3 \
       parameter "b" explicit c3 c4 \
        arity
         (prod `bb` {{ (lp:c3 * lp:c3)%type }} c5 \
           prod `_` (app [c2, {{ (lp:c3 * lp:c3)%type }}, c5, {{ bool }}, {{ true }}]) c6 \
            app [c2, c3, c4, {{ unit }},  {{ tt }}])), 
    constructor "k2"
     (parameter "B" explicit (sort (typ UB3)) c3 \
       parameter "b" explicit c3 c4 \
        arity
         (app [c2, c3, c4, {{ nat }}, {{ 1 }}]))]),
  std.assert! (D = D1) "coq.env.indt-decl".

}}.

Arguments k1 A a B b [bb] _.

Elpi Query lp:{{

  coq.locate "ind1" (indt I),
  coq.env.indt-decl I D,
  D1 =
    (parameter "A" explicit (sort (typ UA)) c0 \
     parameter "a" explicit c0 c1 \
       inductive "ind1" tt 
          (parameter "B" explicit (sort (typ UB1)) c2 \
           parameter "b" explicit c2 c3 \
           arity
             (prod `C` (sort (typ UC)) c4 \ prod `_` c4 c5 \ sort (typ U)))
       c2 \
   [constructor "k1"
     (parameter "B" explicit (sort (typ UB2)) c3 \
       parameter "b" explicit c3 c4 \
       parameter "bb" implicit {{ (lp:c3 * lp:c3)%type }} c5 \
        arity
          (prod `_` (app [c2, {{ (lp:c3 * lp:c3)%type }}, c5, {{ bool }}, {{ true }}]) c6 \
            app [c2, c3, c4, {{ unit }},  {{ tt }}])), 
    constructor "k2"
     (parameter "B" explicit (sort (typ UB3)) c3 \
       parameter "b" explicit c3 c4 \
        arity
         (app [c2, c3, c4, {{ nat }}, {{ 1 }}]))]),
   std.assert! (D = D1) "coq.env.indt-decl + implicits".
}}.

Record r1 (P : Type) (p : P) : Type := mk_r1 {
  f1 :> P -> P;
  #[canonical=no] f2 : p = f1 p;
}.

Elpi Query lp:{{

  coq.locate "r1" (indt I),
  coq.env.indt-decl I D,
  D1 =
    (parameter "P" explicit (sort (typ UP)) c0 \
     parameter "p" explicit c0 c1 \
       record "r1" (sort (typ UR)) "mk_r1" 
         (field [coercion reversible, canonical tt] "f1" {{ lp:c0 -> lp:c0 }} c2\
          field [coercion off, canonical ff] "f2" {{ @eq lp:c0 lp:c1 (lp:c2 lp:c1) }} c3\
          end-record)
    ),
  std.assert! (D = D1) "coq.env.indt-decl + record".

}}.

#[warning="-uniform-inheritance"] Coercion f2 : r1 >-> eq.

Elpi Query lp:{{

  coq.locate "r1" (indt I),
  coq.env.indt-decl I D,
  D1 =
    (parameter "P" explicit (sort (typ UP)) c0 \
     parameter "p" explicit c0 c1 \
       record "r1" (sort (typ UR)) "mk_r1" 
         (field [coercion reversible, canonical tt] "f1" {{ lp:c0 -> lp:c0 }} c2\
          field [coercion regular, canonical ff] "f2" {{ @eq lp:c0 lp:c1 (lp:c2 lp:c1) }} c3\
          end-record)
    ),
  std.assert! (D = D1) "coq.env.indt-decl + record".

}}.

Elpi Query lp:{{

  coq.locate "plus" GR,
  coq.env.dependencies GR _ L,
  coq.say L,
  coq.env.transitive-dependencies GR _ S,
  coq.say S,
  std.assert! (S = L) "plus wrong deps"

}}.

Module X.
  Definition a := 0.
  Definition b := a + a.
End X.

Elpi Query lp:{{

  coq.locate "X.b" GR,
  coq.locate-module "X" M,
  coq.env.dependencies GR M L,
  coq.env.dependencies GR _ AllL,
  coq.say L AllL,
  std.assert! (coq.gref.set.subset L AllL) "??",
  std.assert! (coq.gref.set.elements L [{coq.locate "X.a"}]) "??",
  coq.env.transitive-dependencies GR M S,
  coq.env.transitive-dependencies GR _ AllS,
  coq.say S AllS,
  std.assert! (coq.gref.set.subset S AllS) "??"
  
}}.

End HOAS.

From elpi_stdlib Require Ranalysis5.

Elpi Query lp:{{

  coq.locate "Ranalysis5.derivable_pt_lim_CVU" GR,
  std.time (coq.env.transitive-dependencies GR _ S) T,
  std.assert! ({coq.gref.set.cardinal S} > 3000) "too few",
  std.assert! (T < 10.0) "too slow" % 0.5 here

}}.

Elpi Query lp:{{

  T = {{ forall x : nat, x + 0 = x }},
  coq.env.term-dependencies T S,
  std.assert! ({coq.gref.set.cardinal S} = 4) "wrong",
  not (coq.gref.set.mem {{:gref S }}       S),
      (coq.gref.set.mem {{:gref O }}       S),
      (coq.gref.set.mem {{:gref nat }}     S),
      (coq.gref.set.mem {{:gref Nat.add }} S),
      (coq.gref.set.mem {{:gref eq }}      S)

}}.

Set Universe Polymorphism.

Elpi Query lp:{{
  coq.env.begin-module "Test" none,
  coq.env.end-module _.
}} lp:{{
  coq.env.begin-module "Test" _,
  Decl = record "Rec" {{ Type }} "BuildRec" (field [] "f" {{ Type }} (_\ end-record)),
  (@univpoly! => coq.env.add-indt Decl _),
  coq.env.end-module _.
}}.

Set Printing Universes. Print Module Test.
Check Test.f.

From elpi_stdlib Require Import ZArith.

Elpi Query lp:{{
  coq.locate-module "N2Z" MP,
  coq.locate-module "Znat" LP,
  coq.modpath->library MP LP
}}.
