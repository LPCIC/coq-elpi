From elpi Require Import elpi.

Elpi Tactic test1.
Elpi Accumulate lp:{{

solve G GS :- pi x\
  coq.sigma.print,
  print_constraints,
  refine {{ fun w : _ => _ }} G GS.
}}.


Lemma test (x : nat) : bool -> True.
Proof.

elpi test1.

Abort.

Ltac foobar x := idtac x; eapply x.

(* TODO: test evar type with a binder *)

Elpi Tactic test2.
Elpi Accumulate lp:{{

solve (goal [decl T _ _ | _ ] _ _ _ _ as G) GS :-
  coq.ltac.call "foobar" [trm T] G GS,
  coq.say GS.

}}.


Lemma test  : (forall b: ( forall b : bool, b = b), True) -> True.
Proof.
intro.
elpi test2.
intro; reflexivity.
Qed.



Module kwd.

Parameter x : bool.

Elpi Command kwd.
Elpi Accumulate lp:{{
  main L :- coq.say L.
}}.


Elpi kwd fun in as 4 end match return => : := { } ; , | "x" 1 H (fun x => match x as y in False return nat with end).

End kwd.

Elpi Command test.

Elpi Query lp:{{
  std.do! [coq.env.begin-section "xxxxx", coq.env.end-section]
}} lp:{{
  coq.env.begin-section "xxxxx",
  coq.univ.new U,
  T = sort (typ U),
  coq.env.add-section-variable "a" _ T _,
  coq.env.end-section
}}.

Elpi Db univs.db lp:{{ pred u o:univ. }}.
Elpi Command test_u.
Elpi Accumulate Db univs.db.
Elpi Query lp:{{
  coq.univ.new U,
  coq.elpi.accumulate current "univs.db" (clause _ _ (u U))
}}.

Universe foo.

Elpi Query lp:{{
  {{ Type@{foo} }} = sort (typ U),
  coq.elpi.accumulate current "univs.db" (clause _ _ (u U))
}}.


Axiom B : bool -> Type.
Axiom N : nat -> Type.

(* restriction *)
Elpi Query lp:{{
  pi w\
  @pi-decl `a` {{ bool }} a\
  pi e\
  @pi-decl `b` {{ B lp:a }} b\
  coq.typecheck {{ fun x (y z : N x) => lp:{{ X a {{x}} {{z}} }} }} _ ok.
}}.


(* option *)
Fail Elpi Query lp:{{
  @pi-decl `a` {{ bool }} a\
    coq.typecheck (X a a) _ ok
}}.
Elpi Query lp:{{
  @pi-decl `a` {{ bool }} a\
  coq.say "----------------------------------",
  (@holes! => coq.typecheck (X a a) TY ok),
  coq.sigma.print,
  coq.say (X a a) ":" TY.
}}.

(* primitive *)

Module Pint.

Elpi Command primitive.
Elpi Accumulate lp:{{
main [trm T] :-
  std.assert! (coq.reduction.native.norm T _ T1) "normal form is not an opinion",
  std.assert! (coq.reduction.vm.norm T _ T1) "normal form is not an opinion",
  std.assert! (coq.reduction.cbv.norm T T1) "normal form is not an opinion",
  std.assert! (coq.reduction.lazy.norm T T1) "normal form is not an opinion",
  std.assert! (coq.reduction.lazy.whd_all T T1) "normal form is not an opinion",
  coq.say "Raw term:" T "\nNice term:" {coq.term->string T} "\nRed:" {coq.term->string T1}.
}}.


From elpi.core Require Import PrimInt63.
Elpi primitive (PrimInt63.add 2000000003333002 1).

From elpi.core Require Import PrimFloat.
Open Scope float_scope.
Elpi primitive (2.4e13 + 1).
End Pint.

(* redflags *)

Elpi Query lp:{{
  T1 = {{ 1 + 2 }},
  T2 = {{ (fix plus n m {struct n} := match n with O => m | S p => S (plus p m) end) 1 2 }},
  coq.locate "plus" (const C),
  coq.redflags.add coq.redflags.nored [
    coq.redflags.const C,
  ] F,
  (@redflags! F => coq.reduction.cbv.norm T1 T),
  std.assert! (T = T2) "normal form is not an opinion".
}}.

Elpi Query lp:{{
  T1 = {{ 1 + 2 }},
  T2 = {{ (fun n m => match n with O => m | S p => S ((fix plus n m {struct n} := match n with O => m | S p => S (plus p m) end) p m) end) 1 2 }},
  coq.locate "plus" (const C),
  coq.redflags.add coq.redflags.nored [
    coq.redflags.const C,
    coq.redflags.fix,
  ] F,
  (@redflags! F => coq.reduction.cbv.norm T1 T),
  std.assert! (T = T2) "normal form is not an opinion".
}}.

Elpi Query lp:{{
  T1 = {{ 1 + 2 }},
  T2 = {{ match 1 with O => 2 | S p => S ((fix plus n m {struct n} := match n with O => m | S p => S (plus p m) end) p 2) end }},
  coq.locate "plus" (const C),
  coq.redflags.add coq.redflags.nored [
    coq.redflags.const C,
    coq.redflags.fix,
    coq.redflags.beta,
  ] F,
  (@redflags! F => coq.reduction.cbv.norm T1 T),
  std.assert! (T = T2) "normal form is not an opinion".
}}.

Elpi Query lp:{{
  T1 = {{ 1 + 2 }},
  T2 = {{ 3 }},
  coq.locate "plus" (const C),
  coq.redflags.add coq.redflags.nored [
    coq.redflags.const C,
    coq.redflags.fix,
    coq.redflags.beta,
    coq.redflags.match,
  ] F,
  (@redflags! F => coq.reduction.cbv.norm T1 T),
  std.assert! (T = T2) "normal form is not an opinion".
}}.

(* ------------------------------------ *)

Module P.
Set Primitive Projections.

Unset Auto Template Polymorphism.
Record foo {A : Type} := { p1 : nat; p2 : A }.
Definition x : foo := {| p1 := 3; p2 := false |}.

Unset Primitive Projections.
End P.


Module P'.
  Record s (T : Type) := {
    proj1 : nat;
    proj2 : nat
  }.

  Elpi Query  lp:{{
    global (const C) = {{proj1}},
    coq.env.projection? C 1.
  }}.
End P'.


Module P''.
  #[local] Set Primitive Projections.
  Record s1 (T : Type) := {
    proj1 : nat;
    proj2 : nat
  }.

  Axiom (X : s1 nat).

  Elpi Query  lp:{{
    app[primitive (proj P _) | _] = {{X.(proj1 _)}},
    coq.env.primitive-projection? P C _,
    global (const C) = {{proj1}}.
  }}.

End P''.


Elpi Command primitive_proj.
Elpi Accumulate lp:{{
  main [str Kind, trm (global (indt I)), trm T, int N, trm V] :- std.do! [
    coq.env.projections I [_,_],
    coq.env.primitive-projections I [some (pr _ 1), some (pr _ 2)],
    coq.env.projections I [some P1, some P2],
    if (Kind = "primitive")
       (std.assert! (T = app[primitive (proj P N),A]) "not prim proj", coq.say P N A, coq.say {coq.term->string (primitive (proj P N))})
       (std.assert! (T = app[global(const X), _, A], (X = P1 ; X = P2)) "not regular proj"), coq.say X A,
    coq.say {coq.term->string T},
    std.assert! ( {{:gref P.p1 }} = const C) "wrong gref",
    std.assert! ( {{ @P.p1 }} = global (const C)) "wrong global",
    coq.env.const C BO _,
    coq.say BO,
    std.assert! (unwind {whd T []} V) "wrong value",
  ].
}}.


Elpi primitive_proj "primitive" (@P.foo) (P.x.(P.p1)) 1 (3%nat).
Elpi primitive_proj "primitive" (@P.foo) (P.x.(P.p2)) 2 (false).
(* FIXME, in raw mode this works
Elpi primitive_proj "regular"   (@P.foo) (@P.p1 _ P.x) 1 (3%nat).
Elpi primitive_proj "regular"   (@P.foo) (P.p2 P.x) 2 (false).
Elpi primitive_proj "regular"   (@P.foo) (P.x.(@P.p1 bool)) 1 (3%nat).
Elpi primitive_proj "regular"   (@P.foo) (P.x.(@P.p2 _)) 2 (false).
*)

(* glob of ifte *)

Elpi Command ifte.
Elpi Accumulate lp:{{

main [trm X] :-
  coq.elaborate-skeleton X _ _ ok.

}}.

Elpi ifte (if true then 1 else 2).

(* gref quotations *)

Register nat as elpi.test.nat.

Elpi Query lp:{{

  coq.locate "lib:elpi.test.nat" {{:gref nat }},
  coq.locate "nat" {{:gref lib:elpi.test.nat }}.

}}.

Polymorphic Definition toto (T1 T2 : Type) (x : T1) := x.
Polymorphic Definition titi := toto.

Elpi Query lp:{{
  coq.locate "titi" (const C),
  coq.env.const C Body Term,
  coq.say Body,
  coq.say Term.
}}.

Universes u1 u2.

Elpi Query lp:{{
  coq.say {{ toto }},         % pglobal (const «toto») X
  coq.say {{ toto@{u1 u2} }}, % pglobal (const «toto») «u1 u2»
  coq.say {coq.term->string {{ toto }}}.
}}.

Polymorphic Record F (T : Type) := Build_F { t : T }.
Polymorphic Definition fnat : F nat := {| t := 0%nat |}.

Elpi Query lp:{{
  T = {{ @t nat fnat }},
  coq.say T,
  coq.typecheck T Ty ok,
  coq.say T.
}}.

Section UPolyVar.

Polymorphic Variable n : nat.

Elpi Query lp:{{
  coq.locate "F" GRF,
  coq.typecheck (pglobal GRF I) TyF ok,
  GRF = indt Ind,

  % coq.env.indt
  (@uinstance! I => coq.env.indt Ind _ _ _ Arity K KTys).
  (@uinstance! I => coq.env.indt Ind _ _ _ Arity K _).
  (@uinstance! I => coq.env.indt Ind _ _ _ _ K KTys).
  (@uinstance! I => coq.env.indt Ind _ _ _ _ K _).
  (@uinstance! I => coq.env.indt Ind _ _ _ _ _ _).

  (@uinstance! _ => coq.env.indt Ind _ _ _ Arity1 K KTys1).
  (@uinstance! _ => coq.env.indt Ind _ _ _ Arity2 K _).
  (@uinstance! _ => coq.env.indt Ind _ _ _ _ K KTys3).
  (@uinstance! _ => coq.env.indt Ind _ _ _ _ K _).
  (@uinstance! _ => coq.env.indt Ind _ _ _ _ _ _).

  (@uinstance! A4 => coq.env.indt Ind _ _ _ Arity4 K KTys4).
  (@uinstance! A5 => coq.env.indt Ind _ _ _ Arity5 K _).
  (@uinstance! A6 => coq.env.indt Ind _ _ _ _ K KTys6).
  (@uinstance! A7 => coq.env.indt Ind _ _ _ _ K _).
  (@uinstance! A8 => coq.env.indt Ind _ _ _ _ _ _).

  (@uinstance! A4 => coq.env.indt Ind _ _ _ Arity4 K KTys4).
  (@uinstance! A5 => coq.env.indt Ind _ _ _ Arity5 K _).
  (@uinstance! A6 => coq.env.indt Ind _ _ _ _ K KTys6).

  coq.locate "Build_F" GRB,
  coq.typecheck (pglobal GRB I2) TyB ok,
  GRB = indc B,

  % coq.env.indc
  (@uinstance! I2 => coq.env.indc B _ _ _ TyB).
  (@uinstance! I2 => coq.env.indc B _ _ _ _).

  (@uinstance! _ => coq.env.indc B _ _ _ BTy2).
  (@uinstance! _ => coq.env.indc B _ _ _ _).

  (@uinstance! B1 => coq.env.indc B _ _ _ BTy3).
  (@uinstance! B2 => coq.env.indc B _ _ _ _).

  (@uinstance! B1 => coq.env.indc B _ _ _ BTy3).

  coq.locate "t" GRt,
  coq.typecheck (pglobal GRt I3) Tyt ok,
  GRt = const T,

  % coq.env.const
  % constant
  (@uinstance! I3 => coq.env.const T BoT TyT).
  (@uinstance! I3 => coq.env.const T BoT _).
  (@uinstance! I3 => coq.env.const T _ TyT).
  (@uinstance! I3 => coq.env.const T _ _).

  (@uinstance! _ => coq.env.const T BoT1 TyT1).
  (@uinstance! _ => coq.env.const T BoT2 _).
  (@uinstance! _ => coq.env.const T _ TyT3).
  (@uinstance! _ => coq.env.const T _ _).

  (@uinstance! D1 => coq.env.const T BoT4 TyT4).
  (@uinstance! D2 => coq.env.const T BoT5 _).
  (@uinstance! D3 => coq.env.const T _ TyT5).
  (@uinstance! D4 => coq.env.const T _ _).

  (@uinstance! D1 => coq.env.const T BoT4 TyT4).
  (@uinstance! D2 => coq.env.const T BoT5 _).
  (@uinstance! D3 => coq.env.const T _ TyT5).

  coq.locate "n" GRn,
  GRn = const N,

  % variable (non polymorphic)
  (@uinstance! _ => coq.env.const N BoN TyN).
  (@uinstance! _ => coq.env.const N BoN _).
  (@uinstance! _ => coq.env.const N _ TyN).
  (@uinstance! _ => coq.env.const N _ _).

  (@uinstance! I4 => coq.env.const N BoN TyN).
  (@uinstance! I4 => coq.env.const N BoN _).
  (@uinstance! I4 => coq.env.const N _ TyN).
  (@uinstance! I4 => coq.env.const N _ _).

  % coq.env.typeof
  % indt
  (@uinstance! I => coq.env.typeof GRF TyF).
  (@uinstance! I => coq.env.typeof GRF _).

  (@uinstance! _ => coq.env.typeof GRF TyF2).
  (@uinstance! _ => coq.env.typeof GRF _).

  (@uinstance! C1 => coq.env.typeof GRF TyF3).
  (@uinstance! C2 => coq.env.typeof GRF _).

  (@uinstance! C1 => coq.env.typeof GRF TyF3).

  % indc
  (@uinstance! I2 => coq.env.typeof GRB TyB).
  (@uinstance! I2 => coq.env.typeof GRB _).

  (@uinstance! _ => coq.env.typeof GRB TyB2).
  (@uinstance! _ => coq.env.typeof GRB _).

  (@uinstance! C3 => coq.env.typeof GRB TyB3).
  (@uinstance! C4 => coq.env.typeof GRB _).

  (@uinstance! C3 => coq.env.typeof GRB TyB3).

  % const
  (@uinstance! I3 => coq.env.typeof GRt TyT).
  (@uinstance! I3 => coq.env.typeof GRt _).

  (@uinstance! _ => coq.env.typeof GRt TyT6).
  (@uinstance! _ => coq.env.typeof GRt _).

  (@uinstance! C5 => coq.env.typeof GRt TyT7).
  (@uinstance! C6 => coq.env.typeof GRt _).

  (@uinstance! C5 => coq.env.typeof GRt TyT7).

  % var
  (@uinstance! I4 => coq.env.typeof GRn TyN).
  (@uinstance! I4 => coq.env.typeof GRn _).

  (@uinstance! _ => coq.env.typeof GRn TyN).
  (@uinstance! _ => coq.env.typeof GRn _).

  % coq.env.const-body
  % const
  (@uinstance! I3 => coq.env.const-body T BoT).
  (@uinstance! I3 => coq.env.const-body T _).

  (@uinstance! _ => coq.env.const-body T BoT6).
  (@uinstance! _ => coq.env.const-body T _).

  (@uinstance! E5 => coq.env.const-body T BoT7).
  (@uinstance! E6 => coq.env.const-body T _).

  (@uinstance! E5 => coq.env.const-body T BoT7).

  % var
  (@uinstance! I4 => coq.env.const-body N BoN).
  (@uinstance! I4 => coq.env.const-body N _).
  
  (@uinstance! _ => coq.env.const-body N BoN).
  @uinstance! _ => coq.env.const-body N _.
}}.

Elpi Query lp:{{
  coq.locate "F" GRF,
  GRF = indt Ind,

  % coq.env.indt
  (@uinstance! I => coq.env.indt-decl Ind Decl).
  coq.say I Decl,
  (@uinstance! I => coq.env.indt-decl Ind Decl1).
  coq.say I Decl1,

  (@uinstance! _ => coq.env.indt-decl Ind Decl2).
  coq.say Decl2.

}}.

End UPolyVar.

Elpi Query lp:{{
  coq.locate "F" GRF,
  coq.typecheck (pglobal GRF I1) _ ok,
  coq.typecheck (pglobal GRF I2) _ ok,
  coq.say I1 I2,
  coq.univ.print,
  coq.univ-instance.unify-eq GRF I1 I2 ok,
  coq.univ.print.
}}.

Elpi Query lp:{{
  coq.locate "F" GRF,
  coq.locate "fnat" GRfnat,
  coq.typecheck (pglobal GRF I1) _ ok,
  coq.typecheck (pglobal GRfnat I2) _ ok,
  coq.say I1 I2,
  coq.univ.print,
  coq.univ-instance.unify-eq GRF I1 I2 (error E),
  coq.say E,
  coq.univ.print.
}}.

Elpi Query lp:{{
  coq.locate "F" GRF,
  coq.typecheck (pglobal GRF I1) _ ok,
  coq.univ-instance I1 UL1,
  coq.univ-instance I1 [U],
  coq.univ-instance I2 [U].
}}.

Elpi Query lp:{{
  coq.locate "F" GRF,
  coq.typecheck (pglobal GRF I1) _ ok,
  coq.typecheck (pglobal GRF I2) _ ok,
  coq.univ-instance I1 [L1],
  coq.univ-instance I2 [L2],
  coq.univ.variable U1 L1,
  coq.univ.variable U2 L2,
  coq.sort.sup (typ U1) (typ U2),
  coq.univ-instance.unify-eq GRF I1 I2 (error E),
  coq.say E.
}}.

Cumulative Polymorphic Record F2@{+x} (T : Type@{x}) := Build_F2 { t2 : T }.

Elpi Query lp:{{
  coq.locate "F2" GRF,
  coq.typecheck (pglobal GRF I1) _ ok,
  coq.typecheck (pglobal GRF I2) _ ok,
  coq.univ-instance I1 [L1],
  coq.univ-instance I2 [L2],
  coq.univ.variable U1 L1,
  coq.univ.variable U2 L2,
  coq.sort.sup (typ U1) (typ U2),
  coq.univ.print,
  coq.univ-instance.unify-leq GRF I1 I2 ok. % why does this add a = not a <= ?
}}.

Elpi Query lp:{{
  coq.locate "F" GRF,
  coq.env.global GRF (pglobal GRF I1),
  coq.typecheck (pglobal GRF I2) _ ok,
  coq.univ-instance I1 [L1],
  coq.univ-instance I2 [L2],
  coq.univ.variable U1 L1,
  coq.univ.variable U2 L2,
  coq.sort.sup (typ U1) (typ U2),
  coq.univ.print,
  coq.univ-instance.unify-leq GRF I2 I1 (error E),
  coq.say E.
}}.

Elpi Query lp:{{
  coq.locate "nat" GR,
  coq.env.global GR (global GR)
}}.

Elpi Query lp:{{
  coq.locate "F" GR,
  coq.env.global GR (pglobal GR I)
}}.


Elpi Query lp:{{
  coq.locate "F" GR,
  not(coq.env.global GR (global GR))
}}.

Elpi Query lp:{{
  coq.locate "F" GR,
  (@uinstance! I => coq.say {coq.env.global GR}).
  coq.locate "Build_F" GR1,
  coq.say I,
  @uinstance! I => coq.say {coq.env.global GR1}.

}}.

Elpi Query lp:{{
  coq.univ-instance I [U,U],
  coq.say I
}}.


(*

#[universes(polymorphic)]
Definition poly@{x y | x < y } : Type@{y} := Type@{x}.
Set Printing Universes.
About poly.

#[universes(polymorphic)]
Inductive Box@{x y z} : Type@{z} := K : (Type@{x} -> Type@{y}) -> (Type@{y} -> Type@{x}) -> Box.
Set Printing Universes.
About Box.
*)

Elpi Query lp:{{
  
  Body = (sort (typ UX)),
  Type = (sort (typ UY)),
  coq.univ.print,
  coq.say "------------------",
  coq.typecheck Body Type ok,
  coq.univ.print,

  coq.univ.variable UX LX,
  coq.univ.variable UY LY,
  coq.univ.print,

  @udecl! [LX,LY] ff [lt LX LY] ff =>
    coq.env.add-const "poly" Body Type _ _.

/*
  @udecl-cumul! [invariant UX,auto UY,covar UZ| _] _ =>
    coq.env.add-indt (inductive "Box" tt (arity (sort (typ UZ))) i\[
      constructor "K" (arity
        prod `_` (prod `_` (sort (typ UX)) (_\sort (typ UY))) _\
        prod `_` (prod `_` (sort (typ UY)) (_\sort (typ UX))) _\
        i)
    ]) _.
*/
}}.

Set Printing Universes.
About poly.
Check poly@{Set Type}.
About Box.

Elpi Query lp:{{ 
  coq.say {{ Set }},
  coq.unify-eq {{ Set }} (sort (typ U)) ok
}}.

Polymorphic Inductive tree (A : Type) :=
| leaf : A -> tree A
| node : A -> list (tree A) -> tree A.
Set Printing Universes.
Print tree.
Elpi Query lp:{{
  std.do! [coq.env.begin-module "M" none, coq.env.end-module _]  
}} lp:{{
pglobal (indt I) _ = {{ tree }},
coq.env.indt-decl I D,
coq.env.begin-module "M" none,
coq.say D,
std.assert-ok! (coq.typecheck-indt-decl D) "D illtyped",
coq.univ.print,
coq.env.add-indt D _,
coq.env.end-module _
}}.

Elpi Command Comm.
Elpi Accumulate  lp:{{
  main [indt-decl X] :- coq.say X,
    coq.env.add-indt X _.
}}.
Elpi Comm Class c {A : Type} (x : A -> A).
Goal c S. Abort.

Elpi Query lp:{{
  coq.typecheck-ty (sort (typ X)) A ok,
  A = typ TX,
  not(coq.univ.alg-super X TX),
  coq.say X ":" TX,
  @keep-alg-univs! => coq.typecheck-ty (sort (typ Y)) B ok,
  B = typ TY,
  coq.say Y ":" TY,
  coq.univ.alg-super Y TY,
  coq.say Y ":" TY
  .

}}.
