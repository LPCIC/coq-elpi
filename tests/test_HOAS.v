From elpi Require Import elpi.

Elpi Tactic test1.
Elpi Accumulate lp:{{

solve G GS :- pi x\
  coq.sigma.print,
  print_constraints,
  refine {{ fun w : _ => _ }} G GS.
}}.
Elpi Typecheck.

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
Elpi Typecheck.

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
Elpi Typecheck.

Elpi kwd fun in as 4 end match return => : := { } ; , | "x" 1 H (fun x => match x as y in False return nat with end).

End kwd.

Elpi Query lp:{{
  coq.env.begin-section "xxxxx",
  coq.univ.new [] U,
  T = sort (typ U),
  coq.env.add-section-variable "a" T _,
  coq.env.end-section
}}.

Elpi Db univs.db lp:{{ pred u o:univ. }}.
Elpi Command test_u.
Elpi Accumulate Db univs.db.
Fail Elpi Query lp:{{
  coq.univ.new [] U,
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
  @holes! => coq.typecheck (X a a) TY ok,
  coq.sigma.print,
  coq.say (X a a) ":" TY.
}}.

(* primitive *)
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
Elpi Typecheck.

From Coq Require Import PrimInt63.
Open Scope int63_scope.
Elpi primitive (PrimInt63.add 2000000003333002 1).

From Coq Require Import PrimFloat.
Open Scope float_scope.
Elpi primitive (2.4e13 + 1).

Module P.
Set Primitive Projections.

Unset Auto Template Polymorphism.
Record foo {A : Type} := { p1 : nat; p2 : A }.
Definition x : foo := {| p1 := 3; p2 := false |}.

Unset Primitive Projections.
End P.

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
Elpi Typecheck.

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
Elpi Typecheck.
Elpi ifte (if true then 1 else 2).

(* gref quotations *)

Register nat as elpi.test.nat.

Elpi Query lp:{{

  coq.locate "lib:elpi.test.nat" {{:gref nat }},
  coq.locate "nat" {{:gref lib:elpi.test.nat }}.

}}.
