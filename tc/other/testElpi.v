From elpi Require Import elpi.

(** Data bases are accumulated by name, hence can be shared among multiple
    commands or across successive executions of the same command.
    
    Let's start with a db containing international phone prefixes *)

Elpi Db eqDec.db lp:{{ 
  pred eqDec o:attribute-type, o:attribute-type, o:(prop -> (prop -> prop)).
  eqDec bool bool (x\ y\ if x y (not y)).
}}.

Elpi Command print_db.
Elpi Accumulate Db eqDec.db.
Elpi Accumulate lp:{{
  main [] :- std.findall (eqDec _ _ _) L, !, coq.say "The Db contains" L.
}}.
Elpi Typecheck.
Set Warnings "+elpi".
Elpi print_db.
Elpi Query lp:{{
  % eqDec false false,
  % X1 = (fun (x\ (fun y\ if (x) (y) (not y)))),
  GR = global {coq.locate "nat"},
  GR = {{nat}},
  X = fun `T` _ (t\ fun `S` _ (s\ fun `x` t (x\ fun `y` s (y\ y)))), % term
  Y = (x\ y\ y), % freccia di elpi
  % coq.say ((X true) false).
  T = (app [X, GR, GR, {{1}}, {{2}}]),
  unwind {whd T []} RES,
  (coq.typecheck T Ty D),
  T1 = (app [X, _, _, {{1}}, {{true}}]),
  (coq.typecheck T1 Ty1 D1)
  .
}}.

Elpi Query lp:{{
  % L = (app [{{nat}}, (app [{{nat}}, {{nat}}])]),
  % L1 = {{nat -> nat -> nat}},
  SND1 = fun `T` _ (t\ fun `S` _ (s\ fun `x` t (x\ fun `y` s (y\ y)))),
  SND2 = fun _ _ (x\ fun _ _ (y\ y)),
  Z = (app [SND1, {{nat}}, {{nat}}, {{1}}, {{2}}]),
  unwind {whd Z []} RES,
  coq.typecheck Z Ty _,
  A = (app [SND2, {{1}}, {{false}}]),
  unwind {whd A []} RES2,
  coq.typecheck A Ty1 _,
  B = (app [SND2, {{false}}, {{false}}]),
  unwind {whd A []} RES3
  .
}}.
Elpi Typecheck.

Elpi Query lp:{{
  X = fun `T` _ (t\ fun `S` _ (s\ fun `x` t (y\ y))). % term.
}}.

Elpi Query lp:{{
  Y = (x\y\y),
  R = Y 1 2

}}.

Elpi Query lp:{{
  % A = {{∀ {A B: Type}, A = B}}.
  A = {{forall {A B: Type}, A = B}}.
}}.

Elpi Query lp:{{
  coq.say {{ forall a : nat, a = 0 }}.
}}.

Elpi Query lp:{{
  (prod A Ty X) = {{ forall a : nat, a = 0 }},
  coq.say {{ forall a : nat, a = 0 }}.
}}.

(* Test decompose *)
Elpi Query lp:{{
  (prod A Ty x\ app [B, C, D x, E]) = {{ forall a : nat, a = 0 }},
  coq.say {{ forall a : nat, a = 0 }}.
}}.

Elpi Query lp:{{
  A = {{forall {A B: nat}, A = B}}.
}}.

Elpi Query lp:{{
  % (= (prod `B` T2 F) (prod `A` (global (indt «nat»)) (prod `B` (global (indt «nat»)) (app (:: (global (indt «eq»)) (:: (_uvk_542_ c5 c6) (:: c5 (:: c6 [])))))))) has type (X26^4 -> prop) but is used with type (term -> term)
  prod _ _ F = 
  	{{forall {A B: nat}, A = B}}.
}}.

Elpi Query lp:{{
  prod A TA (x\ prod B TB (y\ app [F, TF, X x y, Y x y])) = {{forall {A B: nat}, A = B}}.
}}.

From stdpp Require Import base.

Elpi Query lp:{{
  A = {{∀ {A B C : Type} (R1 : relation A) (R2 : relation B) (R3 : relation C) (f : A → B) (g : B → C),Inj R1 R2 f → Inj R2 R3 g → Inj R1 R3 (g ∘ f)}}.
}}.

Elpi Query lp:{{
   GR = global {coq.locate "Inj"}.
}}.

Elpi Query lp:{{
  coq.locate "Inj" A.
}}.

Elpi Query lp:{{
  (prod _ T1 (c0\ prod _ _ (c1\ prod _ _ (c2\ prod _ _ (c3\ prod _ _ (c4\ prod _ _ (c5\ prod _ _ (c6\ prod _ _ (c7\ prod _ (app [_, _, _, _ ,_ , _])  (c8\ prod _ _ (c9\ app [_, _, _, _, _, _]))))))))))) = {{∀ {A B C : Type} (R1 : relation A) (R2 : relation B) (R3 : relation C) (f : A → B) (g : B → C),Inj R1 R2 f → Inj R2 R3 g → Inj R1 R3 (g ∘ f)}}.
}}.
