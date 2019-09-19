
(**
   This example covers reifying an expression into a syntax tree.

   This operation cannot be performed in Gallina itself, hence a meta
   language is needed. Typical approaches are core written in ML, Ltac,
   type class resolution.

*)

Require Arith ZArith Psatz List ssreflect.
From elpi Require Import elpi.



Import Arith ZArith Psatz List ssreflect.

Module MonoidTheory.

(* The syntax of terms *)
Inductive lang :=
| var (i : nat)        (* De Bruijn index, i-th variable in the context *)
| zero : lang          (* Neutral element *)
| add (x y : lang).    (* binary operation *)

(* Interpretation to Z *)
Fixpoint interp T (e : T) (op : T -> T -> T) (gamma : list T) (t : lang) : T :=
match t with
| var v => nth v gamma e
  | zero => e
  | add x y => op (interp T e op gamma x) (interp T e op gamma y)
  end.
 

 (* normalization of parentheses and units *)
 Fixpoint normAx t1 acc :=
   match t1 with
   | add t1 t2 => normAx t1 (normAx t2 acc)
   | _ => add t1 acc
   end.
 Fixpoint normA t :=
   match t with
   | add s1 s2 => normAx s1 (normA s2)
   | _ => t
   end.
 Fixpoint norm1 t :=
  match t with
  | var _ => t
  | zero => t
  | add t1 t2 =>
     match norm1 t1 with
     | zero => norm1 t2
     | t1 =>
         match norm1 t2 with
         | zero => t1
         | t2 => add t1 t2
         end
     end
  end.
 Definition norm t := normA (norm1 t).

  (* Correctness theorem *)
 Section assoc_reflection_proofs.
 Variable T : Type.
 Variable unit : T.
 Variable op : T -> T -> T.
 Hypothesis op_assoc : forall a b c, op a (op b c) = op (op a b) c.
 Hypothesis unit_l : forall a, op unit a = a.
 Hypothesis unit_r : forall a, op a unit = a.

 (*
Lemma norm1_add {t1 t2} : norm1 (add t1 t2) = 
                     if norm1 t1 is zero then norm1 t2 else
                     if norm1 t2 is zero then norm1 t1 else
                     add (norm1 t1) (norm1 t2).
Proof. by case E1: (norm1 t1); case E2: (norm1 t2); rewrite /= ?E1 ?E2. Qed.

Lemma norm_add {t1 t2} :
  norm (add t1 t2) = if norm1 t1 is zero then normA (norm1 t2) else
                     if norm1 t2 is zero then normA (norm1 t1) else
                     normA (add (norm1 t1) (norm1 t2)).
Proof. by rewrite /norm norm1_add; case E1: (norm1 t1); case E2: (norm1 t2). Qed.
*)

Lemma normAxA t1 t2 : normAx t1 (normA t2) = normA (add t1 t2).
Proof. by []. Qed.

Lemma normAx_add {t1 t2 s} : normAx t1 t2 = s -> exists s1 s2, s = add s1 s2.
Proof.
elim: t1 t2 s => /= [i||w1 H1 w2 H2] t2 s <-; try by do 2 eexists; reflexivity.
by case E: (normAx _ _); case/H1: E => s1 [s2 ->]; do 2 eexists; reflexivity.
Qed.

Lemma norm1_zero {l t} : norm1 t = zero -> interp T unit op l t = unit.
Proof.
by elim: t => [||s1 + s2] //=; case E1: (norm1 s1); case E2: (norm1 s2) => //= -> // ->.
Qed.

Lemma norm_zero {l t} : norm t = zero -> interp T unit op l t = unit.
Proof.
rewrite /norm; case E: (norm1 t) => [||x y] //; first by rewrite (norm1_zero E).
by move/normAx_add=> [] ? [].
Qed.

Lemma norm1_var {l t j} : norm1 t = var j -> interp T unit op l t = nth j l unit.
Proof.
elim: t => [i [->]||s1 + s2] //=; case E1: (norm1 s1); case E2: (norm1 s2) => //=.
  by rewrite (norm1_zero E2) unit_r => + _ H => ->.
by rewrite (norm1_zero E1) unit_l => _ + H => ->.
Qed.

Lemma norm_var {l t j} : norm t = var j -> interp T unit op l t = nth j l unit.
Proof.
rewrite /norm; case E: (norm1 t); rewrite /= ?(norm1_var E) //; first by move=> [->].
by move/normAx_add=> [] ? [].
Qed.

Lemma norm1_add {l t s1 s2} : norm1 t = add s1 s2 -> interp T unit op l t = op (interp T unit op l s1) (interp T unit op l s2).
Proof.
elim: t s1 s2 => [i||w1 + w2 + s1 s2 E] //=; move: E => /=; case E1: (norm1 w1); case E2: (norm1 w2) => //=;
  rewrite /= ?(norm1_zero E1) ?(norm1_zero E2) ?(norm1_var E1) ?(norm1_var E2) //= => -[<- <-] //=;
  try move=> /(_ _ _ (refl_equal _)) <-;
  try move=> + /(_ _ _ (refl_equal _)) <-;
  rewrite ?unit_l ?unit_r //;
  by move=> /(_ _ _ (refl_equal _)) <-.
Qed.

Lemma normAxP {l t1 t2} : interp T unit op l (normAx t1 t2) = op (interp T unit op l t1) (interp T unit op l t2).
Proof. by elim: t1 t2 => [||s1 Hs1 s2 Hs2] t2 //=; rewrite Hs1 Hs2 !op_assoc. Qed.

Lemma normAP {l} t : interp T unit op l (normA t) = interp T unit op l t.
Proof. by elim: t => //= x Hx y Hy; rewrite normAxP Hy. Qed.

Lemma norm_add {l t s1 s2} : norm t = add s1 s2 -> interp T unit op l t = op (interp T unit op l s1) (interp T unit op l s2).
Proof.
rewrite /norm; case E: (norm1 t) => [||x y]; rewrite //= (norm1_add E).
elim: x y s1 s2 {E} => //= [????[<- <- //=]|???[<- <-]|x + y + w s1 s2]; rewrite ?normAP //= ?unit_l //.
by rewrite normAxA -!op_assoc => ++ E => /(_ _ _ _ E) ->.
Qed.

Lemma normP_ l t1 t2 : norm t1 = norm t2 -> interp T unit op l t1 = interp T unit op l t2.
Proof.
case E: (norm t2) => [?||??] => [/norm_var|/norm_zero|/norm_add] ->.
  by rewrite (norm_var E).
  by rewrite (norm_zero E).
by rewrite (norm_add E).
Qed.

End assoc_reflection_proofs.
End MonoidTheory.

Import MonoidTheory.

Definition normP {T op zero l t1 t2} p1 p2 p3 H := @normP_ T op zero p1 p2 p3 l t1 t2 H.

Open Scope Z_scope.

Goal forall x y z t, (x + y) + (z + 0 + t) = x + (y + z) + t.
Proof.
intros.
change (interp Z Z.zero Z.add (x::y::z::t::nil)(add (add (var 0) (var 1))
                                           (add (add (var 2) zero) (var 3))) =
        interp Z Z.zero Z.add (x::y::z::t::nil)
              (add (add (var 0) (add (var 1) (var 2))) (var 3))).
apply: normP Z.add_assoc Z.add_0_l Z.add_0_r _.
reflexivity.
Qed.

(* This is for later *)
Elpi Db monoid.db lp:{{ 
  pred is_monoid
    i:term, % type
    o:term, % zero
    o:term, % op
    o:term, % assoc
    o:term, % unit_l
    o:term. % unit_r
}}.

Elpi Tactic reify_list.
Elpi Accumulate Db monoid.db.
Elpi Accumulate lp:{{

% 
pred mem o:term, o:term, o:term.
mem {{ lp:X :: lp:XS_ }} X {{0%nat}} :- !.
mem {{ _ :: lp:XS }} X {{S lp:N}} :- mem XS X N.

pred close o:term.
close {{ nil }} :- !.
close {{ _ :: lp:XS }} :- close XS.

pred quote i:term, i:term, i:term, o:term, o:term.
quote Zero Op (app [Op, T1, T2]) {{ add lp:R1 lp:R2 }} L :- !,
  quote Zero Op T1 R1 L,
  quote Zero Op T2 R2 L.
quote Zero _ Zero {{ zero }} _ :- !.
quote _ _ T {{ var lp:R }} L :- mem L T R.

solve [trm Zero, trm Op] [goal Ctx P {{ lp:A = lp:B }} _] _ :-
  quote Zero Op A AstA L,
  quote Zero Op B AstB L,
  close L,
  !,
  Ctx => coq.typecheck Zero T,
  Ty = {{ (interp lp:T lp:Zero lp:Op lp:L lp:AstA) = (interp lp:T lp:Zero lp:Op lp:L lp:AstB)}},
  P = {{ (fun x : lp:Ty => x) _ }}.

:name "error"
solve _ _ _ :- coq.error "Not an equality".

}}.
Elpi Typecheck.
Tactic Notation "monoid_refl" constr(zero) constr(add) := elpi reify_list (zero) (add).

Goal forall x y z t, (x + y) + (z + 0 + t) = x + (y + z) + t.
Proof. 
  intros.
  monoid_refl 0 Z.add.
  apply: normP Z.add_assoc Z.add_0_l Z.add_0_r _.
  reflexivity.
Qed.

Elpi Accumulate monoid.db lp:{{

  is_monoid {{ Z }} {{ 0 }} {{ Z.add }} {{ Z.add_assoc }} {{ Z.add_0_l }} {{ Z.add_0_r }}.

}}.

Elpi Accumulate reify_list lp:{{

:before "error"
solve [] [G] GL :-
  G = goal _ _ {{ @eq lp:T lp:A lp:B }} _,
  std.assert! (is_monoid T Zero Op Assoc Ul Ur) "not a monoid",
  quote Zero Op A AstA L,
  quote Zero Op B AstB L,
  close L,
  !,
  thenl [
    refine {{ @normP lp:T lp:Zero lp:Op lp:L lp:AstA lp:AstB lp:Assoc lp:Ul lp:Ur _ }},
    coq.ltac1.call "compute" [], % https://github.com/coq/coq/issues/10769
    coq.ltac1.call "reflexivity" []
  ] G GL.

}}.
Elpi Typecheck.
Tactic Notation "monoid_refl" := elpi reify_list.

Goal forall x y z t, (x + y) + (z + 0 + t) = x + (y + z) + t.
Proof. 
  intros. 
  monoid_refl.
Qed.
