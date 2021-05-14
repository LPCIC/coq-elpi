
(**
   This file builds a reflexive tactic solving equalities in a monoid.

   We use elpi to:
   - reify an expression into a syntax tree
   - query a Db of known monoids
   - call a few ltac primitives in order to apply the corrctness theorem

*)

From elpi Require elpi.
Require Arith ZArith Psatz List ssreflect.

Import elpi.
Import Arith ZArith Psatz List ssreflect.

(* This module contains the reflexive normalizer and its correctness proof *)
Module MonoidTheory.

(* The syntax of terms *)
Inductive lang :=
| var (i : nat)        (* i-th variable in the context *)
| zero : lang          (* Neutral element *)
| add (x y : lang).    (* binary operation *)

(* Interpretation to T *)
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

  (* Correctness theorem. This is not the point of this demo, please don't
     look at the proofs ;-) *)
 Section assoc_reflection_proofs.
 Variable T : Type.
 Variable unit : T.
 Variable op : T -> T -> T.
 Hypothesis op_assoc : forall a b c, op a (op b c) = op (op a b) c.
 Hypothesis unit_l : forall a, op unit a = a.
 Hypothesis unit_r : forall a, op a unit = a.

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
elim: t s1 s2 => [||w1 + w2 + s1 s2] //=.
by case E1: (norm1 w1); case E2: (norm1 w2) => //= ++ [<- <-] /=;
  do 2! [ move=> /(_ _ _ (refl_equal _)) -> | move=> _];
  rewrite ?(norm1_zero E1) ?(norm1_zero E2) ?(norm1_var E1) ?(norm1_var E2).
Qed.

Lemma normAxP {l t1 t2} : interp T unit op l (normAx t1 t2) = op (interp T unit op l t1) (interp T unit op l t2).
Proof. by elim: t1 t2 => [||s1 Hs1 s2 Hs2] t2 //=; rewrite Hs1 Hs2 !op_assoc. Qed.

Lemma normAP {l} t : interp T unit op l (normA t) = interp T unit op l t.
Proof. by elim: t => //= x Hx y Hy; rewrite normAxP Hy. Qed.

Lemma norm_add {l t s1 s2} : norm t = add s1 s2 -> interp T unit op l t = op (interp T unit op l s1) (interp T unit op l s2).
Proof.
rewrite /norm; case E: (norm1 t) => [||x y]; rewrite //= (norm1_add E).
elim: x y s1 s2 {E} => //= [>[<- <- //=]|>[<- <-]|x + y + w s1 s2]; rewrite ?normAP //= ?unit_l //.
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



(* Finally, let's build the tactic *)

Import MonoidTheory.

(* This is the correctness theorem of our normalizer *)
Definition normP {T e op gamma t1 t2} p1 p2 p3 H := @normP_ T e op p1 p2 p3 gamma t1 t2 H.
About normP.
Open Scope Z_scope.

Goal forall x y z t, (x + y) + (z + 0 + t) = x + (y + z) + t.
Proof.
intros.

change (interp Z Z.zero Z.add (x::y::z::t::nil)
             (add (add (var 0) (var 1)) (add (add (var 2) zero) (var 3)))
        =
        interp Z Z.zero Z.add (x::y::z::t::nil)
              (add (add (var 0) (add (var 1) (var 2))) (var 3))).

apply: normP Z.add_assoc Z.add_0_l Z.add_0_r _.

reflexivity.
Qed.

(** Now, let's implement a tactic that does for us:
    - the change step (reification)
    - apply the correctness lemma
*)

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

Elpi Tactic monoid.
Elpi Accumulate Db monoid.db.
Elpi Accumulate lp:{{

% [mem L X N] asserts that X is at position N in L.
% The list is open-ended, that is it terminates with an Elpi unification
% variable, so that the list can be extended with new elements if needed.
% e.g. mem (3 :: L) 4 N ---> L = 4 :: L1, N = 1
% Note: we build a Coq list, since we have to generate that anyway. We could
% use an Elpi list or any other data structure here, but then we would need
% to convert back anyway.
pred mem o:term, o:term, o:term.
mem {{ lp:X :: _     }} X {{ O      }} :- !.
mem {{ _    :: lp:XS }} X {{ S lp:N }} :- mem XS X N.

% Give that [mem] works with open ended lists we need a way to close it (assign
% nil to the tail) at the very end of reification.
pred close o:term.
close {{ nil }} :- !.
close {{ _ :: lp:XS }} :- close XS.

% [quote Zero Op T AstT L] recognizes Zero and Op in T and generates the
% corresponding AstT using the "context" L for variables standing for
% terms that are not Zero nor Op
pred quote i:term, i:term, i:term, o:term, o:term.
quote Zero Op  {{ lp:Op lp:T1 lp:T2 }} {{ add lp:R1 lp:R2 }} L :- !,
  quote Zero Op T1 R1 L,
  quote Zero Op T2 R2 L.
quote Zero _   Zero {{ zero }} _ :- !.
quote _    _   T {{ var lp:R }} L :- mem L T R.

% This preliminary version of the tactic takes as arguments the monoid signature
% and changes the goal [A = B] into [interp L AstA = interp L AstB]
solve [trm Zero, trm Op] [G] _ :-
  G = goal _ Ev {{ @eq lp:T lp:A lp:B }} _ _,
  quote Zero Op A AstA L,
  quote Zero Op B AstB L,
  close L,
  % We are very low level here, we assign a term directly to the goal handler
  % while one could use ltac primitives (as we do later)
  Ty = {{   (interp lp:T lp:Zero lp:Op lp:L lp:AstA)
          = (interp lp:T lp:Zero lp:Op lp:L lp:AstB) }},
  % This implements the "change" tactic
  Ev = {{ (_ : lp:Ty) }}.

:name "error"
solve _ _ _ :- coq.error "Not an equality / no signature provided".

}}.
Elpi Typecheck.
Tactic Notation "monoid" constr(zero) constr(add) := elpi monoid (zero) (add).

(** Let's test the tactic *)
Goal forall x y z t, (x + y) + (z + 0 + t) = x + (y + z) + t.
Proof. 
  intros.
  monoid 0 Z.add.
  (* OK, the goal was reified for us, we can use normP now *)
  apply: normP Z.add_assoc Z.add_0_l Z.add_0_r _.
  reflexivity.
Qed.

(** Now let's register in the Db the monoid for Z *)
Elpi Accumulate monoid.db lp:{{

  is_monoid {{ Z }}
            {{ 0 }} {{ Z.add }}
            {{ Z.add_assoc }} {{ Z.add_0_l }} {{ Z.add_0_r }}.

}}.

(** Now let's improve the tactic. This time we don't expect the signature but
    rather look it up in the Db. *)
Ltac my_compute := vm_compute.

Elpi Accumulate monoid lp:{{

:before "error"
solve [] [G] GL :-
  G = goal _ _ {{ @eq lp:T lp:A lp:B }} _ _,
  is_monoid T Zero Op Assoc Ul Ur,
  quote Zero Op A AstA L,
  quote Zero Op B AstB L,
  close L,
  % This time we use higher level combinators, closer to the standard ltac1 ones
  thenl [
    refine {{ @normP lp:T lp:Zero lp:Op lp:L lp:AstA lp:AstB lp:Assoc lp:Ul lp:Ur _ }},
    coq.ltac1.call "my_compute" [], % https://github.com/coq/coq/issues/10769
    coq.ltac1.call "reflexivity" []
  ] G GL.

}}.
Elpi Typecheck.
Tactic Notation "monoid" := elpi monoid.

(** Let's test it once more *)
Goal forall x y z t, (x + y) + (z + 0 + t) = x + (y + z) + t.
Proof. 
  intros.
  monoid.
  Show Proof.
Qed.

Elpi Accumulate monoid.db lp:{{

  is_monoid {{ Z }}
            {{ 1 }} {{ Z.mul }}
            {{ Z.mul_assoc }} {{ Z.mul_1_l }} {{ Z.mul_1_r }}.

}}.

Goal forall x y z t, (x * y) * (1 * (z + t)) = x * y * (z + t).
Proof. 
  intros.
  monoid.
Qed.
