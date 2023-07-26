From elpi Require Import compiler.
Require Import Bool Setoid.

Elpi Debug "simple-compiler".
Unset TC_NameFullPath.

Class Eqb (T : Type) := {
  eqb : T -> T -> bool; 
  eq_leibniz : forall (a b : T), eqb a b = true -> a = b
}.

(* #[refine] Global Instance eqBool : @Eqb bool := {
  eqb a b := if a then b else negb b
}.
Proof. destruct a, b; easy. Qed. *)

#[refine] Global Instance eqUnit : @Eqb unit := {
  eqb a b := true
}.
Proof. destruct a, b; easy. Qed.

#[refine] Global Instance eqProd {A B : Type} `(Eqb A, Eqb B) : @Eqb (A * B) := {
  eqb x y := match x, y with 
    | (a, b), (c, d) => (eqb a c) && (eqb b d)
  end
}.
Proof.
  intros [] [].
  rewrite andb_true_iff, pair_equal_spec; split; apply eq_leibniz; easy.
Qed.

#[refine] Global Instance eqNat : Eqb nat := {
  eqb := fix f x y := match x, y with 
  | O, O => true | S x, S y => f x y | _, _ => false 
  end
}.
Proof.
  induction a, b; try easy; intros;
  apply eq_S, IHa; easy.
Qed.

Elpi AddAllClasses.
Elpi AddAllInstances.
Elpi Override TC TC_solver All.

Elpi Print TC_solver "TC_solver.json".

Elpi Accumulate TC_solver lp:{{
  % :after "firstHook"
  % tc-Eqb A _ :- coq.say "Solving" A, fail.

  % tc-Eqb A _ :- !, coq.say "No instance found for" A.
}}.

Check (eqb (tt, tt) (tt, tt)).

Elpi Accumulate TC_solver lp:{{
  :after "firstHook"
  tc-Eqb {{prod lp:A lp:B}} Sol :- 
    A = B, !, coq.say "XX", tc-Eqb A PA,
    Sol = {{let p := lp:PA in @eqProd lp:A lp:B p p}}.
}}.
Elpi Typecheck TC_solver.

Elpi Override TC TC_solver All.
Check (eqb (tt, tt) (tt, tt)).