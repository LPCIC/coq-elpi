From elpi Require Import compiler.
Elpi Debug "simple-compiler".
Set AddModes.

Class A (S : Type) (T : Type).
Class B (S : Type) (T : Type).
Class C (S : Type).

Global Hint Mode A + - : typeclass_instances.
Global Hint Mode B - + : typeclass_instances.

Global Instance A1 : A nat nat. Admitted.
Global Instance B1 : B nat nat. Admitted.


Global Instance C1 {S T : Type} `{A T S, B S T} : C bool. Admitted.

Elpi AddAllClasses. 
Elpi AddAllInstances.
Elpi Override TC TC_solver All.

Elpi Accumulate TC_solver lp:{{
  pred get_premises i:term, i:list term, i:list term, o:prop.
  get_premises (prod _ A B) Types Vars (pi x\ R x) :- 
    pi x\ get_premises (B x) [A | Types] [x | Vars] (R x).
  get_premises _ T V (pi x\ T x) :- 
    coq.say T V.
}}.
Elpi Typecheck TC_solver.

Elpi Query TC_solver lp:{{
  coq.env.typeof {{:gref C1}} T,
  get_premises T [] [] _.
}}.

(* Here should give an error of cyclic dependencies *)
Goal C bool.
  apply _.
Qed.