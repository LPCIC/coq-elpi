(* Equations for lenses

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi.
From elpi.apps Require Export derive.lens.

Definition law1_on {a c} (l : Lens a a c c) r := forall x,
  view l (set l x r) = x.
Definition law1 {a c} (l : Lens a a c c) := forall r, law1_on l r.

Definition law2_on {a c d} (l : Lens a a c d) r := forall x y,
  set l y (set l x r) = set l y r.
Definition law2 {a c d} (l : Lens a a c d) := forall r, law2_on l r.

Definition law3_on {a c} (l : Lens a a c c) r :=
  set l (view l r) r = r.
Definition law3 {a c} (l : Lens a a c c) := forall r, law3_on l r.

Definition law4_on {a b d e f} (l1 : Lens a a b d) (l2 : Lens a a e f) r := forall x y,
  set l1 x (set l2 y r) = set l2 y (set l1 x r).
Definition law4 {a b d e f} (l1 : Lens a a b d) (l2 : Lens a a e f) := forall r, law4_on l1 l2 r.

Register law1 as elpi.derive.lens.law1.
Register law1_on as elpi.derive.lens.law1_on.
Register law2 as elpi.derive.lens.law2.
Register law2_on as elpi.derive.lens.law2_on.
Register law3 as elpi.derive.lens.law3.
Register law3_on as elpi.derive.lens.law3_on.
Register law4 as elpi.derive.lens.law4.
Register law4_on as elpi.derive.lens.law4_on.

Elpi Command derive.lens_laws.
Elpi Accumulate File "elpi/lens_laws.elpi".
Elpi Accumulate Db derive.lens.db.
Elpi Accumulate lp:{{ 
  main [str I] :- !, coq.locate I (indt GR), derive.lens-laws.main GR _.
  main _ :- usage.
   
  usage :- coq.error "Usage: derive.lens_laws <record name>".
}}.
Elpi Typecheck.
      
   