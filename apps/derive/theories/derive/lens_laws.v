(* Equations for lenses

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive Extra Dependency "lens_laws.elpi" as lens_laws.
From elpi.apps.derive Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive.lens.

Definition view_set_on {a c} (l : Lens a a c c) r := forall x,
  view l (set l x r) = x.
Definition view_set {a c} (l : Lens a a c c) := forall r, view_set_on l r.

Definition set_set_on {a c d} (l : Lens a a c d) r := forall x y,
  set l y (set l x r) = set l y r.
Definition set_set {a c d} (l : Lens a a c d) := forall r, set_set_on l r.

Definition set_view_on {a c} (l : Lens a a c c) r :=
  set l (view l r) r = r.
Definition set_view {a c} (l : Lens a a c c) := forall r, set_view_on l r.

Definition exchange_on {a b d e f} (l1 : Lens a a b d) (l2 : Lens a a e f) r := forall x y,
  set l1 x (set l2 y r) = set l2 y (set l1 x r).
Definition exchange {a b d e f} (l1 : Lens a a b d) (l2 : Lens a a e f) := forall r, exchange_on l1 l2 r.

Register view_set as elpi.derive.lens.view_set.
Register view_set_on as elpi.derive.lens.view_set_on.
Register set_set as elpi.derive.lens.set_set.
Register set_set_on as elpi.derive.lens.set_set_on.
Register set_view as elpi.derive.lens.set_view.
Register set_view_on as elpi.derive.lens.set_view_on.
Register exchange as elpi.derive.lens.exchange.
Register exchange_on as elpi.derive.lens.exchange_on.

Elpi Db derive.lens_laws.db lp:{{
  pred lens-laws-done i:inductive.
}}.

(* standalone *)
Elpi Command derive.lens_laws.
Elpi Accumulate File derive_hook.
Elpi Accumulate File lens_laws.
Elpi Accumulate Db derive.lens.db.
Elpi Accumulate Db derive.lens_laws.db.
Elpi Accumulate lp:{{ 
  main [str I, str O] :- !, coq.locate I (indt GR), derive.lens-laws.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.lens-laws.main GR "_" _.
  main _ :- usage.
   
  usage :- coq.error "Usage: derive.lens_laws <record name> [<prefix>]".
}}.
Elpi Typecheck.
      
(* hook into derive *)
Elpi Accumulate derive File lens_laws.
Elpi Accumulate derive Db derive.lens_laws.db.

#[phases=both] Elpi Accumulate derive lp:{{
dep1 "lens_laws" "lens".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "lens_laws" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{
  
derivation (indt T) Prefix ff (derive "lens_laws" (derive.lens-laws.main T N) (lens-laws-done T)) :- N is Prefix ^ "_".

}}.
