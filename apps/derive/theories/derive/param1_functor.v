(* Functorial property of params in param1 translation.
      Inductive I A PA : A -> Type := K : forall a b, I A PA a.
    Elpi derive.param1.functor is_I.
      Definition is_I_functor A PA PB (f : forall x, PA x -> PB x) a :
         I A PA a -> I A PB a.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "param1_functor.elpi" as param1_functor.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive derive.param1.

Elpi Db derive.param1.functor.db lp:{{
  func param1-functor-db term, term -> term.
  func param1-functor-for inductive -> gref, list bool.
}}.

Elpi Command derive.param1.functor.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.param1.functor.db.
Elpi Accumulate File param1_functor.
Elpi Accumulate lp:{{ 
  main [str I, str O] :- !, coq.locate I (indt GR), derive.param1.functor.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.param1.functor.main GR "_functor" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.param1.functor <inductive type name> [<output suffix>]".
}}.  


(* hook into derive *)
Elpi Accumulate derive Db derive.param1.functor.db.
Elpi Accumulate derive File param1_functor.

#[phases="both"] Elpi Accumulate derive lp:{{
dep1 "param1_functor" "param1".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "param1_functor" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation (indt T) _ ff (derive "param1_functor" (derive.on_param1 T derive.param1.functor.main "_functor") (derive.on_param1 T (T\_\_\param1-functor-for T _ _) _ _)).

}}.
