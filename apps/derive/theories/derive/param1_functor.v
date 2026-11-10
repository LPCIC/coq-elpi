(* Functorial property of params in param1 translation.
      Inductive I A PA : A -> Type := K : forall a b, I A PA a.
    Elpi derive.param1.functor is_I.
      Definition is_I_functor A PA PB (f : forall x, PA x -> PB x) a :
         I A PA a -> I A PB a.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive.elpi Extra Dependency "param1_functor.elpi" as param1_functor.
From elpi.apps.derive.elpi Extra Dependency "param1.db.elpi" as param1db.
From elpi.apps.derive.elpi Extra Dependency "param1_functor.db.elpi" as param1_functordb.

From elpi Require Import elpi.
From elpi.apps Require Import derive derive.param1.

Elpi Db derive.param1.functor.db lp:{{ accumulate "elpi.apps.derive.elpi/param1_functor.db". }}.

Elpi Command derive.param1.functor.
Elpi Accumulate File paramX.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.functor.db.
Elpi Accumulate File param1_functor.
Elpi Accumulate lp:{{ 
  main [str I, str O] :- !,
    coq.locate I IsGR,
    realiR T {coq.env.global IsGR},
    coq.env.global GR T,
    derive.param1.functor.main GR IsGR O _.
  main [str I] :- !,
    coq.locate I IsGR,
    realiR T {coq.env.global IsGR},
    coq.env.global GR T,
    derive.param1.functor.main GR IsGR "_functor" _.
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

derivation (indt T) _ ff (derive "param1_functor" (derive.on_param1 (indt T) derive.param1.functor.main "_functor") (derive.on_param1 (indt T) (_\T\_\_\sigma I\ T = indt I, param1-functor-for I _ _) _ _)).

}}.
