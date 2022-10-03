(* Functorial property of params in param1 translation.
      Inductive I A PA : A -> Type := K : forall a b, I A PA a.
    Elpi derive.param1.functor is_I.
      Definition is_I_functor A PA PB (f : forall x, PA x -> PB x) a :
         I A PA a -> I A PB a.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive Extra Dependency "param1_functor.elpi" as param1_functor.

From elpi Require Export elpi.

Elpi Db derive.param1.functor.db lp:{{
  pred param1-functor-db i:term, i:term, o:term.
  pred param1-functor-for i:inductive, o:gref, o:list bool.
}}.

Elpi Command derive.param1.functor.
Elpi Accumulate Db derive.param1.functor.db.
Elpi Accumulate File param1_functor.
Elpi Accumulate lp:{{ 
  main [str I, str O] :- !, coq.locate I (indt GR), derive.param1.functor.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.param1.functor.main GR "_functor" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.param1.functor <inductive type name> [<output suffix>]".
}}.  
Elpi Typecheck.
