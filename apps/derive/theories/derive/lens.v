(* A lens, to see better.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)
From elpi.apps.derive Extra Dependency "lens.elpi" as lens.

From elpi Require Export elpi.

(* Coq stdlib has no lens data type so we declare one here. To override with
  your own "copy", use Register as below *)
Local Set Primitive Projections.
Record Lens (a b c d : Type) : Type := mkLens
{ view : a -> c
; over : (c -> d) -> a -> b
}.
Register mkLens as elpi.derive.lens.make.

Arguments view {_ _ _ _} _ _.
Arguments over {_ _ _ _} _ _ _.

Definition set {a b c d} (l : Lens a b c d) new := over l (fun _ => new).
Register set as elpi.derive.lens.set.
Register view as elpi.derive.lens.view.

Elpi Db derive.lens.db lp:{{
  pred lens-db o:inductive, o:string, o:constant.
}}.

Elpi Command derive.lens.
Elpi Accumulate File lens.
Elpi Accumulate Db derive.lens.db.
Elpi Accumulate lp:{{ 
  main [str I, str O] :- !, coq.locate I (indt GR), derive.lens.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.lens.main GR "_" _.
  main _ :- usage.
   
  usage :- coq.error "Usage: derive.lens <record name> [<output prefix>]".
}}.
Elpi Typecheck.
   
