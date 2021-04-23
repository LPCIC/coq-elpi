(* A lens, to see better.

   license: GNU Lesser General Public License Version 2.1 or later           
   ------------------------------------------------------------------------- *)

From elpi Require Export elpi.

(* Coq stdlib has no lens data type so we declare one here. To override with
  your own "copy", use Register as below *)
Local Set Primitive Projections.
Record Lens (a b c d : Type) : Type := mkLens
{ view : a -> c
; over : (c -> d) -> a -> b
}.
Register mkLens as elpi.derive.mklens.

Elpi Command derive.lens.
Elpi Accumulate File "elpi/lens.elpi".
Elpi Accumulate lp:{{ 
  main [str I, str O] :- !, coq.locate I (indt GR), derive.lens.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.lens.main GR "_" _.
  main _ :- usage.
   
  usage :- coq.error "Usage: derive.lens <record name> [<output prefix>]".
}}.
Elpi Typecheck.
   
