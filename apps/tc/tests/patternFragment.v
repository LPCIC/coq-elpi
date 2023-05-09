From elpi.apps Require Import compiler.


Class X (A: Type).
Class Y (A: Type).
Class Z (A: Type).

Local Instance Inst1: Y (bool * bool). Qed. 
Local Instance Inst2 A F: (forall (a: Type), Y (F a)) -> Z A. Qed.
Elpi Debug "here".

Elpi Override TC TC_check All.
Elpi AddAllInstances.
Elpi Print TC_check.


Goal  Z bool.
  apply _.
Qed.

(* 
Elpi Accumulate TC_check lp:{{
  tc {{:gref Z}} {{Z lp:A}} {{Inst2 lp:A lp:{{fun _ _ F}} lp:{{fun _ _ S}}}} :-
    pi a\ tc {{:gref Y}} (app [global {{:gref Y}}, F a]) (S a).  
}}.
Elpi Typecheck TC_check.

Goal  Z bool.
  apply _.
Qed. 
*)