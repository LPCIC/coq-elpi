From elpi.apps Require Import tc.
Elpi TC Solver Override TC.Solver All.

Polymorphic Definition pidentity {A : Type} (a : A) := a.

Class C A (H : A -> A) (Z : A -> A)  := {}.

Elpi Accumulate TC.Solver lp:{{
  tc.print-goal.
  tc.print-compiled-goal.
  tc.print-post-process-goal.
}}.

Instance I A : C A pidentity pidentity. Qed.
(* 

  Elpi Accumulate TC.Solver lp:{{
    shorten tc-elpi.apps.tc.tests.polyUniv.{tc-C}.
    tc-C A
      (app [global {{:gref pidentity}} _, A])
      (app [global {{:gref pidentity}} U, A])
      (app [global {{:gref I}} U, A]).
  }}. *)

(* Through debugging:
tc.compile.instance-gr const «I» To 
pi c0 \
 pi c1 \
  pi c2 \
   pi c3 \
    pi c4 \
     pi c5 \
      tc-elpi.apps.tc.tests.polyUniv.tc-C c5 
       (app [global (const «pidentity») c3, c5]) 
       (app [global (const «pidentity») c3, c5]) 
       (app [global (const «I») c0, c5])
       
       This forces both univ instances of pidentity to be the same
       *)
Lemma test : True.
  eassert (forall A, C A pidentity pidentity).
  Set Printing Universes.
  (* Goal is : forall A : Type@{elpi.apps.tc.tests.polyUniv.55},
C@{elpi.apps.tc.tests.polyUniv.55} A 
pidentity@{elpi.apps.tc.tests.polyUniv.56}
pidentity@{elpi.apps.tc.tests.polyUniv.57} , notice that 56 and 57 do not necessarily match here *)
  intro A'.
  Elpi Trace.
  apply _. Show Proof. exact Logic.I.
Qed.
  (* The goal is <<< 
app
 [global (indt «C») (pr [] [«elpi.apps.tc.tests.polyUniv.63»]), c0, 
  app
   [global (const «pidentity») (pr [] [«elpi.apps.tc.tests.polyUniv.64»]), 
    c0], 
  app
   [global (const «pidentity») (pr [] [«elpi.apps.tc.tests.polyUniv.65»]), 
    c0]] >>>
[TC] the compiled goal is 
tc-elpi.apps.tc.tests.polyUniv.tc-C c0 
 (app [global (const «pidentity») X126^1, c0]) 
 (app [global (const «pidentity») X140^1, c0]) X20^1
[TC] the post-process goal list is 
[tc.compile.goal.unif-univ-constraint
  (global (const «pidentity») (pr [] [«elpi.apps.tc.tests.polyUniv.65»])) 
  (global (const «pidentity») X140^1), 
 tc.compile.goal.unif-univ-constraint
  (global (const «pidentity») (pr [] [«elpi.apps.tc.tests.polyUniv.64»])) 
  (global (const «pidentity») X126^1), 
 tc.compile.goal.unif-univ-constraint
  (global (indt «C») (pr [] [«elpi.apps.tc.tests.polyUniv.63»])) 
  (global (indt «C») X112^1)]
  *)

(* 
 tc.time-it tc.oTC-time-instance-search 
     (do
       [tc.compile.goal.unif-univ-constraint
         (global (const «pidentity») 
           (pr [] [«elpi.apps.tc.tests.polyUniv.102»])) 
         (global (const «pidentity») X140^1), 
        tc.compile.goal.unif-univ-constraint
         (global (const «pidentity») 
           (pr [] [«elpi.apps.tc.tests.polyUniv.101»])) 
         (global (const «pidentity») X126^1), 
        tc.compile.goal.unif-univ-constraint
         (global (indt «C») (pr [] [«elpi.apps.tc.tests.polyUniv.100»])) 
         (global (indt «C») X112^1)] , 
       tc-elpi.apps.tc.tests.polyUniv.tc-C c0 
        (app [global (const «pidentity») X126^1, c0]) 
        (app [global (const «pidentity») X140^1, c0]) X20^1 , 
       tc.link.solve-eta , tc.link.solve-llam) instance search 

*)