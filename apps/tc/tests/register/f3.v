From elpi.apps.tc.tests.register Require Import f2.

(*
  Note that in f2, auto_compiler has been deactivated,
  therefore I3 should not be added
*)

Instance I3 : A 3. Qed.

Goal A 3. Fail apply _. Abort.

Elpi Command custom_observer. 
Elpi Accumulate lp:{{
  main L :- 
    coq.say "Received the following event" L.
}}.

Elpi TC Activate Observer auto_compiler.
Elpi Register TC Compiler custom_observer.
Elpi TC Activate Observer custom_observer.

(* Here we have two active event listener for the instance creation:
   custom observer which simply prints the received event and 
   auto_compiler that adds I4 to the db
*)
Instance I4 : A 4. Qed.

Goal A 4. apply _. Qed.
