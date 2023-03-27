From elpi.apps Require Import tc.myEqDec.eqDec_proof.

(* Print HintDb typeclass_instances. *)
(* Print Instances EqDec. *)

(* =======================================
           Opaque vs Transparent 
=========================================*)
Definition nat' := nat.

Local Typeclasses Opaque nat'.
Check (fun (x y : nat') => x == y).
Compute ((3: nat') == 4).

#[local]Typeclasses Transparent nat'.
Check (fun (x y : nat') => x == y).
Compute ((3: nat') == 4).

(* =======================================
                Custom TC opaque
=========================================*)
Definition tc_opaque {A} (x : A) := x.
Local Typeclasses Opaque tc_opaque.

Check ((fun (x y : (tc_opaque nat)) => x == y)).
Check (fun (x y : nat) => x == y).

(* =======================================
          Generalize Variables
=========================================*)
Generalizable All Variables.
Definition sym `(x:A) : `(x = y -> y = x) := fun _ p => eq_sym p.

Generalizable No Variables.
Definition sym1 {A : Type} `(x:A, y:A) : `(x = y -> y = x) := fun p => eq_sym p.

Print sym.
Print sym1.

(* In sym the types of A and y are implicitly generalized by coq *)


(* =======================================
          Set the depth of search
=========================================*)

(* The depth to unify a prod is 2, if we set 
the depth to 1, we are not able to find the 
instance we are working with *)
Set Typeclasses Debug.
Set Typeclasses Depth 1.
Check ((3, true) == (3, false)).

(* -1 set the depth to unbounded *)
Set Typeclasses Depth -1.
Compute ((3, true) == (3, false)).

(* =======================================
                DFS vs BFS
=========================================*)

Typeclasses eauto := debug (bfs).
Check ((3, true) == (3, false)).

Typeclasses eauto := debug (dfs).
Check ((3, true) == (3, false)).

(* 
Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
1: looking for (EqDec (nat * bool)) without backtracking
1.1: simple apply @eq_prod on (EqDec (nat * bool)), 2 subgoal(s)
1.1-1 : (EqDec nat)
1: looking for (EqDec (nat * bool)) without backtracking
1.1: simple apply @eq_prod on (EqDec (nat * bool)), 2 subgoal(s)
1.1-1 : (EqDec nat)
1.1-1: looking for (EqDec nat) without backtracking
1.1-1.1: exact eq_int on (EqDec nat), 0 subgoal(s)
1.1-2 : (EqDec bool)
1.1-2: looking for (EqDec bool) without backtracking
1.1-2.1: exact eq_bool on (EqDec bool), 0 subgoal(s)

Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
1: looking for (EqDec (nat * bool)) without backtracking
1.1: simple apply @eq_prod on (EqDec (nat * bool)), 2 subgoal(s)
1.1-1 : (EqDec nat)
1.1-1: looking for (EqDec nat) without backtracking
1.1-1.1: exact eq_int on (EqDec nat), 0 subgoal(s)
1.1-2 : (EqDec bool)
1.1-2: looking for (EqDec bool) without backtracking
1.1-2.1: exact eq_bool on (EqDec bool), 0 subgoal(s)
*)

(* =======================================
                  Idtac
=========================================*)

Local Obligation Tactic := idtac.