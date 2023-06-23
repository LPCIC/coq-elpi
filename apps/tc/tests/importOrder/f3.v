From elpi.apps.tc.tests.importOrder Require Import f1.

(* Module M1.
  From elpi.apps.tc.tests.importOrder Require Import f2a.
  From elpi.apps.tc.tests.importOrder Require Import f2b.

  Check (_ : A _).
  (* Print HintDb typeclass_instances. *)

  Elpi Override TC TC_solver All.

  Elpi Accumulate TC_solver lp:{{
    :after "firstHook"
    tc _ A _ :- coq.say "Searching for:" A, fail.
  }}.

  Check (_ : A _).
End M1.
Reset M1.

Module M2.
  From elpi.apps.tc.tests.importOrder Require Import f2b.
  From elpi.apps.tc.tests.importOrder Require Import f2a.

  Check (_ : A _).

  Elpi Override TC TC_solver All.

  Elpi Accumulate TC_solver lp:{{
    :after "firstHook"
    tc _ A _ :- coq.say "Searching for:" A, fail.
  }}.

  Check (_ : A _).
End M2.
Reset M2.

Module M3.
  Local Instance f3a : A nat := {f x := x}.
  Local Instance f3b : A nat := {f x := x}.
  Local Instance f3c : A nat := {f x := x}.

  Section S1.
    Global Instance f3d : A nat := {f x := x}.
    Global Instance f3e : A nat := {f x := x}.
    Global Instance f3f : A nat := {f x := x}.
    Print HintDb typeclass_instances.
  End S1.

  Section S2.
    Context (T : Set).
    Global Instance f3g : A T := {f x := x}.
  End S2.

  Section S3.
    Global Instance f3h T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.
  End S3.

End M3.

Reset M3.

Module M4.
  From elpi.apps.tc.tests.importOrder Require Import f2b.
  Elpi AddAllInstances.

  Print HintDb typeclass_instances.

  Elpi Print TC_solver "TC_solver.html" ".*elpi.[^a].*" ".*:.*[0-9]+".


  Global Instance f3a' T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.
  Module M4'.
    From elpi.apps.tc.tests.importOrder Require Import f2a.
    (* Elpi AddAllInstances. *)
    Print HintDb typeclass_instances.

    Global Instance f3a : A nat := {f x := x}.
    Elpi AddInstances f3a.
    Print HintDb typeclass_instances.

    Section S1.
      Global Instance f3b : A nat := {f x := x}.
      Elpi AddInstances f3b.
      Section S1'.
        Global Instance f3c : A nat := {f x := x}.
        Elpi AddInstances f3c.
        Print HintDb typeclass_instances.
      MySectionEnd.
      Print HintDb typeclass_instances.
    MySectionEnd.
    Print HintDb typeclass_instances.

    Section S2.
      Global Instance f3h T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.
      Elpi AddInstances f3h.
      Print HintDb typeclass_instances.
    MySectionEnd.
  End M4'.

  Print HintDb typeclass_instances.
  (* Elpi AddAllInstances. *)
  Elpi Print TC_solver "TC_solver1.html" ".*elpi.[^a].*" ".*:.*[0-9]+". 
End M4.

Reset M4.

Module M5.
  From elpi.apps.tc.tests.importOrder Require Import f2b.

  Global Instance f3a' T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.
  Module M4'.
    From elpi.apps.tc.tests.importOrder Require Import f2a.

    Global Instance f3a : A nat := {f x := x}.

    Section S1.
      Global Instance f3b : A nat := {f x := x}.
      Section S1'.
        Global Instance f3c : A nat := {f x := x}.
      MySectionEnd.
    MySectionEnd.

    Section S2.
      Global Instance f3h T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.
    MySectionEnd.
  End M4'.

  Elpi AddAllInstances. 
  Elpi Print TC_solver "TC_solver1.html" ".*elpi.[^a].*" ".*:.*[0-9]+".
  Print HintDb typeclass_instances.

End M5.

Reset M5.

Module M6.
  Global Instance f3a : A nat := {f x := x}.
  Global Instance f3b : A nat := {f x := x}.
  Global Instance f3c : A nat := {f x := x}.
  (* Elpi AddAllInstances. *)
  Elpi Print TC_solver "TC_solver.html" ".*elpi.[^a].*" ".*:.*[0-9]+".

  Section S1.
    Global Instance f3d : A nat := {f x := x}.
    Global Instance f3e : A nat := {f x := x}.
    Global Instance f3f : A nat := {f x := x}.
  MySectionEnd.
  Elpi AddAllInstances.
  Elpi Print TC_solver "TC_solver.html" ".*elpi.[^a].*" ".*:.*[0-9]+".
End M6.

Reset M6. *)

Module M7.
  Section S1.
    Context (T : Set).
    Global Instance f3a : A T := {f x := x}.
    Elpi AddInstances f3a.
    Section S2.
      Context (T1 : Set).
      Global Instance f3b : A T1 := {f x := x}.
      Elpi AddInstances f3b.
      Elpi print_instances.

      (* Elpi Query TC_solver lp:{{
        coq.env.section SVars1,
        coq.env.end-section,
        coq.env.section SVars2
      }}. *)

    MySectionEnd.
    Elpi print_instances.
  MySectionEnd.
  Elpi print_instances.
  Print HintDb typeclass_instances.

  (* TODO: instance f3b depends on T1 in S2, after exiting S2, f3b 
  has no more section dependency *)

  Elpi Print TC_solver "TC_solver.html" ".*elpi.[^a].*" ".*:.*[0-9]+".
End M7.

Reset M7.

Module M8.
  Class Classe (A: Type) (B: Type).

  Global Instance I (a b c d: Type): Classe a a -> Classe b c. Admitted.

  Elpi AddAllInstances.
  
  Print HintDb typeclass_instances.

  Elpi Query TC_solver lp:{{
    get-inst-prio {{:gref I}} X, !,
    std.assert! (X = 3) "CIAO".
  }}.
End M8.
