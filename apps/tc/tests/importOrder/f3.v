From elpi.apps.tc.tests.importOrder Require Import f1.

Elpi Command SameOrderImport.
Elpi Accumulate Db tc.db.
Elpi Accumulate lp:{{
  main _ :-
    std.findall (instance _ _ _) RulesInst,
    coq.TC.db DB_tc-inst,
    std.map RulesInst (x\inst\ instance _Path inst _TC = x) Rules,
    std.map DB_tc-inst (x\inst\ tc-instance inst _ = x) Rules2,
    std.assert! (Rules = Rules2) "Error in import order [Elpi = Coq]".
}}.

Module M1.
  From elpi.apps.tc.tests.importOrder Require Import f2a.
  From elpi.apps.tc.tests.importOrder Require Import f2b.

  Elpi Override TC TC_solver All.

  Elpi SameOrderImport.
End M1.
Reset M1.

Module M2.
  From elpi.apps.tc.tests.importOrder Require Import f2b.
  From elpi.apps.tc.tests.importOrder Require Import f2a.

  Elpi Override TC TC_solver All.
  
  (* TODO: @gares @FissoreD why it fails *)
  Fail Elpi SameOrderImport.
End M2.
Reset M2.

Module M3.
  Global Instance f3a : A nat := {f x := x}.
  Global Instance f3b : A nat := {f x := x}.
  Global Instance f3c : A nat := {f x := x}.
  Elpi AddAllInstances.
  Elpi SameOrderImport.

  Section S1.
    Global Instance f3d : A nat := {f x := x}.
    Global Instance f3e : A nat := {f x := x}.
    Global Instance f3f : A nat := {f x := x}.
    Elpi AddAllInstances.
    Elpi SameOrderImport.
  MySectionEnd.
  Elpi SameOrderImport.

  Section S2.
    Context (T : Set).
    Global Instance f3g : A T := {f x := x}.
    Elpi AddAllInstances.
    Elpi SameOrderImport.
  MySectionEnd.
  Elpi SameOrderImport.

  Section S3.
    Context (T : Set).
    Global Instance f3g2 : A (T: Set) := {f x := x}.

    Global Instance f3h T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.

    Global Instance f3g3 : A (T: Set) := {f x := x}.
    Global Instance f3g4 : A (T: Set) | 10 := {f x := x}.

    Elpi AddAllInstances.
    (* TODO: order should be corrected *)
    Fail Elpi SameOrderImport.
  MySectionEnd.

  Fail Elpi SameOrderImport.
End M3.

Reset M3.

Module M4.
  From elpi.apps.tc.tests.importOrder Require Import f2b.
  Elpi SameOrderImport.

  Global Instance f3a' T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.
  Module M4'.
    From elpi.apps.tc.tests.importOrder Require Import f2a.
    Fail Elpi SameOrderImport.

    Global Instance f3a : A nat := {f x := x}.
    Elpi AddInstances f3a.

    Section S1.
      Global Instance f3b : A nat := {f x := x}.
      Elpi AddInstances f3b.
      Section S1'.
        Global Instance f3c : A nat := {f x := x}.
        Elpi AddInstances f3c.
      MySectionEnd.
    MySectionEnd.

    Fail Elpi SameOrderImport.

    Section S2.
      Global Instance f3h T1 T2 `(A T1, A T2) : A (T1 * T2) := {f x := x}.
      Elpi AddInstances f3h.
    MySectionEnd.
  End M4'.
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
  Fail Elpi SameOrderImport.
End M5.

Reset M5.

Module M6.
  Global Instance f3a : A nat := {f x := x}.
  Global Instance f3b : A nat := {f x := x}.
  Global Instance f3c : A nat := {f x := x}.
  
  Section S1.
    Global Instance f3d : A nat := {f x := x}.
    Global Instance f3e : A nat := {f x := x}.
    Global Instance f3f : A nat := {f x := x}.
  MySectionEnd.
  Elpi AddAllInstances.

  Elpi SameOrderImport.
End M6.

Reset M6.

Module M7.
  Section S1.
    Context (T : Set).
    Global Instance f3a : A T := {f x := x}.
    Elpi AddInstances f3a.
    Section S2.
      Context (T1 : Set).
      Global Instance f3b : A T1 := {f x := x}.
      Elpi AddInstances f3b.
    MySectionEnd.
   Elpi SameOrderImport.
  MySectionEnd.
  Fail Elpi SameOrderImport.
End M7.

Reset M7.

Module M8.
  Class Classe (A: Type) (B: Type).
  Elpi AddClasses Classe.

  Global Instance I (a b c d: Type): Classe a a -> Classe b c. Admitted.

  Elpi AddAllInstances.
  Elpi SameOrderImport.
End M8.
