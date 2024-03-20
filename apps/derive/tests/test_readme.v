From elpi.apps Require Import derive.std.

Module example1.
  derive Inductive peano := Zero | Succ (p : peano).

  Print peano.
  (* Inductive peano : Set :=  Zero : peano | Succ : peano -> peano *)

  Eval compute in peano_eqb Zero (Succ Zero).
  (* = false : bool *)

  Check peano_eqb_OK.
  (* peano_eqb_OK : forall x1 x2 : peano, reflect (x1 = x2) (eqb x1 x2) *)
End example1.

Module example2.
  #[module]
  derive Inductive peano := Zero | Succ (p : peano).

  Print peano.
  (* Notation peano := peano.peano *)

  Print peano.peano.
  (* Inductive peano : Set :=  Zero : peano | Succ : peano -> peano *)

  Eval compute in peano.eqb Zero (Succ Zero).
  (* = false : bool *)

  Check peano.eqb_OK.
  (* peano.eqb_OK : forall x1 x2 : peano, reflect (x1 = x2) (eqb x1 x2) *)
End example2.

Module example3.
  #[module="Peano"]
  derive Inductive peano := Zero | Succ (p : peano).

  Print peano.
  (* Notation peano := Peano.peano *)

  Print Peano.peano.
  (* Inductive peano : Set :=  Zero : peano | Succ : peano -> peano *)

  Eval compute in Peano.eqb Zero (Succ Zero).
  (* = false : bool *)

  Check Peano.eqb_OK.
  (* Peano.eqb_OK : forall x1 x2 : peano, reflect (x1 = x2) (eqb x1 x2) *)
End example3.

Module example4.
  #[module="Peano",prefix="Peano_"]
  derive Inductive peano := Zero | Succ (p : peano).

  Print peano.
  (* Notation Peano := Peano.peano *)

  Print Peano.peano.
  (* Inductive peano : Set :=  Zero : peano | Succ : peano -> peano *)

  Print Module Peano.

  Eval compute in Peano.Peano_eqb Zero (Succ Zero).
  (* = false : bool *)

  Check Peano.Peano_eqb_OK.
  (* Peano.Peano_eqb_OK : forall x1 x2 : peano, reflect (x1 = x2) (eqb x1 x2) *)
End example4.

Module example5.
  #[prefix=""]
  derive Inductive peano := Zero | Succ (p : peano).

  Print peano.
  (* Inductive peano : Set :=  Zero : peano | Succ : peano -> peano *)

  Eval compute in eqb Zero (Succ Zero).
  (* = false : bool *)

  Check eqb_OK.
  (* eqb_OK : forall x1 x2 : peano, reflect (x1 = x2) (eqb x1 x2) *)
End example5.

Module example6.
  #[module=Peano,no_alias]
    derive Inductive peano := Zero | Succ (p : peano).

  Fail Print peano.

  Print Peano.peano.
  (* Inductive peano : Set := Peano.Zero : peano | Peano.Succ : peano -> peano *)

  Eval compute in Peano.eqb Peano.Zero (Peano.Succ Peano.Zero).
  (* = false : bool *)

  Check Peano.eqb_OK.
  (* Peano.eqb_OK : forall x1 x2 : peano, reflect (x1 = x2) (eqb x1 x2) *)
End example6.

Fail #[no_alias]
derive Inductive peano := Zero | Succ (p : peano).
