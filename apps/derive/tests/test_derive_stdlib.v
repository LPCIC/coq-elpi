(* Some standard data types using different features *)
From Coq Require Uint63.
From Coq Require Floats.

Module Coverage.

Inductive empty := .

Inductive unit := tt.

Inductive peano := Zero | Succ (n : peano).

Inductive option A := None | Some (_ : A).

Inductive pair A B := Comma (a : A) (b : B).

Inductive seq A := Nil | Cons (x : A) (xs : seq A).

Inductive box_peano := Box (n:peano).

Inductive rose (A : Type) := Leaf (a : A) | Node (sib : seq (rose A)).

Inductive rose_p (A B : Type) := Leafp (p : pair A B) | Nodep (sib : pair (rose_p A B) (rose_p A B)).

Inductive rose_o (A : Type) := Leafo (a : A) | Nodeo (x: pair (rose A) (rose A)) (sib : option (seq (rose A))).

Inductive nest A := NilN | ConsN (x : A) (xs : nest (pair A A)).

Fail Inductive bush A := BNil | BCons (x : A) (xs : bush (bush A)).

Inductive w A := via (f : A -> w A).

Inductive vect A : peano -> Type := VNil : vect A Zero | VCons (x : A) n (xs : vect A n) : vect A (Succ n).

Inductive dyn := box (T : Type) (t : T).

Inductive zeta Sender (Receiver := Sender) := Envelope (a : Sender) (ReplyTo := a) (c : Receiver).

Inductive beta (A : (fun x : Type => x) Type) := Redex (a : (fun x : Type => x) A).

Inductive iota := Why n (a : match n in peano return Type with Zero => peano | Succ _ => unit end).

Inductive large :=
| K1 (_ : unit) 
| K2 (_ : unit) (_ : unit) 
| K3 (_ : unit) (_ : unit) (_ : unit) 
| K4 (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K5 (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K6 (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K7 (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K8 (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K9 (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K10(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K11(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K12(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K13(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K14(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K15(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K16(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K17(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K18(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K19(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K20(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K21(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K22(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K23(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K24(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K25(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) 
| K26(_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit) (_ : unit).

Inductive prim_int := PI (i : Uint63.int).
Inductive prim_float := PF (f : PrimFloat.float).

Record fo_record := { f1 : peano; f2 : unit; }.

Record pa_record A := { f3 : peano; f4 : A; }.

Set Primitive Projections.
Record pr_record A := { pf3 : peano; pf4 : A; }.
Unset Primitive Projections.

Record dep_record := { f5 : peano; f6 : vect unit f5; }.

Variant enum := E1 | E2 | E3.

Definition is_zero (n:peano) : bool := 
  match n with 
  | Zero => true 
  | _ => false
  end.

Record sigma_bool := { depn : peano; depeq : is_zero depn = true }.

Fixpoint is_leq (n m:peano) : bool := 
  match n, m with 
  | Zero, _ => true 
  | Succ n, Succ m => is_leq n m
  | _, _ => false
  end.

Inductive ord (p : peano) := mkOrd (n : peano) (l : is_leq n p = true).

Inductive ord2 (p : peano) := mkOrd2 (o1 o2 : ord p).

Inductive val := V (p : peano) (o : ord p).

(* to make the coverage cound correct
Inductive eq := ...
Inductive bool := ...
we don't have a copy here because some DBs have special rules*)

Definition alias := seq peano.

End Coverage.
