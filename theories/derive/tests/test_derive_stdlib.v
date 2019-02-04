(* Some standard data types using different features *)

Module Coverage.

Inductive empty := .

Inductive unit := tt.

Inductive peano := Zero | Succ (n : peano).

Inductive option A := None | Some (_ : A).

Inductive pair A B := Comma (a : A) (b : B).

Inductive seq A := Nil | Cons (x : A) (xs : seq A).

Inductive rose (A : Type) := Leaf | Node (sib : seq (rose A)).

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
End Coverage.
