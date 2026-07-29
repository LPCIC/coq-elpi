(* Some standard data types using different features *)
From elpi Require elpi.
From Corelib Require PrimInt63 PrimFloat.
From elpi.apps.derive Require PrimStringEqb.

Module Coverage.

Inductive empty := .

Inductive mempty := with mempty' := .

Inductive unit := tt.

Inductive munit := mtt with munit' := mtt'.

Inductive peano := Zero | Succ (n : peano).

Inductive mpeano := mZero | mSucc (n : mpeano') with mpeano' := mZero' | mSucc' (n' : mpeano).

Inductive option A := None | Some (_ : A).

Inductive moption A := mNone | mSome (_ : A) with moption' A := mNone' | mSome' (_ : A).

Inductive pair A B := Comma (a : A) (b : B).

Inductive seq A := Nil | Cons (x : A) (xs : seq A).

Inductive box_peano := Box (n:peano).

Inductive rose (A : Type) := Leaf (a : A) | Node (sib : seq (rose A)).

Inductive rose_p (A B : Type) := Leafp (p : pair A B) | Nodep (sib : pair (rose_p A B) (rose_p A B)).

Inductive rose_o (A : Type) := Leafo (a : A) | Nodeo (x: pair (rose A) (rose A)) (sib : option (seq (rose A))).

Inductive mtree (A : Type) := mLeaf (a : A) | mNode (_ : mforest A) with mforest (A : Type) := mEnd | mTree (_ : mtree A) (_ : mforest A).

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

Inductive prim_int := PI (i : PrimInt63.int).
Inductive prim_float := PF (f : PrimFloat.float).
Inductive prim_string := PS (s : lib:elpi.pstring).

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

Record sigma_bool2 := { depn2 : peano; depeq2 : lib:elpi.is_true (is_zero depn2) }.

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

Module Mutual.

Module Tree.
Inductive tree : Type := node (f : forest)
with forest : Type := empty | cons (t : tree) (f : forest).
End Tree.

Module ParametrizedTree.
Inductive ptree (A : Type) : Type := pnode (x : A) (f : pforest A)
with pforest (A : Type) : Type := pempty | pcons (t : ptree A) (f : pforest A).
End ParametrizedTree.

Module Triple.
Inductive alpha : Type := alpha0 | alpha1 (b : beta)
with beta : Type := beta0 | beta1 (g : gamma)
with gamma : Type := gamma0 | gamma1 (a : alpha) (b : beta).
End Triple.

Module CyclicTriple.
Inductive alpha : Type := alpha_beta (b : beta)
with beta : Type := beta_gamma (g : gamma)
with gamma : Type := gamma_alpha (a : alpha) | gamma_done.
End CyclicTriple.

Module ParametrizedTriple.
Inductive palpha (A : Type) : Type :=
| palpha0
| palpha1 (x : A) (b : pbeta A)
with pbeta (A : Type) : Type :=
| pbeta0
| pbeta1 (g : pgamma A)
with pgamma (A : Type) : Type :=
| pgamma0
| pgamma1 (a : palpha A) (b : pbeta A).
End ParametrizedTriple.

Module NonRecursive.
Inductive color : Type := red | blue
with shape : Type := circle | square.
End NonRecursive.

Module Indexed.
Inductive itree (A : Type) : nat -> Type :=
| ileaf : A -> itree A 0
| inode : forall n, iforest A n -> itree A (S n)
with iforest (A : Type) : nat -> Type :=
| inil : iforest A 0
| icons : forall n, itree A n -> iforest A n -> iforest A (S n).
End Indexed.

Module Dependency.
Inductive a : Type := ka
with b : Type := kb.
Inductive c : Type := kc : a -> kb = kb -> c.
End Dependency.

End Mutual.
