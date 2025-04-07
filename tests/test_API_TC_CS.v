From elpi Require Import elpi.

Elpi Command TCCS.

(****** TC **********************************)

Require Import Classes.RelationClasses.

Axiom T : Type.
Axiom R : T -> T -> Prop.
Axiom Rr : forall x : T, R x x.

Definition myi : Reflexive R.
Proof.
exact Rr.
Defined.

Fail Example ex : Reflexive R := _.

Module TCLocal.
  Elpi Query lp:{{ coq.locate "myi" GR, @local! => coq.TC.declare-instance GR 10. }}.
  Succeed Example ex : Reflexive R := _.
End TCLocal.

Module TCExport.
  Fail Example ex : Reflexive R := _.
  Module Mod.
    Elpi Query lp:{{ coq.locate "myi" GR, coq.TC.declare-instance GR 10. }}.
  End Mod.
  Fail Example ex : Reflexive R := _.
  Import Mod.
  Check (_ : Reflexive R).
  Succeed Example ex : Reflexive R := _.
End TCExport.

Module TCGlobal.
  Elpi Query lp:{{ coq.locate "myi" GR, @global! => coq.TC.declare-instance GR 10. }}.
End TCGlobal.
Succeed Example ex : Reflexive R := _.


Elpi Query lp:{{coq.TC.db L}}.
Elpi Query lp:{{coq.locate "RewriteRelation" GR, coq.TC.db-for GR L}}.
Elpi Query lp:{{coq.locate "RewriteRelation" GR, coq.TC.class? GR}}.
Elpi Query lp:{{coq.locate "True" GR, not(coq.TC.class? GR)}}.

Module hint_instance.
  Class Test : Prop := {}.

  Instance instance_c : Test := Build_Test.
  Instance instance_g : Test | 4 := Build_Test.

  Definition hint_c : Test := Build_Test.
  Definition hint_g : Test := Build_Test.

  Hint Resolve hint_c : typeclass_instances.
  Hint Resolve hint_g | 5 : typeclass_instances.

  Elpi Command test.
  Elpi Accumulate lp:{{
    pred expected o:tc-instance.
    expected (tc-instance {{:gref hint_c}} 0).
    expected (tc-instance {{:gref instance_c}} 0).
    expected (tc-instance {{:gref instance_g}} 4).
    % Note: the priority of hint_g is 5, the one given in the hint resolve
    expected (tc-instance {{:gref hint_g}} 5).
  }}.
  Elpi Query lp:{{ 
    coq.TC.db-for {{:gref Test}} L,
    std.length L 4,               % there are 4 instances for Test
    std.findall (expected _) Exp, % get the expected prio
    (Check: (pred i:prop)) = (x\ sigma Exp\ x = expected Exp, std.mem L Exp),
    std.forall Exp Check.         % check each instance has the expected priority
  }}.

End hint_instance.

Axiom C : Type -> Type.

Elpi Query lp:{{ coq.TC.declare-class {{:gref C }} }}.

Axiom c : C nat.

#[local] Instance foox : C nat := c.

(****** CS **********************************)

Structure eq := mk_eq { carrier : Type; eq_op : carrier -> carrier -> bool; _ : nat }.

Axiom W : Type.
Axiom Z : W -> W -> bool.
Axiom t : W.

Definition myc : eq := mk_eq W Z 3.

Fail Check (eq_op _ t t).

Elpi Query lp:{{coq.locate "myc" GR, coq.CS.declare-instance GR.}}.

Check (eq_op _ t t).

Elpi Query lp:{{ coq.CS.db L }}.

Elpi Query lp:{{
  coq.locate "eq" (indt I),
  coq.env.projections I [some P1, some P2, none],
  coq.locate "carrier" (const P1),
  coq.locate "eq_op" (const P2)
}}.

Axiom W1 : Type.
Axiom Z1 : W1 -> W1 -> bool.
Axiom t1 : W1.

Definition myc1 : eq := mk_eq W1 Z1 3.

Section CStest.
Elpi Query lp:{{ coq.locate "myc1" GR, @local! => coq.CS.declare-instance GR. }}.

Check (eq_op _ t1 t1).

Elpi Query lp:{{ coq.locate "eq_op" P, coq.CS.db-for P _ [_,_] }}.

Elpi Query lp:{{ coq.locate "W" W, coq.CS.db-for _ (cs-gref W) [_] }}.

Elpi Query lp:{{ coq.locate "eq_op" P, coq.locate "Z1" W, coq.CS.db-for P (cs-gref W) L, coq.say L, L = [cs-instance P (cs-gref W) {{:gref myc1}}] }}.

Elpi Query lp:{{ coq.locate "eq_op" P, coq.locate "nat" W, coq.CS.db-for P (cs-gref W) [] }}.


End CStest.

Fail Check (eq_op _ t1 t1).


(****** Coercions **********************************)

Axiom C1 : Type.
Axiom C2 : Type.
Axiom c12 : C1 -> C2.
Axiom c1t : C1 -> Type.
Axiom c1f : C1 -> nat -> nat.

Elpi Query lp:{{
  coq.locate "c12" GR1,
  coq.locate "c1t"   GR2,
  coq.locate "c1f"   GR3,
  coq.locate "C1"    C1,
  % coq.locate "C2"    C2,
  (@global! => coq.coercion.declare (coercion GR1 _ _ _)),
  (@global! => coq.coercion.declare (coercion GR2 _ C1 sortclass)),
  (@global! => coq.coercion.declare (coercion GR3 _ C1 funclass)).
}}.

Check (fun x : C1 => (x : C2)).
Check (fun x : C1 => fun y : x => true).
Check (fun x : C1 => x 3).

Elpi Query lp:{{coq.coercion.db L}}.

Axiom C3 : nat -> Type.
Axiom nuc : forall x, C1 -> C3 x.

Set Warnings "-uniform-inheritance".
Elpi Query lp:{{ @reversible! => coq.coercion.declare (coercion {coq.locate "nuc"} _ _ _) }}.

About nuc.

