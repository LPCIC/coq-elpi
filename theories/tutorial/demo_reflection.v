Require Import Arith ZArith Psatz List.

Open Scope Z_scope.

Inductive lang := var (_ : nat) | add (_ _ : lang).

Fixpoint interp (op : Z -> Z -> Z) (l : list Z) (t : lang) : Z :=
  match t with
  | var v => nth v l 0
  | add x y => op (interp op l x) (interp op l y)
  end.

Fixpoint norm_aux t1 t2 : lang :=
  match t1 with
  | var x => add (var x) t2
  | add t t' => norm_aux t (norm_aux t' t2)
  end.

Fixpoint norm t :=
  match t with
  | var x => t
  | add t1 t2 => norm_aux t1 (norm t2)
  end.

Section assoc_reflection_proofs.

Variable op : Z -> Z -> Z.

Hypothesis op_assoc : forall a b c, op a (op b c) = op (op a b) c.

Lemma norm_aux_c l t1 t2 :
  interp op l (norm_aux t1 t2) = op (interp op l t1) (interp op l t2).
Proof.
revert t2; induction t1 as [i | t1 IH1 t2 IH2]; intros t3.
  now auto.
now simpl; rewrite IH1, IH2, op_assoc.
Qed.

Lemma norm_c l t :  interp op l t = interp op l (norm t).
Proof.
induction t as [i | t1 IH1 t2 IH2]; auto; simpl.
now rewrite IH2, norm_aux_c.
Qed.

Lemma norm_c2 l t1 t2 : norm t1 = norm t2 -> interp op l t1 = interp op l t2.
Proof. now intros nn; rewrite (norm_c _ t1), (norm_c _ t2); apply f_equal.  Qed.

End assoc_reflection_proofs.

Arguments norm_c2 {op}.

Example axpypzpt x y z t : (x + y) + (z + t) = x + (y + z) + t.
Proof.
change (interp Z.add (x::y::z::t::nil)(add (add (var 0) (var 1))
                                           (add (var 2) (var 3))) =
        interp Z.add (x::y::z::t::nil)
              (add (add (var 0) (add (var 1) (var 2))) (var 3))).
apply (norm_c2 Z.add_assoc).
reflexivity.
Qed.

From elpi Require Import elpi.

Elpi Tactic reify.
Elpi Accumulate lp:{{

pred mem o:term, o:term, o:term.
mem {{ lp:X :: lp:XS_ }} X {{0%nat}} :- !.
mem {{ _ :: lp:XS }} X {{S lp:N}} :- mem XS X N.

pred close o:term.
close {{ nil }} :- !.
close {{ _ :: lp:XS }} :- close XS.

pred quote i:term, i:term, o:term, o:term.
quote GR (app [GR, T1, T2]) {{ add lp:R1 lp:R2 }} L :- !,
  quote GR T1 R1 L,
  quote GR T2 R2 L.
quote _ T {{ var lp:R }} L :- mem L T R.

solve [trm Op] [goal Ctx P {{ lp:A = lp:B }} _] _ :-
  quote Op A AstA L,
  quote Op B AstB L,
  close L,
  !,
  Ty = {{ (interp lp:Op lp:L lp:AstA) = (interp lp:Op lp:L lp:AstB)}},
  P = {{ (fun x : lp:Ty => x) _ }}.

}}.
Elpi Typecheck.
Tactic Notation "reify_step" constr(x) := elpi reify (x).


Example axpypzpt2 (x : Z) : x = x.
Proof.
  reify_step Z.add.
  now apply (norm_c2 Z.add_assoc); compute.
Qed.

(* Now adding the reification phase. *)

Class Reify (op : Z -> Z -> Z) (t : lang) (l : list Z) (x : Z).

Instance addRf op x y l e1 e2 {_ : Reify op e1 l x} {_ : Reify op e2 l y} :
   Reify op (add e1 e2) l (op x y) | 1 := {}.

Class Nth (i : nat) (l : list Z) (e : Z).

Instance nth0 t l : Nth 0 (t :: l) t | 0 := {}.

Instance nthS i t l t'
   {_ : Nth i l t} : Nth (S i) (t' :: l) t | 2 := {}.

Instance varRf op e i l 
  {_ : Nth i l e} : Reify op (var i) l e | 100 := {}.

Class closed (l : list Z).

Instance closed0 : closed nil := {}.

Instance closed1 a l {_ : closed l} : closed (a :: l) := {}.

Definition reify_trigger op (expr : lang) (lvar : list Z) (term : Z)
 {_ : Reify op expr lvar term} `{closed lvar} := (lvar, expr).

Ltac reify_step_ltac op := time(
match goal with |- ?u = ?v =>
  match eval red in (reify_trigger op _ _ (op u v)) with
    (?a, add ?b ?c) => change (interp op a b = interp op a c)
  end
end).

Example axpypzpt23 x y z t : (x + y) + (z + t) = x + (y + z) + t.
Proof.
reify_step_ltac Z.add.
now apply (norm_c2 Z.add_assoc); compute.
Qed.

(* Now adding the commutative property to the operator. *)

Fixpoint lang_insert (x : nat) (t : lang) :=
  match t with
    add (var y) t' =>
      if (x <=? y)%nat then add (var x) (add (var y) t')
      else add (var y) (lang_insert x t')
  | var y =>
      if (x <=? y)%nat then add (var x) (var y)
      else add (var y) (var x)
  | _ => add (var x) t
  end.

Fixpoint lang_sort (t : lang) :=
  match t with
  | add (var x) t' => lang_insert x (lang_sort t')
  | _ => t
  end.

Section comm_reflection_proofs.

Variable op : Z -> Z -> Z.

Hypotheses (op_assoc : forall a b c, op a (op b c) = op (op a b) c)
  (op_comm : forall a b, op a b = op b a).

Lemma lang_insert_c l x t :
  interp op l (lang_insert x t) = interp op l (add (var x) t).
Proof.
induction t as [ j | [ j | t11 t12] _ t2 IH ]; simpl; auto;
  case (x <=? j)%nat; simpl; auto.
now rewrite IH; simpl; rewrite !op_assoc, (op_comm (_ x l 0)).
Qed.

Lemma lang_sort_c l t :
  interp op l (lang_sort t) = interp op l t.
Proof.
induction t as [ i | [ j | t11 t12] _ t2 IH]; auto.
now simpl; rewrite lang_insert_c; simpl; rewrite IH.
Qed.

Lemma lang_sort_c2 l t1 t2 :
  lang_sort (norm t1) = lang_sort (norm t2) -> interp op l t1 = interp op l t2.
Proof.
intros nn; rewrite (norm_c _ op_assoc _ t1), (norm_c _ op_assoc _ t2).
rewrite <- (lang_sort_c _ (norm t1)), <- (lang_sort_c _ (norm t2)).
now apply f_equal.
Qed.

End comm_reflection_proofs.

Arguments lang_sort_c2 {op}.

Example cxpypz x y z : x + y + z = z + x + y.
Proof.
reify_step Z.add.
apply (lang_sort_c2 Z.add_assoc Z.add_comm).
compute.
reflexivity.
Qed.

Example cxmymy x y : x * y * y = y * x * y.
Proof.
reify_step Z.mul.
apply (lang_sort_c2 Z.mul_assoc Z.mul_comm).
compute.
reflexivity.
Qed.

Class comm_monoid (op : Z -> Z -> Z) :=
  {op_assoc : forall x y z, op x (op y z) = op (op x y) z;
   op_comm : forall x y, op x y = op y x}.

Lemma lang_sort_c2' {op : Z -> Z -> Z} `{comm_monoid op} l t1 t2 :
  lang_sort (norm t1) = lang_sort (norm t2) ->
  interp op l t1 = interp op l t2.
Proof.
intros sn2; apply lang_sort_c2, sn2.
  apply op_assoc.
now apply op_comm.
Qed.

Example cxpypz2 x y z : x + y + z = z + x + y.
Proof.
reify_step Z.add.
Fail apply lang_sort_c2'.
Abort.

Instance add_comm_monoid : comm_monoid Z.add :=
  {op_assoc := Z.add_assoc; op_comm := Z.add_comm}.

Instance mul_comm_monoid : comm_monoid Z.mul :=
  {op_assoc := Z.mul_assoc; op_comm := Z.mul_comm}.

Example cxpypz2 x y z : x + y + z = z + x + y.
Proof.
reify_step Z.add.
now apply lang_sort_c2'.
Qed.

Example cxmymz2 x y z : x * y * z = z * x * y.
Proof.
reify_step Z.mul.
now apply lang_sort_c2'.
Qed.
