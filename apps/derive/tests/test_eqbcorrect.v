From elpi.apps Require Import derive.eqbcorrect.
From elpi.apps.derive Require Import param1. (* FIXME, the clause is in param1 *)
From elpi.apps.derive.tests Require Import test_derive_stdlib test_eqType_ast test_tag test_fields test_eqb test_induction 
                                           test_param1 test_param1_trivial test_param1_functor.
Import test_derive_stdlib.Coverage 
       test_eqType_ast.Coverage 
       test_tag.Coverage 
       test_fields.Coverage
       test_eqb.Coverage 
       test_induction.Coverage 
       test_param1.Coverage 
       test_param1_trivial.Coverage 
       test_param1_functor.Coverage.
    
Module Coverage.

(* Elpi Trace (* "derive.eqbcorrect.*" "derive.param1.functor.*" "correct-lemma-for" *) "param1-functor-for". *)
Elpi derive.eqbcorrect empty. 
Elpi derive.eqbcorrect unit. 
Elpi derive.eqbcorrect peano.
Elpi derive.eqbcorrect option.
Elpi derive.eqbcorrect pair.
Elpi derive.eqbcorrect seq.
Elpi derive.eqbcorrect box_peano.
Elpi derive.eqbcorrect rose.
Elpi derive.eqbcorrect rose_p.
Elpi derive.eqbcorrect rose_o.
Fail Elpi derive.eqbcorrect nest. (* Maybe fixable *)
Fail Elpi derive.eqbcorrect w.    (* Not fixable *)
Fail Elpi derive.eqbcorrect vect. (* Can be done *)
Fail Elpi derive.eqbcorrect dyn.  (* Not Fixable *)
Fail Elpi derive.eqbcorrect zeta. (* FIXME *)
Elpi derive.eqbcorrect beta.
Fail Elpi derive.eqbcorrect iota.
(*
Elpi derive.eqbcorrect large.
*)
Fail Elpi derive.eqbcorrect prim_int.
Fail Elpi derive.eqbcorrect prim_float. (* Can not work, we don't have a syntaxtic test *)
Elpi derive.eqbcorrect fo_record.
Elpi derive.eqbcorrect pa_record.
Elpi derive.eqbcorrect pr_record.   
Fail Elpi derive.eqbcorrect dep_record.
Elpi derive.eqbcorrect enum.
Fail Elpi derive.eqbcorrect eq.
Elpi derive.eqbcorrect bool.
Elpi derive.eqbcorrect sigma_bool.
Elpi derive.eqbcorrect ord.
Elpi derive.eqbcorrect ord2.
Elpi derive.eqbcorrect val.

End Coverage.

Import Coverage.

Check peano_eqb_correct : forall n m, peano_eqb n m = true -> n = m.
Check peano_eqb_refl : forall n, peano_eqb n n = true.

Check ord_eqb_correct : forall n, eqb_correct (ord_eqb n n).
Check ord_eqb_refl : forall n, eqb_reflexive (ord_eqb n n).

Check ord2_eqb_correct : forall n, eqb_correct (ord2_eqb n n).
Check ord2_eqb_refl : forall n, eqb_reflexive (ord2_eqb n n).

Check val_eqb_correct : eqb_correct val_eqb.
Check val_eqb_refl : eqb_reflexive val_eqb.

(*
Import PArith.

Import ssreflect ssrfun ssrbool.
Require Import JMeq.

Module UseJMeq.

Definition vect_fields_t (A:Type) (n:peano) (p:positive) : Type := 
  match p with 
  | 1 => unit 
  | 2 => (A * { m : peano & vect A m })%type
  | _ => unit
  end.

Definition vect_fields (A:Type) (n:peano) (v:vect A n) : vect_fields_t A n (vect_tag A n v) := 
  match v as v' in vect _ n return vect_fields_t A n (vect_tag A n v') with 
  | VNil _ => tt 
  | VCons _ a m v' => (a, existT _ m v')
  end.



Definition vect_construct_t (A:Type) (n:peano) (t:positive) : vect_fields_t A n t -> Type :=
  match t with
  | 1 => fun _ => vect A Zero
  | 2 => fun f => vect A (Succ (projT1 f.2))
  | _ => fun _ => unit
  end.

Definition vect_construct (A:Type) (n:peano) (t:positive) : 
  forall (f: vect_fields_t A n t), vect_construct_t A n t f :=
 match t with
 | 1 => fun _ => VNil A
 | 2 => fun f =>
    let a := f.1 in
    let f := f.2 in
    let m := projT1 f in
    let v' := projT2 f in
    VCons A a m v'
 | _ => fun _ => tt
 end.

Lemma vect_construct_tP (A:Type) (n:peano) (v : vect A n):
  vect_construct_t A n (vect_tag A n v) (vect_fields A n v) = vect A n.
Proof. by case: v. Qed.

Lemma vect_constructP (A:Type) (n:peano) (v : vect A n):
  JMeq (vect_construct A n (vect_tag A n v) (vect_fields A n v)) v.
Proof. case: v => *; apply JMeq_refl. Qed.

Definition vect_eqb_fields (A A':Type) (eqA:A->A'->bool) (n n':peano) 
  (rec : forall i i', vect A i -> vect A' i' -> bool) 
  (p:positive) : 
     vect_fields_t A n p ->  vect_fields_t A' n' p -> bool := 
match p with
| 1 => fun _ _ => true
| 2 => fun (f: vect_fields_t A n 2) (f':vect_fields_t A' n' 2) => 
      eqA f.1 f'.1 && 
      let f := f.2 in let f' := f'.2 in
      let m := projT1 f in let m' := projT1 f' in
      peano_eqb m m' &&  
      let v := projT2 f in let v' := projT2 f' in
      rec m m' v v' 
| _ => fun _ _ => true
end.

Definition eqb_body := 
fun (A' : Type) (tag' : A' -> positive) (fields_t fields_t' : positive -> Type)
  (fields' : forall a : A', fields_t' (tag' a))
  (eqb_fields : forall p : positive, (fields_t p -> fields_t' p -> bool)) 
  (t1 : positive)
  (f1 : fields_t t1) (x2 : A') =>
let t2 := tag' x2 in
match Pos.eq_dec t2 t1 with
| left heq => let f2 := fields' x2 in eqb_fields t1 f1 (eq_rect t2 fields_t' f2 t1 heq)
| right _ => false
end.
       
Definition eqb_fields_correct_on {A : Type} 
  [tag : A -> positive] [fields_t : positive -> Type] [construct_t : forall t:positive, fields_t t -> Type] :=
  fun (fields : forall a : A, fields_t (tag a))
      (construct : forall (t : positive) (f:fields_t t), construct_t t f) 
      (eqb_fields : forall t : positive, eq_test (fields_t t)) (a : A) =>
     forall f : fields_t (tag a), eqb_fields (tag a) (fields a) f -> JMeq a (construct (tag a) f).

Lemma eqb_body_correct {A : Type} [tag : A -> positive] [fields_t : positive -> Type]
  [fields : forall a : A, fields_t (tag a)]
  [construct_t : forall t:positive, fields_t t -> Type] 
  [construct : forall (t : positive) (f:fields_t t), construct_t t f] :
  (forall a : A, construct_t (tag a) (fields a) = A) ->
  (forall a : A, JMeq (construct (tag a) (fields a)) a) ->
  forall (eqb_fields : forall t : positive, eq_test (fields_t t))
         (a1 : A),
   eqb_fields_correct_on (tag:=tag) (fields_t:=fields_t) fields construct eqb_fields a1 ->
   forall a2 : A,
     eqb_body A tag fields_t fields_t fields eqb_fields (tag a1) (fields a1) a2 -> a1 = a2.
Proof.
  move=> construct_tP constructP eqb_fields a1 hf a2 hb.
  apply JMeq_eq.
  apply: JMeq_trans (constructP a2); move: hb; rewrite /eqb_body.
  case: Pos.eq_dec => // heq.
  move: (tag a2) heq (fields a2) => t2 ?; subst t2 => f2 /=; apply hf.
Qed.

Section S.
Context  (A A':Type) (eqA:A->A'->bool).

Fixpoint vect_eqb (n n':peano) (v:vect A n) (v':vect A' n') := 
  match v with 
  | VNil _ => 
    eqb_body (vect A' n') (vect_tag A' n') (vect_fields_t A Zero) (vect_fields_t A' n')
     (vect_fields A' n') 
     (vect_eqb_fields A A' eqA Zero n' vect_eqb) 1 tt v'
  | VCons _ a m v => 
    eqb_body (vect A' n') (vect_tag A' n') (vect_fields_t A (Succ m)) (vect_fields_t A' n')
     (vect_fields A' n') 
     (vect_eqb_fields A A' eqA (Succ m) n' vect_eqb)
     2 (a, existT _ m v) v'
  end.

End S.

Lemma vect_eqb_correct (A:Type) (eqA:A->A->bool) (heqA: eqb_correct eqA) (n : peano) (v : vect A n) :
  eqb_correct_on (vect_eqb A A eqA n n) v.
pose TA := fun n (_:is_peano n) (v:vect A n) => eqb_correct_on (vect_eqb A A eqA n n) v.
pose (T := fun (a:A) => True). 
apply: (vect_induction _ T TA _ _ n (is_peano_witness n) v); rewrite /TA /T => {TA T}.
+ apply: (@eqb_body_correct (vect A Zero) 
             (vect_tag A Zero) 
             (vect_fields_t A Zero) (vect_fields A Zero) 
             (vect_construct_t A Zero) (vect_construct A Zero) 
             (@vect_construct_tP A Zero)
             (@vect_constructP A Zero)
             (vect_eqb_fields A A eqA Zero Zero (vect_eqb A A eqA)) 
             (VNil A) _).
  rewrite /eqb_fields_correct_on /= => f _; apply JMeq_refl.
+ move=> {n v} a heqa m is_p_m v hrec.
  apply: (@eqb_body_correct (vect A (Succ m)) 
             (vect_tag A (Succ m)) 
             (vect_fields_t A (Succ m)) (vect_fields A (Succ m)) 
             (vect_construct_t A (Succ m)) (vect_construct A (Succ m)) 
             (@vect_construct_tP A (Succ m))
             (@vect_constructP A (Succ m))
             (vect_eqb_fields A A eqA (Succ m) (Succ m) (vect_eqb A A eqA)) 
             (VCons A a m v) _).
   rewrite /eqb_fields_correct_on /= => -[a' [m' v']] /= /andP [] /heqA <- /andP [] /peano_eqb_correct ?.
   by subst m' => /hrec <-. (*
 + by apply is_vect_witness.
Qed.
*)
Admitted.

End UseJMeq.

Module UseEqRect.

Definition vect_fields_t (A:Type) (n:peano) (p:positive) : Type := 
  match p with 
  | 1 => vect A Zero = vect A n  (* We add the forced equality at the end *)
  | 2 => (A * { m : peano & vect A m * (vect A (Succ m) = vect A n) })%type
  | _ => unit
  end.

Definition vect_fields (A:Type) (n:peano) (v:vect A n) : vect_fields_t A n (vect_tag A n v) := 
  match v as v' in vect _ n return vect_fields_t A n (vect_tag A n v') with 
  | VNil _ => eq_refl
  | VCons _ a m v' => (a, existT _ m (v', eq_refl))
  end.

Definition vect_construct (A:Type) (n:peano) (t:positive) : vect_fields_t A n t -> Datatypes.option (vect A n) := 
  match t as t' return vect_fields_t A n t' -> Datatypes.option (vect A n) with
  | 1 => fun (heq: vect A Zero = vect A n) => 
     Datatypes.Some (eq_rect (vect A Zero) id (VNil A) (vect A n) heq)
  | 2 => fun (f: vect_fields_t A n 2) => 
           let a := f.1 in
           let f := f.2 in
           let m := projT1 f in
           let f := projT2 f in
           let v' := f.1 in
           let heq := f.2 in
           Datatypes.Some (eq_rect (vect A (Succ m)) id (VCons A a m v') (vect A n) heq) 
  | _ => fun _ => Datatypes.None 
  end.

Definition vect_eqb_fields (A A':Type) (eqA:A->A'->bool) (n n':peano) 
  (rec : forall i i', vect A i -> vect A' i' -> bool) 
  (p:positive) : 
     vect_fields_t A n p ->  vect_fields_t A' n' p -> bool := 
match p with
| 1 => fun _ _ => true
| 2 => fun (f:  vect_fields_t A n 2) (f':vect_fields_t A' n' 2) => 
      eqA f.1 f'.1 && 
      let f := f.2 in let f' := f'.2 in
      let m := projT1 f in let m' := projT1 f' in
      peano_eqb m m' &&  
      let f := (projT2 f) in let f' := (projT2 f') in
      rec m m' f.1 f'.1 
| _ => fun _ _ => true
end.

Definition eqb_body := 
fun (A' : Type) (tag' : A' -> positive) (fields_t fields_t' : positive -> Type)
  (fields' : forall a : A', fields_t' (tag' a))
  (eqb_fields : forall p : positive, (fields_t p -> fields_t' p -> bool)) 
  (t1 : positive)
  (f1 : fields_t t1) (x2 : A') =>
let t2 := tag' x2 in
match Pos.eq_dec t2 t1 with
| left heq => let f2 := fields' x2 in eqb_fields t1 f1 (eq_rect t2 fields_t' f2 t1 heq)
| right _ => false
end.

(*       
Definition eq_test (fields_t fields_t' : positive -> Type) (t:positive) := 
   fields_t t -> fields_t' t -> bool.
*)
(*
Definition eqb_fields_correct_on := 
fun (A A': Type) (tag : A -> positive) (fields_t fields_t' : positive -> Type)
  (fields : forall a : A, fields_t (tag a))
  (construct' : forall t : positive, fields_t' t -> Datatypes.option A')
  (eqb_fields : forall t : positive, eq_test fields_t fields_t' t) (a : A) =>
forall (f : fields_t' (tag a)) (H:A' = A),
eqb_fields (tag a) (fields a) f -> 
  Datatypes.Some a = 
    eq_rect A' Datatypes.option (construct' (tag a) f) A H.
*)

Lemma eqb_body_correct :
forall {A : Type} [tag : A -> positive] [fields_t : positive -> Type] [fields : forall a : A, fields_t (tag a)]
  [construct : forall t : positive, fields_t t -> Datatypes.option A],
(forall a : A, construct (tag a) (fields a) = Datatypes.Some a) ->
forall (eqb_fields : forall t : positive, eq_test (fields_t t)) (a1 : A),
eqb_fields_correct_on (tag:=tag) (fields_t:=fields_t) fields construct eqb_fields a1 ->
forall a2 : A,
  @eqb_body A tag fields_t fields_t fields eqb_fields (tag a1) (fields a1) a2 -> a1 = a2.
Proof.
  move=> A tag fields_t fields construct constructP eqb_fields a1 hf a2 hb.
  suff : Datatypes.Some a1 = Datatypes.Some a2 by move=> [->].
  rewrite -(constructP a2); move: hb; rewrite /eqb_body.
  case: Pos.eq_dec => // heq.
  move: (tag a2) heq (fields a2) => t2 ?; subst t2 => f2 /=; apply hf.
Qed.

Lemma eq_rect_can (A:Type) (v: A) (heq : A = A) : v = eq_rect A id v A heq.
Proof.
  have: forall (B:Type) (v1:A) (v2:B) (heq: B = A),
    JMeq v1 v2 ->
    v1 = eq_rect B id v2 A heq.
  + by move=> B v1 v2 heq'; subst B => /=; apply JMeq_eq.
  + apply;apply JMeq_refl.
Qed.

Section S.
Context  (A A':Type) (eqA:A->A'->bool).

Fixpoint vect_eqb (n n':peano) (v:vect A n) (v':vect A' n') := 
  match v with 
  | VNil _ => 
    eqb_body (vect A' n') (vect_tag A' n') (vect_fields_t A Zero) (vect_fields_t A' n')
     (vect_fields A' n') 
     (vect_eqb_fields A A' eqA Zero n' vect_eqb) 1 erefl v'
  | VCons _ a m v => 
    eqb_body (vect A' n') (vect_tag A' n') (vect_fields_t A (Succ m)) (vect_fields_t A' n')
     (vect_fields A' n') 
     (vect_eqb_fields A A' eqA (Succ m) n' vect_eqb)
     2 (a, existT _ m (v, erefl)) v'
  end.

End S.

Lemma vect_constructP (A:Type) n (a : vect A n):
  vect_construct A n (vect_tag A n a) (vect_fields A n a) = Datatypes.Some a.
Proof. by case: a. Qed.

Lemma vect_eqb_correct (A:Type) (eqA:A->A->bool) (heqA: eqb_correct eqA) (n : peano) (v : vect A n) :
  eqb_correct_on (vect_eqb A A eqA n n) v.
pose TA := fun n (_:is_peano n) (v:vect A n) => eqb_correct_on (vect_eqb A A eqA n n) v.
pose (T := fun (a:A) => True). 
apply: (vect_induction _ T TA _ _ n (is_peano_witness n) v); rewrite /TA /T => {TA T}.
+ apply: (@eqb_body_correct (vect A Zero) 
             (vect_tag A Zero) 
             (vect_fields_t A Zero) (vect_fields A Zero) 
             (vect_construct A Zero) 
             (@vect_constructP A Zero)
             (vect_eqb_fields A A eqA Zero Zero (vect_eqb A A eqA)) 
             (VNil A) _).
  by move=> f _; rewrite /= -eq_rect_can.
+ move=> {n v} a heqa m is_p_m v hrec.
  apply: (@eqb_body_correct (vect A (Succ m)) 
             (vect_tag A (Succ m)) 
             (vect_fields_t A (Succ m)) (vect_fields A (Succ m)) 
             (vect_construct A (Succ m)) 
             (@vect_constructP A (Succ m))
             (vect_eqb_fields A A eqA (Succ m) (Succ m) (vect_eqb A A eqA)) 
             (VCons A a m v) _).
   rewrite /eqb_fields_correct_on /= => -[a' [m' v']] /= /andP [] /heqA <- /andP [] /peano_eqb_correct ?.
   by subst m' => /hrec <-; rewrite -eq_rect_can.
(* + by apply is_vect_witness.
Qed.
*)
Admitted.

End UseEqRect.

Require Import Eqdep_dec.

Module UseEqRect_SB.

 
From elpi.apps.derive.tests Require Import test_param1_trivial.
Import test_param1_trivial.Coverage.
(*
About is_bool_trivial.

Lemma sigma_bool_eqb_correct (sb:sigma_bool) : 
  eqb_correct_on sigma_bool_eqb sb.
Proof.
pose P := eqb_correct_on sigma_bool_eqb.
apply: (@sigma_bool_induction P).
+ move=> {sb} b isb hb _ sb /=.
  apply: (@eqb_body_correct sigma_bool
           sigma_bool_tag
           sigma_bool_fields_t sigma_bool_fields 
           sigma_bool_construct
           sigma_bool_constructP
           (sigma_bool_eqb_fields (fun=> xpredT))
           {| depn := b; depeq := hb |} _).
  rewrite /eqb_fields_correct_on /= => -[b' hb'] /andP [] /= /peano_eqb_correct ? _.
  subst b'. 
  (* Now we rewrite UIP *)
  rewrite (@UIP_dec _ Bool.bool_dec _ _ hb hb').
  done.
+ clear P.
  case: sb => p1 p2.
  eapply (@is_Build_sigma_bool _ (is_peano_witness p1)).

  have is_eq_witness A (PA : A -> Type) (x y :A) (px: PA x) (py : PA y)
      (eq_xy : x = y) (eq_pxpy : py = @eq_rect A x PA px y eq_xy)
    : is_eq A PA x px y py eq_xy.
    destruct eq_xy.
    simpl in eq_pxpy.
    subst.
    constructor.
  eapply is_eq_witness.
  case: (is_bool_trivial true) => ? H.
  rewrite -[LHS]H.
  rewrite -[RHS]H.
  by [].
Qed.
Print is_bool.

Lemma sigma_bool_eqb_correct1 (sb:sigma_bool) : 
  eqb_correct_on sigma_bool_eqb sb.
Proof.
case: sb => b hb sb /=.
apply: (@eqb_body_correct sigma_bool
           sigma_bool_tag
           sigma_bool_fields_t sigma_bool_fields 
           sigma_bool_construct
           sigma_bool_constructP
           (sigma_bool_eqb_fields (fun=> xpredT))
           {| depn := b; depeq := hb |} _).
rewrite /eqb_fields_correct_on /= => -[b' hb'] /andP [] /= /peano_eqb_correct ? _.
subst b'. 
(* Now we rewrite UIP *)
rewrite (@UIP_dec _ Bool.bool_dec _ _ hb hb').
done.
Qed.
*)
End UseEqRect_SB.



*)
