From elpi Require Import elpi derive.eq.

Require Import Coq.Lists.List.

Inductive mbtree :=
| mbnode : mbtree -> mbtree -> nat -> mbtree
| mbleaf : nat * nat -> mbtree.

Fixpoint eq_list (A : Type)
(eq : A -> A -> bool) (l1 l2 : list A) :=
match (l1,l2) with
| (cons x1 t1, cons x2 t2) => andb (eq x1 x2)
                         (eq_list A eq t1 t2)
| (nil,nil) => true
| _ => false
end.

Inductive awful (A B : Type) : Type :=
| mkawful : awful (list B) B -> awful A B
| awful_nil : B -> awful A B.

Inductive mlist (A B : Type) : Type :=
| mcons : A -> B -> mlist A B -> mlist A B
| mnil  : mlist A B.
About mlist.

Elpi derive.eq prod.
Fail Elpi derive.eq mbtree.
Elpi derive.eq nat.
Elpi derive.eq mbtree.
Print mbtree_equal.
Print mbtree_equal_ok.
Elpi derive.eq mlist.
Elpi derive.eq list.

Module Foo.
  Inductive t := K (_ : nat) | W (_ : t).
  Elpi derive.eq.
End Foo.
Print Foo.t_equal.

Print eq_list.
Print list_equal.
Print mlist_equal_ok.

Import DecEq.theory. 
Eval compute in (3,4,(cons 3 nil)) ~~ (3,4,nil).

Inductive monster :=
| K1(_ : nat) 
| K2(_ : nat) (_ : nat) 
| K3(_ : nat) (_ : nat) (_ : nat) 
| K4(_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K5(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K6(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K7(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K8(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K9(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
(*| K10(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K11(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K12(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K13(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K14(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K15(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K16(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K17(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K18(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K19(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K20(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K21(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K22(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K23(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K24(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K25(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K26(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K27(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K28(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K29(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K30(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K31(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K32(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K33(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K34(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K35(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K36(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K37(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K38(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K39(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K40(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K41(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K42(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K43(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K44(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K45(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K46(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K47(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K48(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K49(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
| K50(_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) (_ : nat) 
*).
Elpi derive.eq monster.

Lemma test (x y : monster) : { x = y } + { ~ x = y}.
Proof. Time repeat decide equality. Time Defined.

Theorem DecideEquality {A : DecEq.type} (x y : DecEq.obj A) : { x = y } + { ~ x = y }.
Proof. destruct (DecEq.op x y) eqn:Hop.
  - left. apply DecEq.op_ok. assumption.
  - right. intro H. apply DecEq.op_ok in H. rewrite -> H in Hop. inversion Hop.
Qed.

Lemma test' (x y : monster) : { x = y } + { ~ x = y }.
Proof. apply DecideEquality. Defined.
