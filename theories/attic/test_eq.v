From elpi Require Import elpi.

Elpi Command derive.eq.
Elpi Accumulate File "attic/derive-eq.elpi".
Elpi Accumulate "
  main [str X] :- derive-deceq X.
".

Theorem congr (A B : Type) (f g : A -> B) (x y : A) :
    x = y -> f = g -> f x = g y.
Proof. now intros Hxy Hfg; rewrite Hxy, Hfg. Qed.

Definition eq_ok (A : Type) (eq : A -> A -> bool) (a b : A) :=
  (eq a b = true <-> a = b).

Module DecEq.
  Record class (T : Type) := Class { cmp : T -> T -> bool;
                                     proof : forall (a b : T), cmp a b = true <-> a = b }.
  Structure type := Pack { obj : Type; class_of : class obj }.
  Definition op (e : type) : obj e -> obj e -> bool :=
    let 'Pack _ (Class _ cmp _) := e in cmp.
  Definition op_ok (e : type) : forall (a b : obj e), op e a b = true <-> a = b :=
    let 'Pack _ (Class _ _ proof) := e in proof.
  Arguments op {e} x y : simpl never.
  Arguments op_ok {e} : simpl never.
  Arguments Class {T} cmp proof.
  Module theory.
    Notation "x ~~ y" := (op x y) (at level 70).
  End theory.
End DecEq.

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

(* unit tests **************************** *)

(* these were written by Luc in the .elpi file
   but use constants defined in this file, so we
   put them here (and we run them systematically) *)

Elpi Query derive.eq "
%build-eq-check-test :-
   coq.locate ""andb""   And,
    coq.locate ""true""   True,
    coq.locate ""nat""    Nat,
    coq.locate ""O""      Zero,
    coq.locate ""S""      Succ,
    TY = {{nat -> nat -> bool}},
    (pi a\ pi b\ eq-proof Nat (pr a b) _ (app [Eq, a, b]))
     => build-eq-check And True
                       [pr Zero Zero, pr Zero Zero]
                       [Nat, Nat] Out.
".

Require Import NArith.

Elpi Query derive.eq "
%build-eq-check-test' :-
  coq.locate ""andb"" And,
    coq.locate ""true"" True,
    coq.locate ""nat""  Nat,
    coq.locate ""Nat.eqb"" Eq,
    (pi a\ pi b\ eq-proof Nat (pr a b) _ (app [Eq, a, b]))
     => build-eq-check And True [] [] Out.
". 

Elpi Query derive.eq "
%build-eq-check-proof-proj1-eq-test :-
   coq.locate ""mbtree"" MbTree,
    coq.locate ""mbnode"" MbNode, MbNode = indc GR,
    coq.env.indc GR _ _ _ TY,
    coq.locate ""eq_refl"" EqRefl', EqRefl = app [EqRefl', hole, hole],
    coq.locate ""congr"" FgEq,
    (pi eq\ pi heq\ pi x1\ pi y1\ pi x2\ pi y2\ pi x3\ pi y3\
        (pi t\ pi a\ pi b\ eq-proof t (pr a b) (app [heq, t, a, b]) (app [eq, t, a, b])) =>
        (build-eq-check-proof-proj1-eq MbNode MbNode TY [x1, x2, x3] [y1, y2, y3]
            [app [eq, MbTree, x1, y1], app [eq, MbTree, x2, y2], app [eq, {{nat}}, x3, y3]]
            FgEq EqRefl (Out eq heq x1 y1 x2 y2 x3 y3))),
    Bo = (fun _ {{forall (A : Type), A -> A -> bool}} eq\
        fun _ {{forall (A : Type) (a b : A), lp:eq A a b = true}} teq\
        fun _ {{forall (A : Type) (a b : A), eq_ok A (lp:eq A) a b}} heq\
        fun _ MbTree x1\ fun _ MbTree y1\ fun _ MbTree x2\ fun _ MbTree y2\
        fun _ {{nat}} x3\ fun _ {{nat}} y3\ Out teq heq x1 y1 x2 y2 x3 y3),
    coq.elaborate Bo TBo Bo'.
".

Elpi Query derive.eq "
%build-eq-check-proof-proj1-eq-test' :-
   coq.locate ""pair"" Pair, Pair = indc GR,
    coq.env.indc GR _ _ _ TY,
    coq.locate ""eq_refl"" EqRefl', EqRefl = app [EqRefl', hole, hole],
    coq.locate ""congr"" FgEq,
    (pi A\ pi B\ build-eq-match-proof-apply-params-types [A, B] TY (TY' A B)),
    (pi A\ pi B\ pi ha\ pi hb\ pi x1\ pi y1\ pi x2\ pi y2\
        (pi t\ pi a\ pi b\ eq-proof t (pr a b) {{DecEq.op_ok lp:a lp:b}} {{DecEq.op lp:a lp:b}}) =>
        (build-eq-check-proof-proj1-eq (app [Pair, A, B]) (app [Pair, A, B]) (TY' A B )[x1, x2] [y1, y2]
            [app [ha, x1, y1], app [hb, x2, y2]]
            FgEq EqRefl (Out A B ha hb x1 y1 x2 y2))),
    Bo = (fun `EA` {{DecEq.type}} EA\ fun `EB` {{DecEq.type}} EB\
        fun `HA` {{forall (a b : DecEq.obj lp:EA), DecEq.op a b = true}} ha\
        fun `HB` {{forall (a b : DecEq.obj lp:EB), DecEq.op a b = true}} hb\
        fun `x1` {{DecEq.obj lp:EA}} x1\ fun `y1` {{DecEq.obj lp:EA}} y1\
        fun `x2` {{DecEq.obj lp:EB}} x2\ fun `y2` {{DecEq.obj lp:EB}} y2\
        Out {{DecEq.obj lp:EA}} {{DecEq.obj lp:EB}} ha hb x1 y1 x2 y2),
    coq.elaborate Bo TBo Bo'.
".
 
Elpi Query derive.eq "
%build-eq-check-proof-proj1-test :-
    coq.locate ""mbnode"" MbNode, MbNode = indc GR,
    coq.env.indc GR _ _ _ TY,
    constructor-args Args' {prod->fun TY}, std.rev Args' Args,
    (pi h\ pi eq\ pi heq\ pi x1\ pi y1\ pi x2\ pi y2\ pi x3\ pi y3\
        (pi t\ pi a\ pi b\ eq-proof t (pr a b) (app [heq, t, a, b]) (app [eq, t, a, b])) =>
        build-eq-check-proof-proj1 MbNode TY Args
            [x3, x2, x1] [x1, x2, x3] [y3, y2, y1] [y1, y2, y3] [] h (Out h eq heq x1 y1 x2 y2 x3 y3)).
".


(* main tests *************************** *)

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
  Elpi derive.eq t.
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
