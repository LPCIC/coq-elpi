Cd "~/git/coq-elpi".
(* Set Universe Polymorphism. *)

From elpi Require Import elpi.

Set Printing Universes.
Class param_db {X X1 XR : Type} (x : X) (x : X1) (xR : XR) := store_param {}.
Class param {X : Type} {XR : X -> X -> Type} (x : X) (xR : XR x x) := Param {}.

Elpi Tactic param " typecheck.".
Elpi Accumulate File "coq-extra.elpi".
Elpi Accumulate File "coq-param.elpi".
Elpi Run param "typecheck".

Elpi Print param "param.html"
  "pervasives.elpi"
  "coq-lib.elpi"
  "lp-lib.elpi"
  "coq-refiner.elpi".

Elpi Run param "env-add-param {{@unit}} ""unitR""".
Elpi Run param "env-add-param {{@nat}} ""natR""".
Elpi Run param "env-add-param {{@list}} ""listR""".
Elpi Run param "env-add-param {{@eq}} ""eqR""".
Elpi Run param "env-add-param {{@plus}} ""plusR""".

Definition test := fun x0 : nat => fun x1=> fun x2=>
    fun y0=> fun y1=> fun y2=>
    x0 + x1 + x2 + y0 + y1 + y2.

Elpi Run param "
  term->gr {{@test}} GR,
  coq-env-const GR X _,
  $coq-say X,
  perm-op lam demix 6 X [] Y _,
  perm-op lam (mix 2) 6  Y [] Z _
".





Inductive vec (A : Type) : nat -> Type :=
    nil : vec A 0 | cons : A -> forall n : nat, vec A n -> vec A (S n).
Elpi Run param "env-add-param {{@vec}} ""vecR"")".

Definition vec_length_type := forall (A : Type) (n : nat), vec A n -> nat.
Elpi Run param "env-add-param {{@vec_length_type}} ""vec_length_typeR"")".

Definition vec_length_rec (vec_length : vec_length_type)
  (A : Type) n (v : vec A n) :=
  match v with nil _ => 0 | cons _ _ _ w => S (vec_length _ _ w) end.
Elpi Run param "env-add-param {{@vec_length_rec}} ""vec_length_recR"")".

Fixpoint vec_length (A : Type) n (v : vec A n) :=
  match v with nil _ => 0 | cons _ _ _ w => S (vec_length _ _ w) end.

From Coq Require Import ssreflect ssrfun ssrbool.


Definition vec_lengthR : vec_length_typeR vec_length vec_length.
unfold vec_length_typeR.
fix 8.
set (FR := vec_length_recR vec_length vec_length vec_lengthR).
refine (let F' : (forall (A A0 : Type) (A1 : A -> A0 -> Type)
       (n n0 : nat) (n1 : natR n n0) (v : vec A n) (v0 : vec A0 n0),
     vecR A A0 A1 n n0 n1 v v0 ->
     natR
       match v with
       | nil _ => 0
       | cons _ _ n5 w => S (vec_length A n5 w)
       end (@vec_length A0 n0 v0)) :=
  fun A A0 A1 n n0 n1 v v0 => _ in _).
Unshelve. Focus 2.
induction v0.
  set v0 := nil _.
  apply (FR A A0 A1 n 0 n1 v v0).
set v0' := cons _ _ _ _.
apply (FR A A0 A1 n (S n0) n1 v v0').


Show Proof.


refine (let F' : (forall (A A0 : Type)
       (n n0 : nat) (v : vec A n) (v0 : vec A0 n0),
     forall (A1 : A -> A0 -> Type) (n1 : natR n n0),
     vecR A A0 A1 n n0 n1 v v0 ->
     natR
       match v with
       | nil _ => 0
       | cons _ _ n5 w => S (vec_length A n5 w)
       end (@vec_length A0 n0 v0)) :=
  fun A A0 n n0 v v0 => _ in _).
Unshelve. Focus 2.
induction v0.
  set v0 := nil _.
  intros A1 n1 v1.
  apply (FR A A0 A1 n n0 n1 v v0 v1).
  (* match v0 as v0 in vec _ abstract return ( *)
  (*      forall (A1 : A -> A0 -> Type) (n1 : natR n abstract), vecR A A0 A1 n abstract n1 v v0 -> natR match v with *)
  (*      | nil _ => 0 *)
  (*      | cons _ _ n5 w => S (vec_length A n5 w) *)
  (*      end (@vec_length A0 abstract v0)) *)
  (* with nil _ as k | cons _ _ _ _ as k =>  *)
  (*   fun A1 n1 v1 => FR A A0 A1 n n0 n1 v v0 v1 end *)
  (*       in _). *)
refine (let F : (forall (A A0 : Type) (A1 : A -> A0 -> Type)
       (n n0 : nat) (n1 : natR n n0) (v : vec A n) (v0 : vec A0 n0),
     vecR A A0 A1 n n0 n1 v v0 ->
     natR (@vec_length A n v) (@vec_length A0 n0 v0)) :=
  fun A A0 A1 n n0 n1 v v0 =>
  match v with nil _ as k | cons _ _ _ _ as k => _ end
        in _).
exact F.
Defined.


Definition vec_lengthR : vec_length_typeR vec_length vec_length.
unfold vec_length_typeR.
fix 8.
set (FR := vec_length_recR vec_length vec_length vec_lengthR).
refine (let F' : (forall (A A0 : Type) (A1 : A -> A0 -> Type)
       (n n0 : nat) (n1 : natR n n0) (v : vec A n) (v0 : vec A0 n0),
     vecR A A0 A1 n n0 n1 v v0 ->
     natR
       match v with
       | nil _ => 0
       | cons _ _ n5 w => S (vec_length A n5 w)
       end (@vec_length A0 n0 v0)) :=
  fun A A0 A1 n n0 n1 v v0 =>
  match v0 as v0 in vec _ abstract return (
       vecR A A0 A1 n abstract n1 v v0 -> natR match v with
       | nil _ => 0
       | cons _ _ n5 w => S (vec_length A n5 w)
       end (@vec_length A0 abstract v0))
  with nil _ as k | cons _ _ _ _ as k => FR A A0 A1 n n0 n1 v v0 end
        in _).
refine (let F : (forall (A A0 : Type) (A1 : A -> A0 -> Type)
       (n n0 : nat) (n1 : natR n n0) (v : vec A n) (v0 : vec A0 n0),
     vecR A A0 A1 n n0 n1 v v0 ->
     natR (@vec_length A n v) (@vec_length A0 n0 v0)) :=
  fun A A0 A1 n n0 n1 v v0 =>
  match v with nil _ as k | cons _ _ _ _ as k => _ end
        in _).
exact F.
Defined.

intros A2 A3 A4 n4 v2 v3.


Show Proof.


Fail Elpi Run param "env-add-param {{@vec_length}} ""vec_lengthR"")".
Elpi Run param "coq-env-const {term->gr {{@vec_length}}} X _, $coq-say X,
                     with-TC-param (param X _ Res)".

Fail Elpi Run param "
coq-env-const {term->gr {{@vec_length}}} X Ty,
unify-eq Ty (prod _ ATy _),
(MyFix = let ""vec_length""
 (prod ""A"" (ATy) x0 \
   prod ""n"" ({{@nat}}) x1 \
    prod ""v"" (app [{{@vec}}, x0, x1]) x2 \ {{@nat}})
 (fix ""vec_length"" 2
   (prod ""A"" (ATy) x0 \
     prod ""n"" ({{@nat}}) x1 \
      prod ""v"" (app [{{@vec}}, x0, x1]) x2 \ {{@nat}}) x0 \
   lam ""A"" (ATy) x1 \
    lam ""n"" ({{@nat}}) x2 \
     lam ""v"" (app [{{@vec}}, x1, x2]) x3 \
      match x3
       (lam ""n"" ({{@nat}}) x4 \
         lam ""v"" (app [{{@vec}}, x1, x4]) x5 \ {{@nat}})
       [{{@O}},
        (lam ""a"" x1 x4 \
          lam ""n"" ({{@nat}}) x5 \
           lam ""w"" (app [{{@vec}}, x1, x5]) x6 \
            app [{{@S}}, app [x0, x1, x5, x6]])]) x0 \
 let ""vec_length""
  (prod ""A"" (ATy) x1 \
    prod ""n"" ({{@nat}}) x2 \
     prod ""v"" (app [{{@vec}}, x1, x2]) x3 \ {{@nat}})
  (fix ""vec_length"" 2
    (prod ""A"" (ATy) x1 \
      prod ""n"" ({{@nat}}) x2 \
       prod ""v"" (app [{{@vec}}, x1, x2]) x3 \ {{@nat}}) x1 \
    lam ""A"" (ATy) x2 \
     lam ""n"" ({{@nat}}) x3 \
      lam ""v"" (app [{{@vec}}, x2, x3]) x4 \
       match x4
        (lam ""n"" ({{@nat}}) x5 \
          lam ""v"" (app [{{@vec}}, x2, x5]) x6 \ {{@nat}})
        [{{@O}},
         (lam ""a"" x2 x5 \
           lam ""n"" ({{@nat}}) x6 \
            lam ""w"" (app [{{@vec}}, x2, x6]) x7 \
             app [{{@S}}, app [x1, x2, x6, x7]])]) x1 \
  fix ""vec_length"" 8
   (prod ""A"" (ATy) x2 \
     prod ""A"" (ATy) x3 \
      prod ""A"" (prod ""s"" x2 x4 \ prod ""s"" x3 x5 \ ATy) x4 \
       prod ""n"" ({{@nat}}) x5 \
        prod ""n"" ({{@nat}}) x6 \
         prod ""n"" (app [{{@natR}}, x5, x6]) x7 \
          prod ""v"" (app [{{@vec}}, x2, x5]) x8 \
           prod ""v"" (app [{{@vec}}, x3, x6]) x9 \
            prod ""v"" (app [{{@vecR}}, x2, x3, x4, x5, x6, x7, x8, x9])
             x10 \
             app
              [{{@natR}}, app [app [app [x0, x2], x5], x8],
               app [app [app [x1, x3], x6], x9]]) x2 \
   lam ""A"" (ATy) x3 \
    lam ""A"" (ATy) x4 \
     lam ""A"" (prod ""s"" x3 x5 \ prod ""s"" x4 x6 \ ATy) x5 \
      lam ""n"" ({{@nat}}) x6 \
       lam ""n"" ({{@nat}}) x7 \
        lam ""n"" (app [{{@natR}}, x6, x7]) x8 \
         lam ""v"" (app [{{@vec}}, x3, x6]) x9 \
          lam ""v"" (app [{{@vec}}, x4, x7]) x10 \
           lam ""v"" (app [{{@vecR}}, x3, x4, x5, x6, x7, x8, x9, x10]) x11 \
            app
             [app
               [app
                 [app
                   [app
                     [app
                       [app
                         [app
                           [app
                             [(let ""U""
                                (prod ""x""
                                  (prod ""A"" (ATy) x12 \
                                    prod ""n"" ({{@nat}}) x13 \
                                     prod ""v"" (app [{{@vec}}, x12, x13])
                                      x14 \ {{@nat}}) x12 \
                                  prod ""hd_beta_auto"" (ATy)
                                   x13 \
                                   prod ""hd_beta_auto"" ({{@nat}}) x14 \
                                    prod ""hd_beta_auto""
                                     (app [{{@vec}}, x13, x14]) x15 \
                                     {{@nat}})
                                (lam ""x""
                                  (prod ""A"" (ATy) x12 \
                                    prod ""n"" ({{@nat}}) x13 \
                                     prod ""v"" (app [{{@vec}}, x12, x13])
                                      x14 \ {{@nat}}) x12 \
                                  lam ""hd_beta_auto"" (ATy)
                                   x13 \
                                   lam ""hd_beta_auto"" ({{@nat}}) x14 \
                                    lam ""hd_beta_auto""
                                     (app [{{@vec}}, x13, x14]) x15 \
                                     match x15
                                      (lam ""n"" ({{@nat}}) x16 \
                                        lam ""v"" (app [{{@vec}}, x13, x16])
                                         x17 \ {{@nat}})
                                      [{{@O}},
                                       (lam ""a"" x13 x16 \
                                         lam ""n"" ({{@nat}}) x17 \
                                          lam ""w""
                                           (app [{{@vec}}, x13, x17]) x18 \
                                           app
                                            [{{@S}},
                                             app [x12, x13, x17, x18]])])
                                x12 \
                                let ""U1""
                                 (prod ""x""
                                   (prod ""A"" (ATy) x13 \
                                     prod ""n"" ({{@nat}}) x14 \
                                      prod ""v"" (app [{{@vec}}, x13, x14])
                                       x15 \ {{@nat}}) x13 \
                                   prod ""hd_beta_auto"" (ATy)
                                    x14 \
                                    prod ""hd_beta_auto"" ({{@nat}}) x15 \
                                     prod ""hd_beta_auto""
                                      (app [{{@vec}}, x14, x15]) x16 \
                                      {{@nat}})
                                 (lam ""x""
                                   (prod ""A"" (ATy) x13 \
                                     prod ""n"" ({{@nat}}) x14 \
                                      prod ""v"" (app [{{@vec}}, x13, x14])
                                       x15 \ {{@nat}}) x13 \
                                   lam ""hd_beta_auto"" (ATy)
                                    x14 \
                                    lam ""hd_beta_auto"" ({{@nat}}) x15 \
                                     lam ""hd_beta_auto""
                                      (app [{{@vec}}, x14, x15]) x16 \
                                      match x16
                                       (lam ""n"" ({{@nat}}) x17 \
                                         lam ""v"" (app [{{@vec}}, x14, x17])
                                          x18 \ {{@nat}})
                                       [{{@O}},
                                        (lam ""a"" x14 x17 \
                                          lam ""n"" ({{@nat}}) x18 \
                                           lam ""w""
                                            (app [{{@vec}}, x14, x18])
                                            x19 \
                                            app
                                             [{{@S}},
                                              app [x13, x14, x18, x19]])])
                                 x13 \
                                 let ""FR""
                                  (prod ""A"" (ATy) x14 \
                                    prod ""A"" (ATy) x15 \
                                     prod ""A""
                                      (prod ""s"" x14 x16 \
                                        prod ""s"" x15 x17 \ ATy)
                                      x16 \
                                      prod ""n"" ({{@nat}}) x17 \
                                       prod ""n"" ({{@nat}}) x18 \
                                        prod ""n""
                                         (app [{{@natR}}, x17, x18]) x19 \
                                         prod ""v""
                                          (app [{{@vec}}, x14, x17]) x20 \
                                          prod ""v""
                                           (app [{{@vec}}, x15, x18]) x21 \
                                           prod ""v""
                                            (app
                                              [{{@vecR}}, x14, x15, x16,
                                               x17, x18, x19, x20, x21])
                                            x22 \
                                            app
                                             [{{@natR}},
                                              app
                                               [app
                                                 [app [app [x12, x0], x14],
                                                  x17], x20],
                                              app
                                               [app
                                                 [app [app [x13, x1], x15],
                                                  x18], x21]])
                                  (lam ""A"" (ATy) x14 \
                                    lam ""A"" (ATy) x15 \
                                     lam ""A""
                                      (prod ""s"" x14 x16 \
                                        prod ""s"" x15 x17 \ ATy)
                                      x16 \
                                      lam ""n"" ({{@nat}}) x17 \
                                       lam ""n"" ({{@nat}}) x18 \
                                        lam ""n"" (app [{{@natR}}, x17, x18])
                                         x19 \
                                         lam ""v"" (app [{{@vec}}, x14, x17])
                                          x20 \
                                          lam ""v""
                                           (app [{{@vec}}, x15, x18]) x21 \
                                           lam ""v""
                                            (app
                                              [{{@vecR}}, x14, x15, x16,
                                               x17, x18, x19, x20, x21])
                                            x22 \
                                            match x22
                                             (lam ""n"" ({{@nat}}) x23 \
                                               lam ""n"" ({{@nat}}) x24 \
                                                lam ""n""
                                                 (app [{{@natR}}, x23, x24])
                                                 x25 \
                                                 lam ""v""
                                                  (app [{{@vec}}, x14, x23])
                                                  x26 \
                                                  lam ""v""
                                                   (app
                                                     [{{@vec}}, x15, x24])
                                                   x27 \
                                                   lam ""v""
                                                    (app
                                                      [{{@vecR}}, x14, x15,
                                                       x16, x23, x24, x25,
                                                       x26, x27]) x28 \
                                                    app
                                                     [{{@natR}},
                                                      match x26
                                                       (lam ""n"" ({{@nat}})
                                                         x29 \
                                                         lam ""v""
                                                          (app
                                                            [{{@vec}}, x14,
                                                             x29]) x30 \
                                                          {{@nat}})
                                                       [{{@O}},
                                                        (lam ""a"" x14 x29 \
                                                          lam ""n""
                                                           ({{@nat}}) x30 \
                                                           lam ""w""
                                                            (app
                                                              [{{@vec}},
                                                               x14, x30])
                                                            x31 \
                                                            app
                                                             [{{@S}},
                                                              app
                                                               [x0, x14, x30,
                                                                x31]])],
                                                      match x27
                                                       (lam ""n"" ({{@nat}})
                                                         x29 \
                                                         lam ""v""
                                                          (app
                                                            [{{@vec}}, x15,
                                                             x29]) x30 \
                                                          {{@nat}})
                                                       [{{@O}},
                                                        (lam ""a"" x15 x29 \
                                                          lam ""n""
                                                           ({{@nat}}) x30 \
                                                           lam ""w""
                                                            (app
                                                              [{{@vec}},
                                                               x15, x30])
                                                            x31 \
                                                            app
                                                             [{{@S}},
                                                              app
                                                               [x1, x15, x30,
                                                                x31]])]])
                                             [{{@natR_O}},
                                              (lam ""a"" x14 x23 \
                                                lam ""a"" x15 x24 \
                                                 lam ""a""
                                                  (app [x16, x23, x24]) x25 \
                                                  lam ""n"" ({{@nat}}) x26 \
                                                   lam ""n"" ({{@nat}}) x27 \
                                                    lam ""n""
                                                     (app
                                                       [{{@natR}}, x26, x27])
                                                     x28 \
                                                     lam ""w""
                                                      (app
                                                        [{{@vec}}, x14, x26])
                                                      x29 \
                                                      lam ""w""
                                                       (app
                                                         [{{@vec}}, x15,
                                                          x27]) x30 \
                                                       lam ""w""
                                                        (app
                                                          [{{@vecR}}, x14,
                                                           x15, x16, x26,
                                                           x27, x28, x29, x30])
                                                        x31 \
                                                        app
                                                         [{{@natR_S}},
                                                          app
                                                           [x0, x14, x26, x29],
                                                          app
                                                           [x1, x15, x27, x30],
                                                          app
                                                           [x2, x14, x15,
                                                            x16, x26, x27,
                                                            x28, x29, x30,
                                                            x31]])]) x14 \
                                  let ""F'""
                                   (prod ""A"" (ATy) x15 \
                                     prod ""A"" (ATy) x16 \
                                      prod ""A""
                                       (prod ""s"" x15 x17 \
                                         prod ""s"" x16 x18 \ ATy)
                                       x17 \
                                       prod ""n"" ({{@nat}}) x18 \
                                        prod ""n"" ({{@nat}}) x19 \
                                         prod ""n""
                                          (app [{{@natR}}, x18, x19]) x20 \
                                          prod ""v""
                                           (app [{{@vec}}, x15, x18]) x21 \
                                           prod ""v""
                                            (app [{{@vec}}, x16, x19])
                                            x22 \
                                            prod ""v""
                                             (app
                                               [{{@vecR}}, x15, x16, x17,
                                                x18, x19, x20, x21, x22])
                                             x23 \
                                             app
                                              [{{@natR}},
                                               app
                                                [app
                                                  [app [app [x12, x0], x15],
                                                   x18], x21],
                                               app
                                                [app [app [x1, x16], x19],
                                                 x22]])
                                   (lam ""A"" (ATy) x15 \
                                     lam ""A"" (ATy) x16 \
                                      lam ""A""
                                       (prod ""s"" x15 x17 \
                                         prod ""s"" x16 x18 \ ATy)
                                       x17 \
                                       lam ""n"" ({{@nat}}) x18 \
                                        lam ""n"" ({{@nat}}) x19 \
                                         lam ""n""
                                          (app [{{@natR}}, x18, x19]) x20 \
                                          lam ""v""
                                           (app [{{@vec}}, x15, x18]) x21 \
                                           lam ""v""
                                            (app [{{@vec}}, x16, x19])
                                            x22 \
                                            match x22
                                             (lam ""v""
                                               (app [{{@vec}}, x16, x19])
                                               x23 \
                                               prod ""v""
                                                (app
                                                  [{{@vecR}}, x15, x16,
                                                   x17, x18, x19, x20, x21,
                                                   x23]) x24 \
                                                app
                                                 [{{@natR}},
                                                  app
                                                   [app
                                                     [app
                                                       [app [x12, x0], x15],
                                                      x18], x21],
                                                  app
                                                   [app [app [x1, x16], x19],
                                                    x23]])
                                             [(let ""K""
                                                (app [{{@vec}}, x16, x19])
                                                (app [{{@nil}}, x16]) x23 \
                                                app
                                                 [x14, x15, x16, x17, x18,
                                                  x19, x20, x21, x23]),
                                              (let ""K""
                                                (app [{{@vec}}, x16, x19])
                                                (app [{{@cons}}, x16])
                                                x23 \
                                                app
                                                 [x14, x15, x16, x17, x18,
                                                  x19, x20, x21, x23])])
                                   x15 \
                                   let ""F""
                                    (prod ""A"" (ATy) x16 \
                                      prod ""A"" (ATy) x17 \
                                       prod ""A""
                                        (prod ""s"" x16 x18 \
                                          prod ""s"" x17 x19 \
                                           ATy) x18 \
                                        prod ""n"" ({{@nat}}) x19 \
                                         prod ""n"" ({{@nat}}) x20 \
                                          prod ""n""
                                           (app [{{@natR}}, x19, x20])
                                           x21 \
                                           prod ""v""
                                            (app [{{@vec}}, x16, x19])
                                            x22 \
                                            prod ""v""
                                             (app [{{@vec}}, x17, x20])
                                             x23 \
                                             prod ""v""
                                              (app
                                                [{{@vecR}}, x16, x17, x18,
                                                 x19, x20, x21, x22, x23])
                                              x24 \
                                              app
                                               [{{@natR}},
                                                app
                                                 [app [app [x0, x16], x19],
                                                  x22],
                                                app
                                                 [app [app [x1, x17], x20],
                                                  x23]])
                                    (lam ""A"" (ATy) x16 \
                                      lam ""A"" (ATy) x17 \
                                       lam ""A""
                                        (prod ""s"" x16 x18 \
                                          prod ""s"" x17 x19 \
                                           ATy) x18 \
                                        lam ""n"" ({{@nat}}) x19 \
                                         lam ""n"" ({{@nat}}) x20 \
                                          lam ""n""
                                           (app [{{@natR}}, x19, x20])
                                           x21 \
                                           lam ""v""
                                            (app [{{@vec}}, x16, x19])
                                            x22 \
                                            match x22
                                             (lam ""v""
                                               (app [{{@vec}}, x16, x19])
                                               x23 \
                                               prod ""v""
                                                (app [{{@vec}}, x17, x20])
                                                x24 \
                                                prod ""v""
                                                 (app
                                                   [{{@vecR}}, x16, x17,
                                                    x18, x19, x20, x21, x23,
                                                    x24]) x25 \
                                                 app
                                                  [{{@natR}},
                                                   app
                                                    [app [app [x0, x16], x19],
                                                     x23],
                                                   app
                                                    [app [app [x1, x17], x20],
                                                     x24]])
                                             [(let ""K""
                                                (app [{{@vec}}, x16, x19])
                                                (app [{{@nil}}, x16]) x23 \
                                                app
                                                 [x15, x16, x17, x18, x19,
                                                  x20, x21, x23]),
                                              (let ""K""
                                                (app [{{@vec}}, x16, x19])
                                                (app [{{@cons}}, x16])
                                                x23 \
                                                app
                                                 [x15, x16, x17, x18, x19,
                                                  x20, x21, x23])]) x16 \ x16),
                              x3], x4], x5], x6], x7], x8], x9], x10], x11]),
$coq-say ""MyFix="" MyFix,
coq-elaborate MyFix _ _".

(* ARTy = x3\ x4\ app [(lam ""s"" ATy x5 \ lam ""s"" ATy x6 \ *)
(*             prod ""s"" x5 x7 \ prod ""s"" x6 x8 \ ATy), x3, x4], *)

Elpi Run param "with-TC-param (param {{O}} X Y)".
Elpi Run param "with-TC-param (param {{S (S 0)}} X Y)".

Fail Elpi Run param "param-const {{@eq_refl}} _ _ _ _ _".

Elpi Run param "with-TC {{@param_db}} retrieve-param (param {{nat}} X Y)".

Definition nat2nat := nat -> nat.
Definition nat2nat2nat := nat -> nat -> nat.
Elpi Run param "env-add-param {{@nat2nat}} ""nat2natR""".
Elpi Run param "env-add-param {{@nat2nat2nat}} ""nat2nat2natR""".
Elpi Run param "env-add-param {{@pred}} ""predR""".
Print predR.
Check (predR : nat2natR pred pred).

Fixpoint predn n := match n with 0 => 0 | S n => S (predn n) end.

Elpi Run param "env-add-param {{@predn}} ""prednR""".
Elpi Run param "env-add-param {{@plus}} ""plusR""".

Check (prednR : nat2natR predn predn).
Check (plusR : nat2nat2natR plus plus).

Fixpoint quasidn n m := S (match n with 0 => m | S n => S (quasidn n m) end).
Elpi Run param "param-const {{@quasidn}} _ _ _ _ _".

Fixpoint weirdn n := match n with S (S n) => S (weirdn n) | _ => 0 end.
Elpi Run param "param-const {{@weirdn}} _ _ _ _ _".

Inductive bla : nat -> Type := Bla : nat -> bla 0 | Blu n : bla n -> bla 1.
Elpi Run param "env-add-param {{@bla}} ""blaR"")".

Elpi Run param "coq-TC-db-for {term->gr {{@param_db}}} _".
