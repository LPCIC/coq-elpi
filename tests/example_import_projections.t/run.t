  $ . ../setup-project.sh
  $ dune build test.vo
  Notation p2 := (p2 nat 3 x)
  test.test.p1 nat 3 x : nat
       : nat
  p1 : forall (T : Type) (t : T), r T t -> nat
       : forall (T : Type) (t : T), r T t -> nat
  eq_refl : test.test.p1 bool false (Build bool false 3 eq_refl eq_refl) = 3
       : test.test.p1 bool false (Build bool false 3 eq_refl eq_refl) = 3
  test.f1 _ x
       : bool
  File "./test.v", line 48, characters 0-21:
  Warning: Trying to mask the absolute name "test.test.p1"!
  [masking-absolute-name,deprecated-since-8.8,deprecated,default]
  File "./test.v", line 48, characters 0-21:
  Warning: Trying to mask the absolute name "test.test.p2"!
  [masking-absolute-name,deprecated-since-8.8,deprecated,default]
  File "./test.v", line 57, characters 0-70:
  Warning: Trying to mask the absolute name "test.test.p1"!
  [masking-absolute-name,deprecated-since-8.8,deprecated,default]
  File "./test.v", line 57, characters 0-70:
  Warning: Trying to mask the absolute name "test.test.p2"!
  [masking-absolute-name,deprecated-since-8.8,deprecated,default]
