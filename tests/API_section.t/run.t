  $ . ../setup-project.sh
  $ dune build test.vo
  Query assignments:
    CA = «a»
    CB = «b»
    CC = «c»
  d : nat
  
  d is not universe polymorphic
  Expands to: Variable d
  eq_refl : e2 = 3
       : e2 = 3
  Query assignments:
    X = «x»
  fx : nat -> nat
       : nat -> nat
  opaque_3 : nat
  
  opaque_3 is not universe polymorphic
  opaque_3 is opaque
  Expands to: Constant test.test.opaque_3
  foo : nat
       : nat
  bar : bool -> nat
       : bool -> nat
