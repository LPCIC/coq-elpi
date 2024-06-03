  $ . ../setup-project.sh
  $ dune build test.vo
  Coq version: 8.19.1 = 8 . 19 . 1
  Query assignments:
    MA = 8
    MI = 19
    P = 1
    V = 8.19.1
  hello world
  A
  B
  Query assignments:
    GR = «nat»
  Query assignments:
    GR = «Nat.add»
    MP = «Coq.Init.Datatypes»
  Query assignments:
    A = «test.test.succ»
    GR = «Nat.add»
    MP = «Coq.Init.Datatypes»
    X1 = [loc-gref (const «Nat.add»)]
    X2 = [loc-gref (const «Nat.add»)]
    X3 = [loc-abbreviation «test.test.succ»]
    X4 = [loc-modpath «Coq.Init.Datatypes»]
  Universe constraints: 
  Query assignments:
    X = «test.test.1»
  Universe constraints:
  UNIVERSES:
   {test.test.1} |= 
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    X = typ «test.test.2»
    Y = typ «test.test.3»
  Universe constraints:
  UNIVERSES:
   {test.test.3 test.test.2} |= test.test.2 <= test.test.3
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    X = typ «test.test.4»
    Y = typ «test.test.5»
  Universe constraints:
  UNIVERSES:
   {test.test.5 test.test.4} |= test.test.4 <= test.test.5
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    X = typ «test.test.6»
    Y = typ «test.test.7»
    Z = typ «test.test.8»
  Universe constraints:
  UNIVERSES:
   {test.test.8 test.test.7 test.test.6} |=
     test.test.6 <= test.test.8
     test.test.7 <= test.test.8
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    X = typ «test.test.9»
    Y = typ «test.test.10»
  Universe constraints:
  UNIVERSES:
   {test.test.10 test.test.9} |= test.test.9 < test.test.10
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  [foo (const «X»), foo (indt «nat»), foo (indt «bool»)]
  [foo (indt «nat»), foo (indt «bool»)]
  []
  [foo (indt «nat»)]
  hello [int 1, int 2, trm (global (indt «nat»)), str x]
  coq.pp.box (coq.pp.hv 2) 
   [coq.pp.str Module, coq.pp.spc, coq.pp.str Foo, coq.pp.spc, coq.pp.str :=, 
    coq.pp.brk 1 0, coq.pp.str body, coq.pp.spc, coq.pp.str End Foo.]
  Module
    Foo
    :=
    body
    End Foo.
  fix foo (x : ?e3) (y : ?e4) {struct x} : ?e2 :=
    match x as x0 return ?e6@{x:=x0} with
    | true => S (S (S O))
    | false => y
    end
  fix foo x y {struct x} := if x as x0 return ?e14@{x:=x0} then 3 else y
