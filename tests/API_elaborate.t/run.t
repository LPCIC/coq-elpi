  $ . ../setup-project.sh
  $ dune build test.vo
  Query assignments:
    E = fun `n` (global (indt «nat»)) c0 \
   fun `t` (app [global (const «T2»), c0]) c1 \
    fun `x` 
     (app [global (const «f3»), c0, app [global (const «h»), c0, c1]]) c2 \
     app
      [global (const «g3»), c0, app [global (const «h»), c0, c1], 
       app
        [global (indc «S»), 
         app
          [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]]
    TY = prod `n` (global (indt «nat»)) c0 \
   prod `t` (app [global (const «T2»), c0]) c1 \
    prod `x` 
     (app [global (const «f3»), c0, app [global (const «h»), c0, c1]]) c2 \
     global (indt «nat»)
    _uvk_1_ = X0
  Universe constraints:
  UNIVERSES:
   {test.test.13 test.test.10 test.test.9} |=
     test.test.13 < test.test.9
     Set <= test.test.10
     Set <= test.test.13
     T2.u0 <= test.test.13
     f3.u0 <= test.test.13
  ALGEBRAIC UNIVERSES:
   {test.test.10}
  FLEXIBLE UNIVERSES:
   test.test.10
  SORTS:
   α4 := Type
   α5 := Type
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    E = app
   [global (const «bar»), 
    app
     [global (indc «S»), 
      app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]], 
    global (const «xxx»)]
    TY = prop
    _uvk_4_ = X0
    _uvk_5_ = X1
  Query assignments:
    E = app
   [global (const «op»), global (const «c»), 
    app
     [global (indc «S»), 
      app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]]
    TY = app [global (const «field»), global (const «c»)]
    _uvk_6_ = X0
  Universe constraints:
  UNIVERSES:
   {test.test.19 test.test.18} |=
     test.test.19 < test.test.18
     s.u0 <= test.test.19
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α11 := Type
  WEAK CONSTRAINTS:
   
  
  raw: 
  parameter A explicit (global (const «T1»)) c0 \
   inductive ind1 tt 
    (parameter B explicit (sort (typ «test.test.20»)) c1 \
      arity (sort (typ «test.test.22»))) c1 \
    [constructor K1 
      (parameter B explicit (sort (typ «test.test.20»)) c2 \
        arity (prod `_` (app [c1, c2]) c3 \ app [c1, c2])), 
     constructor K2 
      (parameter B explicit (sort (typ «test.test.20»)) c2 \
        arity (prod `_` (app [global (const «f1»), c0]) c3 \ app [c1, c2])), 
     constructor K3 
      (parameter B explicit (sort (typ «test.test.20»)) c2 \
        arity (prod `a` (app [global (const «f1»), c0]) c3 \ app [c1, c2]))]
  elab1: 
  parameter A explicit (global (const «T1»)) c0 \
   inductive ind1 tt 
    (parameter B explicit (sort (typ «test.test.23»)) c1 \
      arity (sort (typ «test.test.25»))) c1 \
    [constructor K1 
      (parameter B explicit (sort (typ «test.test.28»)) c2 \
        arity (prod `_` (app [c1, c2]) c3 \ app [c1, c2])), 
     constructor K2 
      (parameter B explicit (sort (typ «test.test.30»)) c2 \
        arity (prod `_` (app [global (const «f1»), c0]) c3 \ app [c1, c2])), 
     constructor K3 
      (parameter B explicit (sort (typ «test.test.33»)) c2 \
        arity (prod `a` (app [global (const «f1»), c0]) c3 \ app [c1, c2]))]
  elab2: 
  parameter A explicit (global (const «T1»)) c0 \
   parameter B explicit (sort (typ «ind1.u0»)) c1 \
    inductive ind1 tt (arity (sort (typ «ind1.u1»))) c2 \
     [constructor K1 (arity (prod `_` c2 c3 \ c2)), 
      constructor K2 
       (arity (prod `_` (app [global (const «f1»), c0]) c3 \ c2)), 
      constructor K3 
       (arity (prod `a` (app [global (const «f1»), c0]) c3 \ c2))]
  raw: 
  parameter A explicit (global (const «T1»)) c0 \
   record ind2 (sort (typ «f1.u0»)) Build_ind2 
    (field [coercion off, canonical tt] fld1 (app [global (const «f1»), c0]) 
      c1 \
      field [coercion off, canonical tt] fld2 
       (app [global (indt «eq»), app [global (const «f1»), c0], c1, c1]) 
       c2 \ end-record)
  elab1: 
  parameter A explicit (global (const «T1»)) c0 \
   record ind2 (sort (typ «test.test.38»)) Build_ind2 
    (field [coercion off, canonical tt] fld1 (app [global (const «f1»), c0]) 
      c1 \
      field [coercion off, canonical tt] fld2 
       (app [global (indt «eq»), app [global (const «f1»), c0], c1, c1]) 
       c2 \ end-record)
  elab2: 
  parameter A explicit (global (const «T1»)) c0 \
   record ind2 (sort (typ «ind2.u0»)) Build_ind2 
    (field [coercion off, canonical tt] fld1 (app [global (const «f1»), c0]) 
      c1 \
      field [coercion off, canonical tt] fld2 
       (app [global (indt «eq»), app [global (const «f1»), c0], c1, c1]) 
       c2 \ end-record)
  raw: 
  record ind3 (sort (typ «test.test.41»)) Build_ind3 
   (field [coercion reversible, canonical tt] fld3 
     (sort (typ «test.test.40»)) c0 \
     field [coercion off, canonical tt] fld4 
      (prod `x` c0 c1 \ app [global (indt «eq»), c0, c1, c1]) c1 \ end-record)
  elab1: 
  record ind3 (sort (typ «test.test.42»)) Build_ind3 
   (field [coercion reversible, canonical tt] fld3 
     (sort (typ «test.test.43»)) c0 \
     field [coercion off, canonical tt] fld4 
      (prod `x` c0 c1 \ app [global (indt «eq»), c0, c1, c1]) c1 \ end-record)
  elab2: 
  record ind3 (sort (typ «ind3.u0»)) Build_ind3 
   (field [coercion reversible, canonical tt] fld3 (sort (typ «ind3.u1»)) 
     c0 \
     field [coercion off, canonical tt] fld4 
      (prod `x` c0 c1 \ app [global (indt «eq»), c0, c1, c1]) c1 \ end-record)
  forall x : ind3, x -> Prop
       : Type
  Query assignments:
    E = app
   [global (const «op»), global (const «c»), 
    app
     [global (indc «S»), 
      app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]]
    TY = app [global (const «field»), global (const «c»)]
  Universe constraints:
  UNIVERSES:
   {test.test.50 test.test.49} |=
     test.test.50 < test.test.49
     s.u0 <= test.test.50
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α19 := Type
  WEAK CONSTRAINTS:
   
  
  unknown_gref
  «test.test.52» «test.test.52»
  Query assignments:
    E = app [global (indt «list»), global (const «C»)]
    TY = sort (typ «test.test.58»)
  Universe constraints:
  UNIVERSES:
   {test.test.59 test.test.58 test.test.57} |=
     test.test.58 < test.test.59
     test.test.59 < test.test.57
     Set <= test.test.58
     test.test.56 <= list.u0
     test.test.56 <= test.test.58
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α22 := Type
  WEAK CONSTRAINTS:
   
  
