  $ . ../setup-project.sh
  $ dune build test.vo
   {c0} : decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0) 
         (prod `_` (global (indt «bool»)) c1 \ global (indt «True»)) 
         (X1 c0)  /* suspended on X0, X1 */
  EVARS:
   ?X2==[x |- bool -> True] (goal evar) {?Goal}
   ?X1==[ |- => fun x : nat => ?Goal] (goal evar)
  
  SHELF:||
  FUTURE GOALS STACK:
   ||
  
  Coq-Elpi mapping:
  RAW:
  ?X2 <-> c0 \ X0 c0
  ELAB:
  ?X2 <-> X1
  
   {c0} : decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0) 
         (prod `_` (global (indt «bool»)) c1 \ global (indt «True»)) 
         (X1 c0)  /* suspended on X0, X1 */
  H
  [nabla c1 \
    seal
     (goal
       [decl c1 `H` 
         (prod `b` 
           (prod `b` (global (indt «bool»)) c2 \
             app [global (indt «eq»), global (indt «bool»), c2, c2]) c2 \
           global (indt «True»))] (X0 c1) 
       (prod `b` (global (indt «bool»)) c2 \
         app [global (indt «eq»), global (indt «bool»), c2, c2]) (X1 c1) [])]
  [str fun, str in, str as, int 4, str end, str match, str return, str =>, 
   str :, str :=, str {, str }, str ;, str ,, str |, str x, int 1, str H, 
   trm
    (fun `x` (global (indt «False»)) c0 \
      match c0 (fun `y` (global (indt «False»)) c1 \ global (indt «nat»)) 
       [])]
  Query assignments:
    T = sort (typ «test.test.3»)
    U = «test.test.3»
  Query assignments:
    U = «test.test.4»
  Universe constraints:
  UNIVERSES:
   {test.test.4} |= 
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    U = «foo»
  Query assignments:
    X = c0 \ c1 \ c2 \
  X0 c0 c1 c2
    _uvk_19_ = global (indt «nat»)
  Syntactic constraints:
   {c0 c1 c2 c3 c4 c5 c6} :
     decl c6 `z` (app [global (const «N»), c5]), 
       decl c5 `x` (global (indt «nat»)), 
       decl c4 `a` (global (indt «bool»))
     ?- evar (X0 c4 c5 c6) (X1 c4 c5 c6) (X0 c4 c5 c6)  /* suspended on X0 */
   {c0 c1 c2 c3 c4 c5 c6} :
     decl c6 `z` (app [global (const «N»), c5]), 
       decl c5 `x` (global (indt «nat»)), 
       decl c4 `a` (global (indt «bool»))
     ?- evar (X2 c4 c5 c6) (sort (typ «test.test.9»)) (X1 c4 c5 c6)  /* suspended on X2, X1 */
  Universe constraints:
  UNIVERSES:
   {test.test.9 test.test.8} |= Set <= test.test.8
                                test.test.8 <= test.test.8
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α3 := Type
   α4
  WEAK CONSTRAINTS:
   
  
  ----------------------------------
   {c0 c1} : decl c1 `a` (global (indt «bool»))
     ?- evar X0 (sort (typ «test.test.10»)) X1  /* suspended on X0, X1 */
   {c0 c1} : decl c1 `a` (global (indt «bool»)) ?- evar (X2 c1) X1 (X2 c1)  /* suspended on X2 */
  EVARS:
   ?X10==[ |- Type] (internal placeholder) {?elpi_evar}
   ?X9==[a |- ?elpi_evar] (internal placeholder) {?e0}
   ?X8==[a |- => ?elpi_evar] (internal placeholder)
  
  SHELF:
  FUTURE GOALS STACK:?X10
  ?X9
  
  Coq-Elpi mapping:
  RAW:
  ?X9 <-> c0 \ X2 c0
  ?X10 <-> X0
  ELAB:
  ?X9 <-> X2
  ?X10 <-> X1
  
  X2 c0 : X1
  Query assignments:
    TY = X1
    X = c0 \ c1 \
  X2 c0
  Syntactic constraints:
   {c0 c1} : decl c1 `a` (global (indt «bool»))
     ?- evar X0 (sort (typ «test.test.10»)) X1  /* suspended on X0, X1 */
   {c0 c1} : decl c1 `a` (global (indt «bool»)) ?- evar (X2 c1) X1 (X2 c1)  /* suspended on X2 */
  Universe constraints:
  UNIVERSES:
   {test.test.10} |= 
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α5
  WEAK CONSTRAINTS:
   
  
  Raw term: 
  app
   [global (const «add»), primitive (uint63 2000000003333002), 
    primitive (uint63 1)] 
  Nice term: add 2000000003333002 1 
  Red: 
  2000000003333003
  Raw term: 
  app
   [global (const «add»), primitive (float64 24000000000000), 
    primitive (float64 1)] 
  Nice term: 24000000000000 + 1 
  Red: 24000000000001
  Query assignments:
    C = «Nat.add»
    F = TODO
    T = app
   [fix `add` 0 
     (prod `n` (global (indt «nat»)) c0 \
       prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)) c0 \
     fun `n` (global (indt «nat»)) c1 \
      fun `m` (global (indt «nat»)) c2 \
       match c1 (fun `n` (global (indt «nat»)) c3 \ global (indt «nat»)) 
        [c2, 
         fun `p` (global (indt «nat»)) c3 \
          app [global (indc «S»), app [c0, c3, c2]]], 
    app [global (indc «S»), global (indc «O»)], 
    app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]
    T1 = app
   [global (const «Nat.add»), 
    app [global (indc «S»), global (indc «O»)], 
    app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]
    T2 = app
   [fix `plus` 0 
     (prod `n` (global (indt «nat»)) c0 \
       prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)) c0 \
     fun `n` (global (indt «nat»)) c1 \
      fun `m` (global (indt «nat»)) c2 \
       match c1 (fun `n` (global (indt «nat»)) c3 \ global (indt «nat»)) 
        [c2, 
         fun `p` (global (indt «nat»)) c3 \
          app [global (indc «S»), app [c0, c3, c2]]], 
    app [global (indc «S»), global (indc «O»)], 
    app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]
    _uvk_35_ = global (indt «nat»)
    _uvk_36_ = c0 \
  global (indt «nat»)
    _uvk_37_ = c0 \ c1 \
  global (indt «nat»)
    _uvk_38_ = c0 \
  global (indt «nat»)
    _uvk_39_ = c0 \ c1 \
  global (indt «nat»)
    _uvk_40_ = c0 \ c1 \ c2 \
  global (indt «nat»)
    _uvk_41_ = c0 \ c1 \ c2 \
  global (indt «nat»)
  Query assignments:
    C = «Nat.add»
    F = TODO
    T = app
   [fun `n` (global (indt «nat»)) c0 \
     fun `m` (global (indt «nat»)) c1 \
      match c0 (fun `n` (global (indt «nat»)) c2 \ global (indt «nat»)) 
       [c1, 
        fun `p` (global (indt «nat»)) c2 \
         app
          [global (indc «S»), 
           app
            [fix `add` 0 
              (prod `n` (global (indt «nat»)) c3 \
                prod `m` (global (indt «nat»)) c4 \ global (indt «nat»)) 
              c3 \
              fun `n` (global (indt «nat»)) c4 \
               fun `m` (global (indt «nat»)) c5 \
                match c4 
                 (fun `n` (global (indt «nat»)) c6 \ global (indt «nat»)) 
                 [c5, 
                  fun `p` (global (indt «nat»)) c6 \
                   app [global (indc «S»), app [c3, c6, c5]]], c2, c1]]], 
    app [global (indc «S»), global (indc «O»)], 
    app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]
    T1 = app
   [global (const «Nat.add»), 
    app [global (indc «S»), global (indc «O»)], 
    app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]
    T2 = app
   [fun `n` (global (indt «nat»)) c0 \
     fun `m` (global (indt «nat»)) c1 \
      match c0 (fun `n` (global (indt «nat»)) c2 \ global (indt «nat»)) 
       [c1, 
        fun `p` (global (indt «nat»)) c2 \
         app
          [global (indc «S»), 
           app
            [fix `plus` 0 
              (prod `n` (global (indt «nat»)) c3 \
                prod `m` (global (indt «nat»)) c4 \ global (indt «nat»)) 
              c3 \
              fun `n` (global (indt «nat»)) c4 \
               fun `m` (global (indt «nat»)) c5 \
                match c4 
                 (fun `n` (global (indt «nat»)) c6 \ global (indt «nat»)) 
                 [c5, 
                  fun `p` (global (indt «nat»)) c6 \
                   app [global (indc «S»), app [c3, c6, c5]]], c2, c1]]], 
    app [global (indc «S»), global (indc «O»)], 
    app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]
    _uvk_42_ = global (indt «nat»)
    _uvk_43_ = c0 \
  global (indt «nat»)
    _uvk_44_ = c0 \ c1 \
  global (indt «nat»)
    _uvk_45_ = c0 \ c1 \
  global (indt «nat»)
    _uvk_46_ = c0 \ c1 \ c2 \
  global (indt «nat»)
    _uvk_47_ = c0 \ c1 \ c2 \
  global (indt «nat»)
    _uvk_48_ = c0 \ c1 \ c2 \
  global (indt «nat»)
    _uvk_49_ = c0 \ c1 \ c2 \ c3 \
  global (indt «nat»)
    _uvk_50_ = c0 \ c1 \ c2 \ c3 \
  global (indt «nat»)
    _uvk_51_ = c0 \ c1 \ c2 \ c3 \
  global (indt «nat»)
    _uvk_52_ = c0 \ c1 \ c2 \ c3 \
  global (indt «nat»)
  Query assignments:
    C = «Nat.add»
    F = TODO
    T = match (app [global (indc «S»), global (indc «O»)]) 
   (fun `n` (global (indt «nat»)) c0 \ global (indt «nat»)) 
   [app [global (indc «S»), app [global (indc «S»), global (indc «O»)]], 
    fun `p` (global (indt «nat»)) c0 \
     app
      [global (indc «S»), 
       app
        [fix `add` 0 
          (prod `n` (global (indt «nat»)) c1 \
            prod `m` (global (indt «nat»)) c2 \ global (indt «nat»)) c1 \
          fun `n` (global (indt «nat»)) c2 \
           fun `m` (global (indt «nat»)) c3 \
            match c2 
             (fun `n` (global (indt «nat»)) c4 \ global (indt «nat»)) 
             [c3, 
              fun `p` (global (indt «nat»)) c4 \
               app [global (indc «S»), app [c1, c4, c3]]], c0, 
         app
          [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]]]
    T1 = app
   [global (const «Nat.add»), 
    app [global (indc «S»), global (indc «O»)], 
    app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]
    T2 = match (app [global (indc «S»), global (indc «O»)]) 
   (fun `_` (global (indt «nat»)) c0 \ global (indt «nat»)) 
   [app [global (indc «S»), app [global (indc «S»), global (indc «O»)]], 
    fun `p` (global (indt «nat»)) c0 \
     app
      [global (indc «S»), 
       app
        [fix `plus` 0 
          (prod `n` (global (indt «nat»)) c1 \
            prod `m` (global (indt «nat»)) c2 \ global (indt «nat»)) c1 \
          fun `n` (global (indt «nat»)) c2 \
           fun `m` (global (indt «nat»)) c3 \
            match c2 
             (fun `n` (global (indt «nat»)) c4 \ global (indt «nat»)) 
             [c3, 
              fun `p` (global (indt «nat»)) c4 \
               app [global (indc «S»), app [c1, c4, c3]]], c0, 
         app
          [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]]]
    _uvk_53_ = c0 \
  global (indt «nat»)
    _uvk_54_ = global (indt «nat»)
    _uvk_55_ = c0 \
  global (indt «nat»)
    _uvk_56_ = c0 \ c1 \
  global (indt «nat»)
    _uvk_57_ = c0 \ c1 \ c2 \
  global (indt «nat»)
    _uvk_58_ = c0 \ c1 \
  global (indt «nat»)
    _uvk_59_ = c0 \ c1 \ c2 \
  global (indt «nat»)
    _uvk_60_ = c0 \ c1 \ c2 \ c3 \
  global (indt «nat»)
    _uvk_61_ = c0 \ c1 \ c2 \ c3 \
  global (indt «nat»)
  Query assignments:
    C = «Nat.add»
    F = TODO
    T = app
   [global (indc «S»), 
    app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]
    T1 = app
   [global (const «Nat.add»), 
    app [global (indc «S»), global (indc «O»)], 
    app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]
    T2 = app
   [global (indc «S»), 
    app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]
  test.test.P.p1 1 global (const «P.x»)
  @P.p1
  X0 global (const «P.x»)
  P.p1 P.x
  some
   (fun `A` (sort (typ «P.foo.u0»)) c0 \
     fun `f` (app [global (indt «P.foo»), c0]) c1 \
      app [primitive (proj test.test.P.p1 1), c1])
  test.test.P.p2 2 global (const «P.x»)
  @P.p2
  X0 global (const «P.x»)
  P.p2 P.x
  some
   (fun `A` (sort (typ «P.foo.u0»)) c0 \
     fun `f` (app [global (indt «P.foo»), c0]) c1 \
      app [primitive (proj test.test.P.p1 1), c1])
  some (pglobal (const «toto») «test.test.19 test.test.20»)
  prod `T1` (sort (typ «test.test.19»)) c0 \
   prod `T2` (sort (typ «test.test.20»)) c1 \ prod `x` c0 c2 \ c0
  Query assignments:
    Body = some (pglobal (const «toto») «test.test.19 test.test.20»)
    C = «titi»
    Term = prod `T1` (sort (typ «test.test.19»)) c0 \
   prod `T2` (sort (typ «test.test.20»)) c1 \ prod `x` c0 c2 \ c0
  Universe constraints:
  UNIVERSES:
   {test.test.20 test.test.19} |= 
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  pglobal (const «toto») X0
  pglobal (const «toto») «u1 u2»
  toto
  Query assignments:
    Spilled_1 = toto
    _uvk_62_ = X0
    _uvk_63_ = «test.test.23 test.test.24»
  Universe constraints:
  UNIVERSES:
   {test.test.24 test.test.23} |= 
  ALGEBRAIC UNIVERSES:
   {test.test.24 test.test.23}
  FLEXIBLE UNIVERSES:
   test.test.24
   test.test.23
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  app
   [pglobal (const «t») X0, global (indt «nat»), 
    pglobal (const «fnat») X1]
  app
   [pglobal (const «t») «test.test.29», global (indt «nat»), 
    pglobal (const «fnat») «»]
  Query assignments:
    T = app
   [pglobal (const «t») «test.test.29», global (indt «nat»), 
    pglobal (const «fnat») «»]
    Ty = global (indt «nat»)
    _uvk_64_ = «test.test.29»
    _uvk_65_ = «»
  Universe constraints:
  UNIVERSES:
   {test.test.29} |= Set <= test.test.29
                     Set = test.test.29
  ALGEBRAIC UNIVERSES:
   {test.test.29}
  FLEXIBLE UNIVERSES:
   test.test.29 := Set
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    A4 = «test.test.36»
    A5 = «test.test.37»
    A6 = «test.test.38»
    A7 = «test.test.39»
    A8 = «test.test.40»
    Arity = prod `T` (sort (typ «test.test.30»)) c0 \ sort (typ «test.test.30»)
    Arity1 = prod `T` (sort (typ «test.test.31»)) c0 \ sort (typ «test.test.31»)
    Arity2 = prod `T` (sort (typ «test.test.32»)) c0 \ sort (typ «test.test.32»)
    Arity4 = prod `T` (sort (typ «test.test.36»)) c0 \ sort (typ «test.test.36»)
    Arity5 = prod `T` (sort (typ «test.test.37»)) c0 \ sort (typ «test.test.37»)
    B = «Build_F»
    B1 = «test.test.43»
    B2 = «test.test.44»
    BTy2 = prod `T` (sort (typ «test.test.42»)) c0 \
   prod `t` c0 c1 \ app [pglobal (indt «F») «test.test.42», c0]
    BTy3 = prod `T` (sort (typ «test.test.43»)) c0 \
   prod `t` c0 c1 \ app [pglobal (indt «F») «test.test.43», c0]
    BoN = none
    BoT = some
   (fun `T` (sort (typ «test.test.45»)) c0 \
     fun `f` (app [pglobal (indt «F») «test.test.45», c0]) c1 \
      match c1 
       (fun `f` (app [pglobal (indt «F») «test.test.45», c0]) c2 \ c0) 
       [fun `t` c0 c2 \ c2])
    BoT1 = some
   (fun `T` (sort (typ «test.test.46»)) c0 \
     fun `f` (app [pglobal (indt «F») «test.test.46», c0]) c1 \
      match c1 
       (fun `f` (app [pglobal (indt «F») «test.test.46», c0]) c2 \ c0) 
       [fun `t` c0 c2 \ c2])
    BoT2 = some
   (fun `T` (sort (typ «test.test.47»)) c0 \
     fun `f` (app [pglobal (indt «F») «test.test.47», c0]) c1 \
      match c1 
       (fun `f` (app [pglobal (indt «F») «test.test.47», c0]) c2 \ c0) 
       [fun `t` c0 c2 \ c2])
    BoT4 = some
   (fun `T` (sort (typ «test.test.49»)) c0 \
     fun `f` (app [pglobal (indt «F») «test.test.49», c0]) c1 \
      match c1 
       (fun `f` (app [pglobal (indt «F») «test.test.49», c0]) c2 \ c0) 
       [fun `t` c0 c2 \ c2])
    BoT5 = some
   (fun `T` (sort (typ «test.test.50»)) c0 \
     fun `f` (app [pglobal (indt «F») «test.test.50», c0]) c1 \
      match c1 
       (fun `f` (app [pglobal (indt «F») «test.test.50», c0]) c2 \ c0) 
       [fun `t` c0 c2 \ c2])
    BoT6 = some
   (fun `T` (sort (typ «test.test.64»)) c0 \
     fun `f` (app [pglobal (indt «F») «test.test.64», c0]) c1 \
      match c1 
       (fun `f` (app [pglobal (indt «F») «test.test.64», c0]) c2 \ c0) 
       [fun `t` c0 c2 \ c2])
    BoT7 = some
   (fun `T` (sort (typ «test.test.66»)) c0 \
     fun `f` (app [pglobal (indt «F») «test.test.66», c0]) c1 \
      match c1 
       (fun `f` (app [pglobal (indt «F») «test.test.66», c0]) c2 \ c0) 
       [fun `t` c0 c2 \ c2])
    C1 = «test.test.54»
    C2 = «test.test.55»
    C3 = «test.test.58»
    C4 = «test.test.59»
    C5 = «test.test.62»
    C6 = «test.test.63»
    D1 = «test.test.49»
    D2 = «test.test.50»
    D3 = «test.test.51»
    D4 = X0
    E5 = «test.test.66»
    E6 = «test.test.67»
    GRB = indc «Build_F»
    GRF = indt «F»
    GRn = const «n»
    GRt = const «t»
    I = «test.test.30»
    I2 = «test.test.41»
    I3 = «test.test.45»
    I4 = «»
    Ind = «F»
    K = [«Build_F»]
    KTys = [prod `T` (sort (typ «test.test.30»)) c0 \
    prod `t` c0 c1 \ app [pglobal (indt «F») «test.test.30», c0]]
    KTys1 = [prod `T` (sort (typ «test.test.31»)) c0 \
    prod `t` c0 c1 \ app [pglobal (indt «F») «test.test.31», c0]]
    KTys3 = [prod `T` (sort (typ «test.test.33»)) c0 \
    prod `t` c0 c1 \ app [pglobal (indt «F») «test.test.33», c0]]
    KTys4 = [prod `T` (sort (typ «test.test.36»)) c0 \
    prod `t` c0 c1 \ app [pglobal (indt «F») «test.test.36», c0]]
    KTys6 = [prod `T` (sort (typ «test.test.38»)) c0 \
    prod `t` c0 c1 \ app [pglobal (indt «F») «test.test.38», c0]]
    N = «n»
    T = «t»
    TyB = prod `T` (sort (typ «test.test.41»)) c0 \
   prod `t` c0 c1 \ app [pglobal (indt «F») «test.test.41», c0]
    TyB2 = prod `T` (sort (typ «test.test.56»)) c0 \
   prod `t` c0 c1 \ app [pglobal (indt «F») «test.test.56», c0]
    TyB3 = prod `T` (sort (typ «test.test.58»)) c0 \
   prod `t` c0 c1 \ app [pglobal (indt «F») «test.test.58», c0]
    TyF = prod `T` (sort (typ «test.test.30»)) c0 \ sort (typ «test.test.30»)
    TyF2 = prod `T` (sort (typ «test.test.52»)) c0 \ sort (typ «test.test.52»)
    TyF3 = prod `T` (sort (typ «test.test.54»)) c0 \ sort (typ «test.test.54»)
    TyN = global (indt «nat»)
    TyT = prod `T` (sort (typ «test.test.45»)) c0 \
   prod `f` (app [pglobal (indt «F») «test.test.45», c0]) c1 \ c0
    TyT1 = prod `T` (sort (typ «test.test.46»)) c0 \
   prod `f` (app [pglobal (indt «F») «test.test.46», c0]) c1 \ c0
    TyT3 = prod `T` (sort (typ «test.test.48»)) c0 \
   prod `f` (app [pglobal (indt «F») «test.test.48», c0]) c1 \ c0
    TyT4 = prod `T` (sort (typ «test.test.49»)) c0 \
   prod `f` (app [pglobal (indt «F») «test.test.49», c0]) c1 \ c0
    TyT5 = prod `T` (sort (typ «test.test.51»)) c0 \
   prod `f` (app [pglobal (indt «F») «test.test.51», c0]) c1 \ c0
    TyT6 = prod `T` (sort (typ «test.test.60»)) c0 \
   prod `f` (app [pglobal (indt «F») «test.test.60», c0]) c1 \ c0
    TyT7 = prod `T` (sort (typ «test.test.62»)) c0 \
   prod `f` (app [pglobal (indt «F») «test.test.62», c0]) c1 \ c0
    Tyt = prod `T` (sort (typ «test.test.45»)) c0 \
   prod `f` (app [pglobal (indt «F») «test.test.45», c0]) c1 \ c0
  Universe constraints:
  UNIVERSES:
   {test.test.67 test.test.66 test.test.65 test.test.64 test.test.63
    test.test.62 test.test.61 test.test.60 test.test.59 test.test.58
    test.test.57 test.test.56 test.test.55 test.test.54 test.test.53
    test.test.52 test.test.51 test.test.50 test.test.49 test.test.48
    test.test.47 test.test.46 test.test.45 test.test.44 test.test.43
    test.test.42 test.test.41 test.test.40 test.test.39 test.test.38
    test.test.37 test.test.36 test.test.35 test.test.34 test.test.33
    test.test.32 test.test.31 test.test.30} |= 
  ALGEBRAIC UNIVERSES:
   {test.test.45 test.test.44 test.test.43 test.test.42 test.test.41
    test.test.40 test.test.39 test.test.38 test.test.37 test.test.36
    test.test.35 test.test.34 test.test.33 test.test.32 test.test.31
    test.test.30}
  FLEXIBLE UNIVERSES:
   test.test.45
   test.test.44
   test.test.43
   test.test.42
   test.test.41
   test.test.40
   test.test.39
   test.test.38
   test.test.37
   test.test.36
   test.test.35
   test.test.34
   test.test.33
   test.test.32
   test.test.31
   test.test.30
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  «test.test.68» 
  parameter T explicit (sort (typ «test.test.68»)) c0 \
   record F (sort (typ «test.test.68»)) Build_F 
    (field [coercion off, canonical tt] t c0 c1 \ end-record)
  «test.test.68» 
  parameter T explicit (sort (typ «test.test.68»)) c0 \
   record F (sort (typ «test.test.68»)) Build_F 
    (field [coercion off, canonical tt] t c0 c1 \ end-record)
  parameter T explicit (sort (typ «test.test.69»)) c0 \
   record F (sort (typ «test.test.69»)) Build_F 
    (field [coercion off, canonical tt] t c0 c1 \ end-record)
  Query assignments:
    Decl = parameter T explicit (sort (typ «test.test.68»)) c0 \
   record F (sort (typ «test.test.68»)) Build_F 
    (field [coercion off, canonical tt] t c0 c1 \ end-record)
    Decl1 = parameter T explicit (sort (typ «test.test.68»)) c0 \
   record F (sort (typ «test.test.68»)) Build_F 
    (field [coercion off, canonical tt] t c0 c1 \ end-record)
    Decl2 = parameter T explicit (sort (typ «test.test.69»)) c0 \
   record F (sort (typ «test.test.69»)) Build_F 
    (field [coercion off, canonical tt] t c0 c1 \ end-record)
    GRF = indt «F»
    I = «test.test.68»
    Ind = «F»
  Universe constraints:
  UNIVERSES:
   {test.test.69 test.test.68} |= 
  ALGEBRAIC UNIVERSES:
   {test.test.69 test.test.68}
  FLEXIBLE UNIVERSES:
   test.test.69
   test.test.68
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  «test.test.70» «test.test.71»
  Universe constraints: UNIVERSES:
                         {test.test.71 test.test.70} |= 
                        ALGEBRAIC UNIVERSES:
                         {test.test.71 test.test.70}
                        FLEXIBLE UNIVERSES:
                         test.test.71
                         test.test.70
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  Universe constraints: UNIVERSES:
                         {test.test.71 test.test.70} |=
                           test.test.70 = test.test.71
                        ALGEBRAIC UNIVERSES:
                         {test.test.71 test.test.70}
                        FLEXIBLE UNIVERSES:
                         test.test.71
                         test.test.70 := test.test.71
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  Query assignments:
    GRF = indt «F»
    I1 = «test.test.70»
    I2 = «test.test.71»
  Universe constraints:
  UNIVERSES:
   {test.test.71 test.test.70} |= test.test.70 = test.test.71
  ALGEBRAIC UNIVERSES:
   {test.test.71 test.test.70}
  FLEXIBLE UNIVERSES:
   test.test.71
   test.test.70 := test.test.71
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  «test.test.72» «»
  Universe constraints: UNIVERSES:
                         {test.test.72} |= 
                        ALGEBRAIC UNIVERSES:
                         {test.test.72}
                        FLEXIBLE UNIVERSES:
                         test.test.72
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  different universe instance lengths
  Universe constraints: UNIVERSES:
                         {test.test.72} |= 
                        ALGEBRAIC UNIVERSES:
                         {test.test.72}
                        FLEXIBLE UNIVERSES:
                         test.test.72
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  Query assignments:
    E = different universe instance lengths
    GRF = indt «F»
    GRfnat = const «fnat»
    I1 = «test.test.72»
    I2 = «»
  Universe constraints:
  UNIVERSES:
   {test.test.72} |= 
  ALGEBRAIC UNIVERSES:
   {test.test.72}
  FLEXIBLE UNIVERSES:
   test.test.72
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    GRF = indt «F»
    I1 = «test.test.73»
    I2 = «test.test.73»
    U = «test.test.73»
    UL1 = [«test.test.73»]
  Universe constraints:
  UNIVERSES:
   {test.test.73} |= 
  ALGEBRAIC UNIVERSES:
   {test.test.73}
  FLEXIBLE UNIVERSES:
   test.test.73
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Cannot enforce test.test.74 = test.test.75 because test.test.74
  < test.test.75
  Query assignments:
    E = Cannot enforce test.test.74 = test.test.75 because test.test.74
  < test.test.75
    GRF = indt «F»
    I1 = «test.test.74»
    I2 = «test.test.75»
    L1 = «test.test.74»
    L2 = «test.test.75»
    U1 = «test.test.74»
    U2 = «test.test.75»
  Universe constraints:
  UNIVERSES:
   {test.test.75 test.test.74} |= test.test.74 < test.test.75
  ALGEBRAIC UNIVERSES:
   {test.test.75 test.test.74}
  FLEXIBLE UNIVERSES:
   test.test.75
   test.test.74
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Universe constraints: UNIVERSES:
                         {test.test.79 test.test.78} |=
                           test.test.78 < test.test.79
                        ALGEBRAIC UNIVERSES:
                         {test.test.79 test.test.78}
                        FLEXIBLE UNIVERSES:
                         test.test.79
                         test.test.78
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  Query assignments:
    GRF = indt «F2»
    I1 = «test.test.78»
    I2 = «test.test.79»
    L1 = «test.test.78»
    L2 = «test.test.79»
    U1 = «test.test.78»
    U2 = «test.test.79»
  Universe constraints:
  UNIVERSES:
   {test.test.79 test.test.78} |=
     test.test.78 < test.test.79
     test.test.78 <= test.test.79
  ALGEBRAIC UNIVERSES:
   {test.test.79 test.test.78}
  FLEXIBLE UNIVERSES:
   test.test.79
   test.test.78
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Universe constraints: UNIVERSES:
                         {test.test.81 test.test.80} |=
                           test.test.80 < test.test.81
                        ALGEBRAIC UNIVERSES:
                         {test.test.81}
                        FLEXIBLE UNIVERSES:
                         test.test.81
                         test.test.80
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  Cannot enforce test.test.81 = test.test.80 because test.test.80
  < test.test.81
  Query assignments:
    E = Cannot enforce test.test.81 = test.test.80 because test.test.80
  < test.test.81
    GRF = indt «F»
    I1 = «test.test.80»
    I2 = «test.test.81»
    L1 = «test.test.80»
    L2 = «test.test.81»
    U1 = «test.test.80»
    U2 = «test.test.81»
  Universe constraints:
  UNIVERSES:
   {test.test.81 test.test.80} |= test.test.80 < test.test.81
  ALGEBRAIC UNIVERSES:
   {test.test.81}
  FLEXIBLE UNIVERSES:
   test.test.81
   test.test.80
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    GR = indt «nat»
  Query assignments:
    GR = indt «F»
    I = «test.test.82»
  Universe constraints:
  UNIVERSES:
   {test.test.82} |= 
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   test.test.82
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    GR = indt «F»
  pglobal (indt «F») «test.test.84»
  «test.test.84»
  pglobal (indc «Build_F») «test.test.84»
  Query assignments:
    GR = indt «F»
    GR1 = indc «Build_F»
    I = «test.test.84»
    Spilled_1 = pglobal (indc «Build_F») «test.test.84»
    Spilled_2 = pglobal (indt «F») «test.test.84»
  Universe constraints:
  UNIVERSES:
   {test.test.84} |= 
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   test.test.84
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  «test.test.85 test.test.85»
  Query assignments:
    I = «test.test.85 test.test.85»
    U = «test.test.85»
  Universe constraints:
  UNIVERSES:
   {test.test.85} |= 
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Universe constraints: 
  ------------------
  Universe constraints: UNIVERSES:
                         {test.test.87 test.test.86} |=
                           test.test.86 < test.test.87
                        ALGEBRAIC UNIVERSES:
                         {test.test.87 test.test.86}
                        FLEXIBLE UNIVERSES:
                         test.test.87
                         test.test.86
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  Universe constraints: UNIVERSES:
                         {test.test.87 test.test.86} |=
                           test.test.86 < test.test.87
                        ALGEBRAIC UNIVERSES:
                         {test.test.87 test.test.86}
                        FLEXIBLE UNIVERSES:
                         test.test.87
                         test.test.86
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  Query assignments:
    Body = sort (typ «test.test.86»)
    LX = «test.test.86»
    LY = «test.test.87»
    Type = sort (typ «test.test.87»)
    UX = «test.test.86»
    UY = «test.test.87»
  Universe constraints:
  UNIVERSES:
   {test.test.87 test.test.86} |= test.test.86 < test.test.87
  ALGEBRAIC UNIVERSES:
   {test.test.87 test.test.86}
  FLEXIBLE UNIVERSES:
   test.test.87
   test.test.86
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  poly@{u u0} : Type@{u0}
  (* u u0 |= u < u0 *)
  
  poly is universe polymorphic
  poly is transparent
  Expands to: Constant test.test.poly
  poly@{Set
  test.test.88}
       : Type@{test.test.88}
  (* {test.test.88} |= Set < test.test.88 *)
  Box not a defined object.
  sort (typ «Set»)
  Query assignments:
    U = «test.test.89»
  Universe constraints:
  UNIVERSES:
   {test.test.89} |= Set = test.test.89
  ALGEBRAIC UNIVERSES:
   {test.test.89}
  FLEXIBLE UNIVERSES:
   test.test.89 := Set
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Inductive tree@{u} (A : Type@{u}) : Type@{max(Set,u)} :=
      leaf : A -> tree@{u} A | node : A -> list (tree@{u} A) -> tree@{u} A.
  (* u |= Set <= list.u0
          u <= list.u0 *)
  
  Arguments tree A%type_scope
  Arguments leaf A%type_scope _
  Arguments node A%type_scope _ _%list_scope
  parameter A explicit (sort (typ «test.test.98»)) c0 \
   inductive tree tt (arity (sort (typ «test.test.99»))) c1 \
    [constructor leaf (arity (prod `_` c0 c2 \ c1)), 
     constructor node 
      (arity
        (prod `_` c0 c2 \ prod `_` (app [global (indt «list»), c1]) c3 \ c1))]
  Universe constraints: UNIVERSES:
                         {test.test.103 test.test.102 test.test.101
                          test.test.100 test.test.99 test.test.98} |=
                           test.test.98 < test.test.100
                           test.test.99 < test.test.101
                           Set <= list.u0
                           Set <= test.test.99
                           Set <= test.test.103
                           test.test.98 <= list.u0
                           test.test.98 <= test.test.99
                           test.test.98 <= test.test.102
                           test.test.98 <= test.test.103
                           test.test.99 <= list.u0
                           test.test.99 <= test.test.102
                           test.test.99 <= test.test.103
                           test.test.102 <= test.test.99
                           test.test.103 <= test.test.99
                        ALGEBRAIC UNIVERSES:
                         {test.test.98}
                        FLEXIBLE UNIVERSES:
                         test.test.98
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  Query assignments:
    D = parameter A explicit (sort (typ «M.tree.u0»)) c0 \
   inductive tree tt (arity (sort (typ «M.tree.u1»))) c1 \
    [constructor leaf (arity (prod `_` c0 c2 \ c1)), 
     constructor node 
      (arity
        (prod `_` c0 c2 \ prod `_` (app [global (indt «list»), c1]) c3 \ c1))]
    I = «tree»
    _uvk_66_ = X0
  Universe constraints:
  UNIVERSES:
   {test.test.103 test.test.102 test.test.101 test.test.100} |=
     M.tree.u0 < test.test.100
     M.tree.u1 < test.test.101
     Set <= list.u0
     Set <= M.tree.u1
     Set <= test.test.103
     M.tree.u0 <= test.test.102
     M.tree.u0 <= test.test.103
     M.tree.u1 <= test.test.102
     M.tree.u1 <= test.test.103
     test.test.102 <= M.tree.u1
     test.test.103 <= M.tree.u1
  ALGEBRAIC UNIVERSES:
   {M.tree.u0}
  FLEXIBLE UNIVERSES:
   M.tree.u0
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  parameter A maximal (sort (typ «test.test.105»)) c0 \
   parameter x explicit (prod `_` c0 c1 \ c0) c1 \
    record c (sort prop) Build_c end-record
  File "./test.v", line 127, characters 0-34:
  Warning: Use of “Require” inside a module is fragile. It is not recommended
  to use this functionality in finished proof scripts.
  [require-in-module,fragile,default]
  File "./test.v", line 131, characters 0-34:
  Warning: Use of “Require” inside a module is fragile. It is not recommended
  to use this functionality in finished proof scripts.
  [require-in-module,fragile,default]
