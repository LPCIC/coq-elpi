  $ . ../setup-project.sh
  $ dune build test.vo
  Query assignments:
    BO = fix `add` 0 
   (prod `n` (global (indt «nat»)) c0 \
     prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)) c0 \
   fun `n` (global (indt «nat»)) c1 \
    fun `m` (global (indt «nat»)) c2 \
     match c1 (fun `n` (global (indt «nat»)) c3 \ global (indt «nat»)) 
      [c2, 
       fun `p` (global (indt «nat»)) c3 \
        app [global (indc «S»), app [c0, c3, c2]]]
    GR = «Nat.add»
    TY = prod `n` (global (indt «nat»)) c0 \
   prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)
  fix X0 0 
   (prod `n` (global (indt «nat»)) c0 \
     prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)) c0 \
   fun `n` (global (indt «nat»)) c1 \
    fun `m` (global (indt «nat»)) c2 \
     match c1 (fun `n` (global (indt «nat»)) c3 \ X1 c2 c3) 
      [c2, fun `p` (X2 c1 c2) c3 \ app [c0, c3, c2]]
  fix X0 0 
   (prod `n` (global (indt «nat»)) c0 \
     prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)) c0 \
   fun `n` (global (indt «nat»)) c1 \
    fun `m` (global (indt «nat»)) c2 \
     match c1 (fun `n` (global (indt «nat»)) c3 \ global (indt «nat»)) 
      [c2, fun `p` (X3 c1 c2) c3 \ app [c0, c3, c2]]
  Query assignments:
    BO1 = fix X0 0 
   (prod `n` (global (indt «nat»)) c0 \
     prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)) c0 \
   fun `n` (global (indt «nat»)) c1 \
    fun `m` (global (indt «nat»)) c2 \
     match c1 (fun `n` (global (indt «nat»)) c3 \ global (indt «nat»)) 
      [c2, fun `p` (X3 c1 c2) c3 \ app [c0, c3, c2]]
    GR = «Nat.add»
    TY = prod `n` (global (indt «nat»)) c0 \
   prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)
    _uvk_1_ = c0 \ c1 \
  global (indt «nat»)
    _uvk_2_ = c0 \ c1 \
  X3 c0 c1
  Syntactic constraints:
   {c0 c1} :
     decl c1 `m` (global (indt «nat»)), decl c0 `n` (global (indt «nat»))
     ?- evar (X3 c0 c1) (sort (typ «test.test.2»)) (X3 c0 c1)  /* suspended on X3 */
  Universe constraints:
  UNIVERSES:
   {test.test.3 test.test.2 test.test.1} |= Set <= test.test.3
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   test.test.3
  SORTS:
   α1
   α2
  WEAK CONSTRAINTS:
   
  
  fun `v` 
   (app
     [global (indt «Vector.t»), global (indt «nat»), 
      app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]) 
   c0 \
   match c0 
    (fun `_` (X0 c0) c1 \
      fun `v` (app [global (indt «Vector.t»), X1 c0 c1, X2 c0 c1]) c2 \
       X3 c1 c2) 
    [global (indc «O»), 
     fun `_` (X4 c0) c1 \
      fun `_` (X5 c0 c1) c2 \
       fun `_` (X6 c0 c1 c2) c3 \
        app [global (indc «S»), global (indc «O»)]]
  fun `v` 
   (app
     [global (indt «Vector.t»), global (indt «nat»), 
      app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]) 
   c0 \
   match c0 
    (fun `_` (X7 c0) c1 \
      fun `v` 
       (app [global (indt «Vector.t»), global (indt «nat»), X8 c0 c1]) c2 \
       global (indt «nat»)) 
    [global (indc «O»), 
     fun `_` (X9 c0) c1 \
      fun `_` (X10 c0 c1) c2 \
       fun `_` (X11 c0 c1 c2) c3 \
        app [global (indc «S»), global (indc «O»)]]
  Query assignments:
    T = fun `v` 
   (app
     [global (indt «Vector.t»), global (indt «nat»), 
      app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]) 
   c0 \
   match c0 
    (fun `_` (X7 c0) c1 \
      fun `v` 
       (app [global (indt «Vector.t»), global (indt «nat»), X8 c0 c1]) c2 \
       global (indt «nat»)) 
    [global (indc «O»), 
     fun `_` (X9 c0) c1 \
      fun `_` (X10 c0 c1) c2 \
       fun `_` (X11 c0 c1 c2) c3 \
        app [global (indc «S»), global (indc «O»)]]
    _uvk_10_ = c0 \ c1 \
  global (indt «nat»)
    _uvk_11_ = c0 \
  X9 c0
    _uvk_12_ = c0 \ c1 \
  X10 c0 c1
    _uvk_13_ = c0 \ c1 \ c2 \
  X11 c0 c1 c2
    _uvk_7_ = c0 \
  X7 c0
    _uvk_8_ = c0 \ c1 \
  global (indt «nat»)
    _uvk_9_ = c0 \ c1 \
  X8 c0 c1
  Syntactic constraints:
   {c0 c1 c2} :
     decl c2 `y0` (X10 c0 c1), decl c1 `y` (X9 c0), 
       decl c0 `v` 
        (app
          [global (indt «Vector.t»), global (indt «nat»), 
           app
            [global (indc «S»), 
             app [global (indc «S»), global (indc «O»)]]])
     ?- evar (X11 c0 c1 c2) (sort (typ «test.test.10»)) (X11 c0 c1 c2)  /* suspended on X11 */
   {c0 c1} :
     decl c1 `y` (X9 c0), 
       decl c0 `v` 
        (app
          [global (indt «Vector.t»), global (indt «nat»), 
           app
            [global (indc «S»), 
             app [global (indc «S»), global (indc «O»)]]])
     ?- evar (X10 c0 c1) (sort (typ «test.test.9»)) (X10 c0 c1)  /* suspended on X10 */
   {c0} :
     decl c0 `v` 
      (app
        [global (indt «Vector.t»), global (indt «nat»), 
         app
          [global (indc «S»), app [global (indc «S»), global (indc «O»)]]])
     ?- evar (X9 c0) (sort (typ «test.test.8»)) (X9 c0)  /* suspended on X9 */
   {c0 c1} :
     decl c1 `y` (X7 c0), 
       decl c0 `v` 
        (app
          [global (indt «Vector.t»), global (indt «nat»), 
           app
            [global (indc «S»), 
             app [global (indc «S»), global (indc «O»)]]])
     ?- evar (X8 c0 c1) (X12 c0 c1) (X8 c0 c1)  /* suspended on X8 */
   {c0 c1} :
     decl c1 `y` (X7 c0), 
       decl c0 `v` 
        (app
          [global (indt «Vector.t»), global (indt «nat»), 
           app
            [global (indc «S»), 
             app [global (indc «S»), global (indc «O»)]]])
     ?- evar (X13 c0 c1) (sort (typ «test.test.6»)) (X12 c0 c1)  /* suspended on X13, X12 */
   {c0} :
     decl c0 `v` 
      (app
        [global (indt «Vector.t»), global (indt «nat»), 
         app
          [global (indc «S»), app [global (indc «S»), global (indc «O»)]]])
     ?- evar (X7 c0) (sort (typ «test.test.4»)) (X7 c0)  /* suspended on X7 */
  Universe constraints:
  UNIVERSES:
   {test.test.12 test.test.11 test.test.10 test.test.9 test.test.8 test.test.7
    test.test.6 test.test.5 test.test.4} |=
     test.test.11 < test.test.5
     Set <= Vector.t.u0
     Set <= test.test.11
     Set <= test.test.12
     test.test.11 <= Vector.t.u0
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   test.test.12
  SORTS:
   α3
   α4 := Type
   α5
   α6
   α7
   α8
   α9
  WEAK CONSTRAINTS:
   
  
  3
  Query assignments:
    X = 3
  fun `x` X0 c0 \ app [X1, c0]
  Query assignments:
    X = X1
    Y = fun `x` X0 c0 \ app [X1, c0]
    _uvk_34_ = X0
  fun `r` (global (indt «nat»)) c0 \
   fun `p` 
    (prod `y` (global (indt «nat»)) c1 \
      app
       [global (indt «eq»), global (indt «nat»), c1, global (indc «O»)]) 
    c1 \
    fun `q` (global (indt «bool»)) c2 \
     prod `y` (global (indt «nat»)) c3 \
      app
       [global (indt «eq»), global (indt «nat»), c3, global (indc «O»)]
  Query assignments:
    Spilled_1 = c0 \ c1 \ c2 \
  prod `y` (global (indt «nat»)) c3 \
   app [global (indt «eq»), global (indt «nat»), c3, global (indc «O»)]
    X = fun `r` (global (indt «nat»)) c0 \
   fun `p` 
    (prod `y` (global (indt «nat»)) c1 \
      app
       [global (indt «eq»), global (indt «nat»), c1, global (indc «O»)]) 
    c1 \
    fun `q` (global (indt «bool»)) c2 \
     prod `y` (global (indt «nat»)) c3 \
      app
       [global (indt «eq»), global (indt «nat»), c3, global (indc «O»)]
  fun u : nat =>
  {| val := oval u; Sub := Ord u; Sub_rect := inlined_sub_rect |}
       : forall u : nat, is_SUB nat (fun x : nat => leq x u) (ord u)
  Query assignments:
    GR = indc «Ord»
    K = global (indc «Ord»)
    T = fun `u` X0 c0 \
   app
    [global (indc «SubType»), X1 c0, X2 c0, X3 c0, 
     app [global (const «oval»), c0], X4 c0, 
     fun `K` (X5 c0) c1 \
      fun `K_S` (X6 c0 c1) c2 \
       fun `u` (X7 c0 c1 c2) c3 \
        match c3 (fun `u0` (X8 c1 c2 c3) c4 \ app [c1, c4]) 
         [fun `x` (X9 c1 c2 c3) c4 \
           fun `Px` (X10 c1 c2 c3 c4) c5 \ app [c2, c4, c5]]]
    T1 = fun `u` (global (indt «nat»)) c0 \
   app
    [global (indc «SubType»), global (indt «nat»), 
     fun `x` (global (indt «nat»)) c1 \ app [global (const «leq»), c1, c0], 
     app [global (indt «ord»), c0], app [global (const «oval»), c0], 
     app [global (indc «Ord»), c0], 
     fun `K` 
      (prod `x` (app [global (indt «ord»), c0]) c1 \ sort (typ «is_SUB.u2»)) 
      c1 \
      fun `K_S` 
       (prod `x` (global (indt «nat»)) c2 \
         prod `Px` 
          (app
            [global (indt «eq»), global (indt «bool»), 
             app
              [fun `x` (global (indt «nat»)) c3 \
                app [global (const «leq»), c3, c0], c2], 
             global (indc «true»)]) c3 \
          app [c1, app [global (indc «Ord»), c0, c2, c3]]) c2 \
       fun `u0` (app [global (indt «ord»), c0]) c3 \
        match c3 
         (fun `xxx` (app [global (indt «ord»), c0]) c4 \ app [c1, c4]) 
         [fun `x` (global (indt «nat»)) c4 \
           fun `Px` 
            (app
              [global (indt «eq»), global (indt «bool»), 
               app [global (const «leq»), c4, c0], global (indc «true»)]) 
            c5 \ app [c2, c4, c5]]]
    _uvk_35_ = X0
    _uvk_36_ = X1
    _uvk_37_ = X2
    _uvk_38_ = X3
    _uvk_39_ = X4
    _uvk_40_ = X5
    _uvk_41_ = X6
    _uvk_42_ = X7
    _uvk_43_ = X8
    _uvk_44_ = X9
    _uvk_45_ = X10
    _uvk_46_ = global (indt «nat»)
    _uvk_47_ = c0 \
  global (indt «nat»)
    _uvk_48_ = c0 \
  fun `x` (global (indt «nat»)) c1 \ app [global (const «leq»), c1, c0]
    _uvk_49_ = c0 \
  app [global (indt «ord»), c0]
    _uvk_50_ = c0 \
  app [global (const «oval»), c0]
    _uvk_51_ = c0 \
  fun `K` 
   (prod `x` (app [global (indt «ord»), c0]) c1 \ sort (typ «is_SUB.u2»)) 
   c1 \
   fun `K_S` 
    (prod `x` (global (indt «nat»)) c2 \
      prod `Px` 
       (app
         [global (indt «eq»), global (indt «bool»), 
          app
           [fun `x` (global (indt «nat»)) c3 \
             app [global (const «leq»), c3, c0], c2], global (indc «true»)]) 
       c3 \ app [c1, app [global (indc «Ord»), c0, c2, c3]]) c2 \
    fun `u0` (app [global (indt «ord»), c0]) c3 \
     match c3 (fun `xxx` (app [global (indt «ord»), c0]) c4 \ app [c1, c4]) 
      [fun `x` (global (indt «nat»)) c4 \
        fun `Px` 
         (app
           [global (indt «eq»), global (indt «bool»), 
            app [global (const «leq»), c4, c0], global (indc «true»)]) c5 \
         app [c2, c4, c5]]
  Universe constraints:
  UNIVERSES:
   {test.test.28 test.test.27} |=
     Set <= is_SUB.u0
     Set <= is_SUB.u1
     Set <= test.test.27
     is_SUB.u2 <= test.test.28
  ALGEBRAIC UNIVERSES:
   {test.test.28 test.test.27}
  FLEXIBLE UNIVERSES:
   test.test.28
   test.test.27
  SORTS:
   α22 := Type
   α23 := Type
  WEAK CONSTRAINTS:
   
  
  1
       : nat
