  $ . ../setup-project.sh
  $ dune build test.vo
  Query assignments:
    GRnat = indt «nat»
    GRplus = const «Nat.add»
    GRs = indc «S»
  Query assignments:
    Bo = app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]
    C = «x»
    GR = const «x»
    Ty = global (indt «nat»)
    TyC = global (indt «nat»)
  Query assignments:
    Bo = fun `x` (global (indt «nat»)) c0 \ c0
    C = «f»
  Query assignments:
    Bo = fix `add` 0 
   (prod `n` (global (indt «nat»)) c0 \
     prod `m` (global (indt «nat»)) c1 \ global (indt «nat»)) c0 \
   fun `n` (global (indt «nat»)) c1 \
    fun `m` (global (indt «nat»)) c2 \
     match c1 (fun `n` (global (indt «nat»)) c3 \ global (indt «nat»)) 
      [c2, 
       fun `p` (global (indt «nat»)) c3 \
        app [global (indc «S»), app [c0, c3, c2]]]
    C = «Nat.add»
  The return type of m is: c0 \ c1 \
  fun `x` (global (indt «nat»)) c2 \
   fun `e` 
    (app [global (indt «eq»), global (indt «nat»), global (indc «O»), c2]) 
    c3 \ prod `_` (app [c1, global (indc «O»)]) c4 \ app [c1, c2]
  Query assignments:
    C = «m»
    RT = c0 \ c1 \
  fun `x` (global (indt «nat»)) c2 \
   fun `e` 
    (app [global (indt «eq»), global (indt «nat»), global (indc «O»), c2]) 
    c3 \ prod `_` (app [c1, global (indc «O»)]) c4 \ app [c1, c2]
  typ «test.test.6» < typ «test.test.7»
  Debug: Cannot enforce test.test.7 <= test.test.6 because test.test.6
  < test.test.7
  Query assignments:
    U = typ «test.test.6»
    U1 = typ «test.test.7»
  Universe constraints:
  UNIVERSES:
   {test.test.7 test.test.6} |= test.test.6 < test.test.7
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  (id b) is: app [fun `x` (sort (typ X0)) c0 \ c0, sort (typ X1)]
  (id a) is illtyped: 
  Illegal application: 
  The term "fun x : Type => x" of type "Type -> Type"
  cannot be applied to the term
   "Type" : "Type"
  This term has type "Type@{test.test.8+1}" which should be a subtype of
   "Type@{test.test.8}".
  (universe inconsistency: Cannot enforce test.test.8 < test.test.8 because
  test.test.8 = test.test.8)
  after typing (id b) is: 
  app
   [fun `x` (sort (typ «test.test.8»)) c0 \ c0, sort (typ «test.test.9»)] 
  : sort (typ «test.test.8»)
  Universe constraints: UNIVERSES:
                         {test.test.9 test.test.8} |= test.test.9 < test.test.8
                        ALGEBRAIC UNIVERSES:
                         {test.test.9 test.test.8}
                        FLEXIBLE UNIVERSES:
                         test.test.9
                         test.test.8
                        SORTS:
                         
                        WEAK CONSTRAINTS:
                         
                        
  Query assignments:
    A = sort (typ «test.test.8»)
    B = sort (typ «test.test.9»)
    ErrMsg = Illegal application: 
  The term "fun x : Type => x" of type "Type -> Type"
  cannot be applied to the term
   "Type" : "Type"
  This term has type "Type@{test.test.8+1}" which should be a subtype of
   "Type@{test.test.8}".
  (universe inconsistency: Cannot enforce test.test.8 < test.test.8 because
  test.test.8 = test.test.8)
    ID = fun `x` (sort (typ «test.test.8»)) c0 \ c0
    T = sort (typ «test.test.8»)
    U = «test.test.8»
    V = «test.test.9»
  Universe constraints:
  UNIVERSES:
   {test.test.9 test.test.8} |= test.test.9 < test.test.8
  ALGEBRAIC UNIVERSES:
   {test.test.9 test.test.8}
  FLEXIBLE UNIVERSES:
   test.test.9
   test.test.8
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  app
   [global (const «Nat.add»), 
    app [global (indc «S»), global (indc «O»)], 
    app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]] 
  = 
  app
   [global (const «Nat.add»), 
    app [global (indc «S»), global (indc «O»)], 
    app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]]
  app
   [global (const «Nat.add»), 
    app [global (indc «S»), global (indc «O»)], 
    app [global (indc «S»), global (indc «O»)]]
  Query assignments:
    S = indc «S»
  fun `x` (global (indt «nat»)) c0 \
   fun `x` (global (indt «nat»)) c1 \
    app [global (const «Nat.add»), c1, c0]
  fun `x` (global (indt «nat»)) c0 \
   fun `x` (global (indt «nat»)) c1 \
    app [global (const «Nat.add»), c1, c0]
  fun `a` (global (indt «nat»)) c0 \
   fun `b` (global (indt «nat»)) c1 \
    app [global (const «Nat.add»), c1, c0]
  Query assignments:
    X = c0 \ c1 \
  app [global (const «Nat.add»), c1, c0]
  fun `a` (global (indt «nat»)) c0 \
   fun `b` (global (indt «nat»)) c1 \
    app [global (indt «eq»), global (indt «nat»), c0, c1]
  indt «nat»
  indt «nat»
  before: 
  fun `ax` (global (indt «nat»)) c0 \
   fun `b` (global (indt «nat»)) c1 \
    app [global (indt «eq»), X0 c1, c0, c1]
  after: 
  fun `ax` (global (indt «nat»)) c0 \
   fun `b` (global (indt «nat»)) c1 \
    app [global (indt «eq»), global (indt «nat»), c0, c1]
  Query assignments:
    T = fun `ax` (global (indt «nat»)) c0 \
   fun `b` (global (indt «nat»)) c1 \
    app [global (indt «eq»), global (indt «nat»), c0, c1]
    _uvk_1_ = c0 \
  global (indt «nat»)
  Universe constraints:
  UNIVERSES:
   {test.test.11 test.test.10} |=
     test.test.11 < test.test.10
     Set <= test.test.11
     test.test.11 <= eq.u0
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α6 := Type
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    Bo = c0 \
  app
   [global (const «Nat.add»), c0, 
    app [global (indc «S»), global (indc «O»)]]
    N = `x`
    T = fun `x` (global (indt «nat»)) c0 \
   app
    [global (const «Nat.add»), c0, 
     app [global (indc «S»), global (indc «O»)]]
    Ty = global (indt «nat»)
  Query assignments:
    Bo = c0 \
  app
   [global (const «Nat.add»), c0, 
    app [global (indc «S»), global (indc «O»)]]
    N = `x`
    T = fun `x` (global (indt «nat»)) c0 \
   app
    [global (const «Nat.add»), c0, 
     app [global (indc «S»), global (indc «O»)]]
    Ty = global (indt «nat»)
  raw T = X0
  
  SHELF:
  FUTURE GOALS STACK:
   
  
  Coq-Elpi mapping:
  RAW:
  ELAB:
  
  --------------------------------
   evar (X1) (global (indt «nat»)) (X1)  /* suspended on X1 */
  EVARS:
   ?X11==[ |- nat] (internal placeholder) {?e0}
   ?X10==[ |- => nat] (internal placeholder)
  
  SHELF:
  FUTURE GOALS STACK:
   ?X11
  
  Coq-Elpi mapping:
  RAW:
  ?X11 <-> X1
  ELAB:
  ?X11 <-> X1
  
  Query assignments:
    T = X1
    _uvk_4_ = X1
  Syntactic constraints:
   evar (X1) (global (indt «nat»)) (X1)  /* suspended on X1 */
  Universe constraints:
  UNIVERSES:
   {test.test.12} |= Set <= test.test.12
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α7 := Type
  WEAK CONSTRAINTS:
   
  
  raw T = 
  fun `x` (global (indt «nat»)) c0 \
   app [global (const «Nat.add»), c0, X0 c0]
   {c0 c1} : decl c1 `x` (global (indt «nat»))
     ?- evar (X1 c1) (global (indt «nat»)) (X1 c1)  /* suspended on X1 */
  EVARS:
   ?X13==[x |- nat] (internal placeholder) {?e0}
   ?X12==[x |- => nat] (internal placeholder)
  
  SHELF:
  FUTURE GOALS STACK:
   ?X13
  
  Coq-Elpi mapping:
  RAW:
  ?X13 <-> c0 \ X1 c0
  ELAB:
  ?X13 <-> X1
  
  Query assignments:
    Bo = c0 \
  app [global (const «Nat.add»), c0, X1 c0]
    N = `x`
    T = fun `x` (global (indt «nat»)) c0 \
   app [global (const «Nat.add»), c0, X1 c0]
    Ty = global (indt «nat»)
    _uvk_9_ = c0 \
  X1 c0
  Syntactic constraints:
   {c0 c1} : decl c1 `x` (global (indt «nat»))
     ?- evar (X1 c1) (global (indt «nat»)) (X1 c1)  /* suspended on X1 */
  Universe constraints:
  UNIVERSES:
   {test.test.13} |= Set <= test.test.13
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α8 := Type
  WEAK CONSTRAINTS:
   
  
  Bo1 (not in pattern fragment) = 
  app
   [global (const «Nat.add»), 
    app [global (indc «S»), global (indc «O»)], 
    X0 (app [global (indc «S»), global (indc «O»)])]
  Bo1 before = 
  app
   [global (const «Nat.add»), 
    app [global (indc «S»), global (indc «O»)], 
    X0 (app [global (indc «S»), global (indc «O»)])]
  Bo1 after = 
  app
   [global (const «Nat.add»), 
    app [global (indc «S»), global (indc «O»)], X1]
  Query assignments:
    Bo = c0 \
  app [global (const «Nat.add»), c0, X1]
    Bo1 = app
   [global (const «Nat.add»), 
    app [global (indc «S»), global (indc «O»)], X1]
    N = `x`
    T = fun `x` (global (indt «nat»)) c0 \ app [global (const «Nat.add»), c0, X1]
    Ty = global (indt «nat»)
    _uvk_15_ = c0 \
  X1
  Syntactic constraints:
   evar (X1) (global (indt «nat»)) (X1)  /* suspended on X1 */
  Universe constraints:
  UNIVERSES:
   {test.test.14} |= Set <= test.test.14
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α9 := Type
  WEAK CONSTRAINTS:
   
  
  Query assignments:
    Bo = c0 \
  app [global (const «andb»), c0, X0 c0]
    Bo1 = app
   [global (const «andb»), app [global (indc «S»), global (indc «O»)], 
    X0 (app [global (indc «S»), global (indc «O»)])]
    Bo2 = app
   [global (const «andb»), 
    app
     [global (const «nat2bool»), 
      app [global (indc «S»), global (indc «O»)]], X1]
    N = `x`
    T = fun `x` (global (indt «nat»)) c0 \ app [global (const «andb»), c0, X0 c0]
    Ty = global (indt «nat»)
    _uvk_21_ = X0
  Syntactic constraints:
   evar (X2) (global (indt «bool»)) X1  /* suspended on X2, X1 */
