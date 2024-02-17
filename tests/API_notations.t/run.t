  $ . ../setup-project.sh
  $ dune build test.vo
  «test.test.abbr»
  Query assignments:
    A = «test.test.abbr»
    _uvk_1_ = X0
    _uvk_2_ = c0 \
  X1 c0
    _uvk_3_ = c0 \ c1 \
  X2 c0 c1
  Syntactic constraints:
   {c0 c1} : decl c1 `y` (X1 c0), decl c0 `x` X0
     ?- evar (X2 c0 c1) (X3 c0 c1) (X2 c0 c1)  /* suspended on X2 */
   {c0 c1} : decl c1 `y` (X1 c0), decl c0 `x` X0
     ?- evar (X4 c0 c1) (sort (typ «test.test.3»)) (X3 c0 c1)  /* suspended on X4, X3 */
   {c0} : decl c0 `x` X0 ?- evar (X1 c0) (sort (typ «test.test.2»)) (X1 c0)  /* suspended on X1 */
   evar (X0) (sort (typ «test.test.1»)) (X0)  /* suspended on X0 */
  Universe constraints:
  UNIVERSES:
   {test.test.3 test.test.2 test.test.1} |= 
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α1
   α2
   α3
  WEAK CONSTRAINTS:
   
  
  Notation abbr _elpi_ctx_entry_2_was_x_ _elpi_ctx_entry_1_ :=
    (_elpi_ctx_entry_2_was_x_ = _elpi_ctx_entry_2_was_x_)
  Expands to: Notation test.test.abbr
  4 = 4
       : Prop
  Query assignments:
    _uvk_16_ = X0
    _uvk_17_ = c0 \
  X1 c0
    _uvk_18_ = c0 \ c1 \
  X2 c0 c1
  Syntactic constraints:
   {c0 c1} : decl c1 `y` (X1 c0), decl c0 `x` X0
     ?- evar (X2 c0 c1) (X3 c0 c1) (X2 c0 c1)  /* suspended on X2 */
   {c0 c1} : decl c1 `y` (X1 c0), decl c0 `x` X0
     ?- evar (X4 c0 c1) (sort (typ «test.test.6»)) (X3 c0 c1)  /* suspended on X4, X3 */
   {c0} : decl c0 `x` X0 ?- evar (X1 c0) (sort (typ «test.test.5»)) (X1 c0)  /* suspended on X1 */
   evar (X0) (sort (typ «test.test.4»)) (X0)  /* suspended on X0 */
  Universe constraints:
  UNIVERSES:
   {test.test.6 test.test.5 test.test.4} |= 
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α4
   α5
   α6
  WEAK CONSTRAINTS:
   
  
  Notation abbr2 _elpi_ctx_entry_1_was_x_ :=
    (fun H => _elpi_ctx_entry_1_was_x_ = _elpi_ctx_entry_1_was_x_)
  Expands to: Notation test.test.abbr2
  (fun _ : nat => 2 = 2) 3
       : Prop
  fun `H` X0 c0 \
   app [global (indt «eq»), X1 c0, fun `x` X2 c1 \ c1, fun `x` X2 c1 \ c1]
  Query assignments:
    Spilled_1 = «test.test.abbr2»
    T = fun `H` X0 c0 \
   app [global (indt «eq»), X1 c0, fun `x` X2 c1 \ c1, fun `x` X2 c1 \ c1]
    _uvk_31_ = X2
  Query assignments:
    Spilled_1 = «test.test.abbr2»
