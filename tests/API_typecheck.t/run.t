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
  c2
  global (indt «nat»)
  z
  nat
  Query assignments:
    Spilled_1 = c0 \ c1 \ c2 \
  nat
    Spilled_2 = c0 \ c1 \ c2 \
  z
    T = global (indt «nat»)
  c2
  global (indt «nat»)
  z
  nat
  Query assignments:
    Spilled_1 = c0 \ c1 \ c2 \
  nat
    Spilled_2 = c0 \ c1 \ c2 \
  z
    T = global (indt «nat»)
  Illegal application (Non-functional construction): 
  The expression "Prop" of type "Type"
  cannot be applied to the term
   "Prop" : "Type"
  Query assignments:
    E = Illegal application (Non-functional construction): 
  The expression "Prop" of type "Type"
  cannot be applied to the term
   "Prop" : "Type"
  Unable to unify "bool" with "nat".
  Query assignments:
    Msg = Unable to unify "bool" with "nat".
  Query assignments:
    Cons = global (indc «cons»)
    GRCons = indc «cons»
    GRList = indt «list»
    GRNat = indt «nat»
    GRNil = indc «nil»
    GRZero = indc «O»
    L = app
   [global (indc «cons»), global (indt «nat»), global (indc «O»), 
    app [global (indc «nil»), global (indt «nat»)]]
    LE = app
   [global (indc «cons»), global (indt «nat»), global (indc «O»), 
    app [global (indc «nil»), global (indt «nat»)]]
    List = global (indt «list»)
    Nat = global (indt «nat»)
    Nil = global (indc «nil»)
    Zero = global (indc «O»)
  Universe constraints:
  UNIVERSES:
   {test.test.4 test.test.3 test.test.2 test.test.1} |=
     test.test.3 < test.test.2
     test.test.4 < test.test.1
     Set <= test.test.3
     Set <= test.test.4
     test.test.3 <= list.u0
     test.test.4 <= list.u0
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α1 := Type
   α2 := Type
  WEAK CONSTRAINTS:
   
  
  global (indt «nat»)
  Query assignments:
    T = global (indt «nat»)
    _uvk_5_ = global (indt «nat»)
    _uvk_6_ = global (indt «nat»)
  Universe constraints:
  UNIVERSES:
   {test.test.9 test.test.8 test.test.7 test.test.6 test.test.5} |=
     Set < test.test.7
     test.test.8 < test.test.6
     test.test.9 < test.test.5
     Set <= test.test.8
     Set <= test.test.9
     test.test.8 <= list.u0
     test.test.9 <= list.u0
  ALGEBRAIC UNIVERSES:
   {}
  FLEXIBLE UNIVERSES:
   
  SORTS:
   α3 := Type
   α4 := Type
   α5 := Type
  WEAK CONSTRAINTS:
   
  
  «test.test.10»
  Query assignments:
    U = «test.test.10»
  Universe constraints:
  UNIVERSES:
   {test.test.10} |= Set <= test.test.10
  ALGEBRAIC UNIVERSES:
   {test.test.10}
  FLEXIBLE UNIVERSES:
   test.test.10
  SORTS:
   
  WEAK CONSTRAINTS:
   
  
  Unable to unify "Set" with "Prop" (universe inconsistency: Cannot enforce Set
  <= Prop).
  Query assignments:
    E = Unable to unify "Set" with "Prop" (universe inconsistency: Cannot enforce Set
  <= Prop).
