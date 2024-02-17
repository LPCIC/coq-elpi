  $ . ../setup-project.sh
  $ dune build test.vo
  synterp [str X]
  interp [str X]
  synterp [int 1]
  interp [int 1]
  synterp [trm _]
  interp [trm (app [global (indc «S»), global (indc «O»)])]
  synterp 
  [const-decl x (some _) 
    (parameter P explicit _ c0 \ parameter Q explicit _ c1 \ arity _)]
  interp 
  [const-decl x 
    (some
      (fun `P` (global (indt «bool»)) c0 \
        fun `Q` (global (indt «bool»)) c1 \ global (indc «O»))) 
    (parameter P explicit (global (indt «bool»)) c0 \
      parameter Q explicit (global (indt «bool»)) c1 \
       arity (global (indt «nat»)))]
  synterp 
  [const-decl x none 
    (parameter P explicit _ c0 \ parameter Q explicit _ c1 \ arity _)]
  interp 
  [const-decl x none 
    (parameter P explicit (global (indt «bool»)) c0 \
      parameter Q explicit (global (indt «bool»)) c1 \
       arity (global (indt «nat»)))]
  synterp 
  [indt-decl
    (parameter P explicit _ c0 \
      parameter Q explicit _ c1 \
       record x _ K 
        (field [coercion off, canonical tt] f1 _ c2 \
          field [coercion off, canonical tt] f2 _ c3 \ end-record))]
  interp 
  [indt-decl
    (parameter P explicit (global (indt «bool»)) c0 \
      parameter Q explicit (global (indt «bool»)) c1 \
       record x (sort (typ «Set»)) K 
        (field [coercion off, canonical tt] f1 (global (indt «nat»)) c2 \
          field [coercion off, canonical tt] f2 
           (app [global (indt «eq»), global (indt «nat»), c2, c2]) c3 \
           end-record))]
  synterp 
  [indt-decl
    (parameter P explicit _ c0 \
      inductive x tt (parameter Q explicit _ c1 \ arity _) c1 \
       [constructor K (parameter Q explicit _ c2 \ arity _), 
        constructor R (parameter Q explicit _ c2 \ arity _)])]
  interp 
  [indt-decl
    (parameter P explicit (global (indt «bool»)) c0 \
      inductive x tt 
       (parameter Q explicit (global (indt «bool»)) c1 \
         arity (prod `_` (global (indt «nat»)) c2 \ sort (typ «Set»))) c1 \
       [constructor K 
         (parameter Q explicit (global (indt «bool»)) c2 \
           arity
            (prod `_` (global (indt «nat»)) c3 \
              app
               [c1, c2, 
                app
                 [global (indc «S»), 
                  app
                   [global (indc «S»), 
                    app [global (indc «S»), global (indc «O»)]]]])), 
        constructor R 
         (parameter Q explicit (global (indt «bool»)) c2 \
           arity
            (prod `w` (global (indt «bool»)) c3 \
              app [c1, c2, app [global (indc «S»), global (indc «O»)]]))])]
  synterp 
  [ctx-decl
    (context-item A explicit _ none c0 \
      context-item B explicit _ none c1 \ context-end)]
  interp 
  [ctx-decl
    (context-item A explicit (global (indt «nat»)) none c0 \
      context-item B explicit (global (indt «bool»)) none c1 \ context-end)]
  synterp [str X]
  interp [str X]
  synterp [int 1]
  interp [int 1]
  synterp [trm _]
  interp [trm (app [global (indc «S»), global (indc «O»)])]
  synterp 
  [const-decl x (some _) 
    (parameter P explicit _ c0 \ parameter Q explicit _ c1 \ arity _)]
  interp 
  [const-decl x 
    (some
      (fun `P` (global (indt «bool»)) c0 \
        fun `Q` (global (indt «bool»)) c1 \ global (indc «O»))) 
    (parameter P explicit (global (indt «bool»)) c0 \
      parameter Q explicit (global (indt «bool»)) c1 \
       arity (global (indt «nat»)))]
  synterp 
  [const-decl x none 
    (parameter P explicit _ c0 \ parameter Q explicit _ c1 \ arity _)]
  interp 
  [const-decl x none 
    (parameter P explicit (global (indt «bool»)) c0 \
      parameter Q explicit (global (indt «bool»)) c1 \
       arity (global (indt «nat»)))]
  synterp 
  [indt-decl
    (parameter P explicit _ c0 \
      parameter Q explicit _ c1 \
       record x _ K 
        (field [coercion off, canonical tt] f1 _ c2 \
          field [coercion off, canonical tt] f2 _ c3 \ end-record))]
  interp 
  [indt-decl
    (parameter P explicit (global (indt «bool»)) c0 \
      parameter Q explicit (global (indt «bool»)) c1 \
       record x (sort (typ «Set»)) K 
        (field [coercion off, canonical tt] f1 (global (indt «nat»)) c2 \
          field [coercion off, canonical tt] f2 
           (app [global (indt «eq»), global (indt «nat»), c2, c2]) c3 \
           end-record))]
  synterp 
  [indt-decl
    (parameter P explicit _ c0 \
      inductive x tt (parameter Q explicit _ c1 \ arity _) c1 \
       [constructor K (parameter Q explicit _ c2 \ arity _), 
        constructor R (parameter Q explicit _ c2 \ arity _)])]
  interp 
  [indt-decl
    (parameter P explicit (global (indt «bool»)) c0 \
      inductive x tt 
       (parameter Q explicit (global (indt «bool»)) c1 \
         arity (prod `_` (global (indt «nat»)) c2 \ sort (typ «Set»))) c1 \
       [constructor K 
         (parameter Q explicit (global (indt «bool»)) c2 \
           arity
            (prod `_` (global (indt «nat»)) c3 \
              app
               [c1, c2, 
                app
                 [global (indc «S»), 
                  app
                   [global (indc «S»), 
                    app [global (indc «S»), global (indc «O»)]]]])), 
        constructor R 
         (parameter Q explicit (global (indt «bool»)) c2 \
           arity
            (prod `w` (global (indt «bool»)) c3 \
              app [c1, c2, app [global (indc «S»), global (indc «O»)]]))])]
  synterp 
  [ctx-decl
    (context-item A explicit _ none c0 \
      context-item B explicit _ none c1 \ context-end)]
  interp 
  [ctx-decl
    (context-item A explicit (global (indt «nat»)) none c0 \
      context-item B explicit (global (indt «bool»)) none c1 \ context-end)]
  a : nat
  
  a is not universe polymorphic
  a is transparent
  Expands to: Constant test.test.X.a
  Module X := Struct Definition a : nat. End
  
  Module A := Struct Definition a : nat. End
  
  a
       : nat
  L= [p 1]
