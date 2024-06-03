  $ . ../setup-project.sh
  $ dune build test.vo
  nabla c1 \
   seal
    (goal [decl c1 `P` (sort prop)] (app [global (const «id»), X0, X1]) 
      (prod `_` c1 c2 \ c1) 
      (app [global (const «id»), prod `_` c1 c2 \ c1, X2 c1]) [])
   {c0 c1 c2 c3} :
     decl c3 `w` c0, 
       decl c2 `h` 
        (app
          [global (indt «eq»), global (indt «nat»), global (const «o»), 
           global (const «m»)]), 
       decl c1 `x` (prod `y` c0 c4 \ sort (typ «test.test.2»)), 
       decl c0 `T` (sort (typ «test.test.1»))
     ?- evar (X0 c0 c1 c2 c3) 
         (prod `e` 
           (app
             [global (indt «eq»), sort (typ «test.test.2»), app [c1, c3], 
              sort (typ «test.test.3»)]) c4 \
           prod `j` (app [c1, c3]) c5 \
            app
             [global (indt «ex»), app [c1, c3], 
              fun `a` (app [c1, c3]) c6 \
               app [global (indt «eq»), app [c1, c3], c6, c6]]) 
         (X1 c0 c1 c2 c3)  /* suspended on X0, X1 */
  Goal: 
  
  n : nat
  m : nat
  o := m : nat
  T : Type
  x : T -> Type
  h : o = m
  w : T
  ======================
  (x w = Type -> x w -> exists a : x w, a = a)
   {c0 c1 c2 c3} :
     decl c3 `w` c0, 
       decl c2 `h` 
        (app
          [global (indt «eq»), global (indt «nat»), global (const «o»), 
           global (const «m»)]), 
       decl c1 `x` (prod `y` c0 c4 \ sort (typ «test.test.2»)), 
       decl c0 `T` (sort (typ «test.test.1»))
     ?- evar (X0 c0 c1 c2 c3) 
         (prod `e` 
           (app
             [global (indt «eq»), sort (typ «test.test.2»), app [c1, c3], 
              sort (typ «test.test.3»)]) c4 \
           prod `j` (app [c1, c3]) c5 \
            app
             [global (indt «ex»), app [c1, c3], 
              fun `a` (app [c1, c3]) c6 \
               app [global (indt «eq»), app [c1, c3], c6, c6]]) 
         (X1 c0 c1 c2 c3)  /* suspended on X0, X1 */
  Goal: 
  
  n : nat
  m : nat
  o := m : nat
  T : Type
  x : T -> Type
  h : o = m
  w : T
  ======================
  (x w = Type -> x w -> exists a : x w, a = a)
   {c0 c1 c2 c3 c4 c5} :
     decl c5 `j` (app [c1, c3]), 
       decl c4 `e` 
        (app
          [global (indt «eq»), sort (typ «test.test.2»), app [c1, c3], 
           sort (typ «test.test.3»)]), decl c3 `w` c0, 
       decl c2 `h` 
        (app
          [global (indt «eq»), global (indt «nat»), global (const «o»), 
           global (const «m»)]), 
       decl c1 `x` (prod `y` c0 c6 \ sort (typ «test.test.2»)), 
       decl c0 `T` (sort (typ «test.test.1»))
     ?- evar (X0 c0 c1 c2 c3 c4 c5) (app [c1, c3]) (X1 c0 c1 c2 c3 c4 c5)  /* suspended on X0, X1 */ 
   {c0 c1 c2 c3 c4 c5} :
     decl c5 `j` (app [c1, c3]), 
       decl c4 `e` 
        (app
          [global (indt «eq»), sort (typ «test.test.2»), app [c1, c3], 
           sort (typ «test.test.3»)]), decl c3 `w` c0, 
       decl c2 `h` 
        (app
          [global (indt «eq»), global (indt «nat»), global (const «o»), 
           global (const «m»)]), 
       decl c1 `x` (prod `y` c0 c6 \ sort (typ «test.test.2»)), 
       decl c0 `T` (sort (typ «test.test.1»))
     ?- evar (X2 c0 c1 c2 c3 c4 c5) 
         (app
           [global (indt «eq»), app [c1, c3], X1 c0 c1 c2 c3 c4 c5, 
            X1 c0 c1 c2 c3 c4 c5]) (X3 c0 c1 c2 c3 c4 c5)  /* suspended on X2, X3 */
  Goal: 
  
  n : nat
  m : nat
  o := m : nat
  T : Type
  x : T -> Type
  h : o = m
  w : T
  e : x w = Type
  j : x w
  ======================
  (?foo = ?foo)
   {c0 c1 c2 c3 c4 c5} :
     decl c5 `j` (app [c1, c3]), 
       decl c4 `e` 
        (app
          [global (indt «eq»), sort (typ «test.test.2»), app [c1, c3], 
           sort (typ «test.test.3»)]), decl c3 `w` c0, 
       decl c2 `h` 
        (app
          [global (indt «eq»), global (indt «nat»), global (const «o»), 
           global (const «m»)]), 
       decl c1 `x` (prod `y` c0 c6 \ sort (typ «test.test.2»)), 
       decl c0 `T` (sort (typ «test.test.1»))
     ?- evar (X0 c0 c1 c2 c3 c4 c5) (app [c1, c3]) (X1 c0 c1 c2 c3 c4 c5)  /* suspended on X0, X1 */ 
   {c0 c1 c2 c3 c4 c5} :
     decl c5 `j` (app [c1, c3]), 
       decl c4 `e` 
        (app
          [global (indt «eq»), sort (typ «test.test.2»), app [c1, c3], 
           sort (typ «test.test.3»)]), decl c3 `w` c0, 
       decl c2 `h` 
        (app
          [global (indt «eq»), global (indt «nat»), global (const «o»), 
           global (const «m»)]), 
       decl c1 `x` (prod `y` c0 c6 \ sort (typ «test.test.2»)), 
       decl c0 `T` (sort (typ «test.test.1»))
     ?- evar (X2 c0 c1 c2 c3 c4 c5) 
         (app
           [global (indt «eq»), app [c1, c3], X1 c0 c1 c2 c3 c4 c5, 
            X1 c0 c1 c2 c3 c4 c5]) (X3 c0 c1 c2 c3 c4 c5)  /* suspended on X2, X3 */
  Goal: 
  
  n : nat
  m : nat
  o := m : nat
  T : Type
  x : T -> Type
  h : o = m
  w : T
  e : x w = Type
  j : x w
  ======================
  (?foo = ?foo)
   evar (X0) (global (indt «nat»)) X1  /* suspended on X0, X1 */
  X0 global (indt «nat»)
   evar (X2) (global (indt «nat»)) X3  /* suspended on X2, X3 */
  hello
  eq_refl : one = 1
       : one = 1
  [(c4 \ app [c1, c2]), (c4 \ app [c0, c2]), (c4 \ c4), (c4 \
   prod `x0` (app [c0, c2]) c5 \
    prod `x1` (global (indt «nat»)) c6 \ sort (typ «test.test.16»))]
  [app
    [global (indt «eq»), global (indt «nat»), c2, 
     app [global (indc «S»), app [global (indc «S»), global (indc «O»)]]], 
   sort prop]
  1356
       : nat
  this 3 app [c4, X0 c0 c1 c2 c3 c4] 
  app [c3, app [c1, c2], global (const «a»)] foo.bar
  [trm c0, trm (app [global (const «Nat.add»), c0, c1])]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0 c1) (global (indt «True»)) (X1 c0 c1)  /* suspended on X0, X1 */
  [trm c0, trm (app [global (const «Nat.add»), X0 c0 c1, c1])]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X1 c0 c1) (global (indt «nat»)) (X0 c0 c1)  /* suspended on X1, X0 */ 
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X2 c0 c1) (global (indt «True»)) (X3 c0 c1)  /* suspended on X2, X3 */
  [trm c0, trm (app [global (const «Nat.add»), X0 c0 c1, c1])]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X1 c0 c1) (global (indt «True»)) (X2 c0 c1)  /* suspended on X1, X2 */
  [trm c0, trm c1]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0 c1) (global (indt «True»)) (X1 c0 c1)  /* suspended on X0, X1 */
  [trm (app [global (const «Nat.add»), c0, c1])]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0 c1) (global (indt «True»)) (X1 c0 c1)  /* suspended on X0, X1 */
  [trm (app [global (const «Nat.add»), X0 c0 c1, c1])]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X1 c0 c1) (global (indt «nat»)) (X0 c0 c1)  /* suspended on X1, X0 */ 
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X2 c0 c1) (global (indt «True»)) (X3 c0 c1)  /* suspended on X2, X3 */
  [trm (app [global (const «Nat.add»), X0 c0 c1, c1])]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X1 c0 c1) (global (indt «True»)) (X2 c0 c1)  /* suspended on X1, X2 */
  [trm (app [global (indc «O»), global (indc «O»)])]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0 c1) (global (indt «True»)) (X1 c0 c1)  /* suspended on X0, X1 */
  [trm c0]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0 c1) (global (indt «True»)) (X1 c0 c1)  /* suspended on X0, X1 */
  [int 1]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0 c1) (global (indt «True»)) (X1 c0 c1)  /* suspended on X0, X1 */
  [int -1]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0 c1) (global (indt «True»)) (X1 c0 c1)  /* suspended on X0, X1 */
  [str a]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0 c1) (global (indt «True»)) (X1 c0 c1)  /* suspended on X0, X1 */
  [str a]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0 c1) (global (indt «True»)) (X1 c0 c1)  /* suspended on X0, X1 */
  [str x]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0 c1) (global (indt «True»)) (X1 c0 c1)  /* suspended on X0, X1 */
  [trm (app [global (const «Nat.add»), c0, c1])]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0 c1) (global (indt «True»)) (X1 c0 c1)  /* suspended on X0, X1 */
  [trm (app [global (const «Nat.add»), X0 c0 c1, c1])]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X1 c0 c1) (global (indt «True»)) (X2 c0 c1)  /* suspended on X1, X2 */
  [trm (app [global (const «Nat.add»), X0 c0 c1, c1])]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X1 c0 c1) (global (indt «True»)) (X2 c0 c1)  /* suspended on X1, X2 */
  [trm c0]
   {c0 c1} :
     decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))
     ?- evar (X0 c0 c1) (global (indt «True»)) (X1 c0 c1)  /* suspended on X0, X1 */
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test.v", line 314, column 10, character 6765:), 
   attribute elpi.phase (leaf-str interp)]
  Entry binder_constr is
  [ LEFTA
    [ "exists2"; "'"; pattern LEVEL "0"; ":"; term LEVEL "200"; ","; term LEVEL
      "200"; "&"; term LEVEL "200"
    | "exists2"; "'"; pattern LEVEL "0"; ","; term LEVEL "200"; "&"; term LEVEL
      "200"
    | "exists2"; name; ":"; term LEVEL "200"; ","; term LEVEL "200"; "&"; term
      LEVEL "200"
    | "exists2"; name; ","; term LEVEL "200"; "&"; term LEVEL "200"
    | "exists"; "!"; open_binders; ","; term LEVEL "200"
    | "exists"; open_binders; ","; term LEVEL "200"
    | "forall"; open_binders; ","; term LEVEL "200"
    | "fun"; open_binders; "=>"; term LEVEL "200"
    | "let"; "fix"; fix_decl; "in"; term LEVEL "200"
    | "let"; "cofix"; cofix_body; "in"; term LEVEL "200"
    | "let"; "'"; pattern LEVEL "200"; ":="; term LEVEL "200"; "in"; term LEVEL
      "200"
    | "let"; "'"; pattern LEVEL "200"; ":="; term LEVEL "200"; case_type; "in";
      term LEVEL "200"
    | "let"; "'"; pattern LEVEL "200"; "in"; pattern LEVEL "200"; ":="; term
      LEVEL "200"; case_type; "in"; term LEVEL "200"
    | "let"; name; binders; let_type_cstr; ":="; term LEVEL "200"; "in"; term
      LEVEL "200"
    | "let"; [ "("; LIST0 name SEP ","; ")" | "()" ]; as_return_type; ":=";
      term LEVEL "200"; "in"; term LEVEL "200"
    | "if"; term LEVEL "200"; as_return_type; "then"; term LEVEL "200"; "else";
      term LEVEL "200"
    | "fix"; fix_decls
    | "cofix"; cofix_decls ] ]
  
  Entry constr is
  [ LEFTA
    [ "@"; global; univ_annot
    | term LEVEL "8" ] ]
  
  Entry lconstr is
  [ LEFTA
    [ term LEVEL "200" ] ]
  
  Entry term is
  [ "200" RIGHTA
    [  ]
  | "100" RIGHTA
    [ SELF; "<:"; term LEVEL "200"
    | SELF; "<<:"; term LEVEL "200"
    | SELF; ":>"; term LEVEL "200"
    | SELF; ":"; term LEVEL "200" ]
  | "99" RIGHTA
    [ SELF; "->"; term LEVEL "200" ]
  | "95" RIGHTA
    [ SELF; "<->"; NEXT ]
  | "90" RIGHTA
    [  ]
  | "85" RIGHTA
    [ SELF; "\\/"; term LEVEL "85" ]
  | "80" RIGHTA
    [ SELF; "/\\"; term LEVEL "80" ]
  | "75" RIGHTA
    [ "~"; term LEVEL "75" ]
  | "70" RIGHTA
    [ SELF; ">"; NEXT
    | SELF; ">="; NEXT
    | SELF; "<"; NEXT; "<="; NEXT
    | SELF; "<"; NEXT; "<"; NEXT
    | SELF; "<"; NEXT
    | SELF; "<="; NEXT; "<"; NEXT
    | SELF; "<="; NEXT; "<="; NEXT
    | SELF; "<="; NEXT
    | SELF; "<>"; NEXT; ":>"; NEXT
    | SELF; "<>"; NEXT
    | SELF; "="; NEXT; "="; NEXT
    | SELF; "="; NEXT; ":>"; NEXT
    | SELF; "="; NEXT ]
  | "60" RIGHTA
    [ SELF; "++"; term LEVEL "60"
    | SELF; "::"; term LEVEL "60" ]
  | "50" LEFTA
    [ SELF; "||"; NEXT
    | SELF; "-"; NEXT
    | SELF; "+"; NEXT ]
  | "40" LEFTA
    [ SELF; "&&"; NEXT
    | SELF; "/"; NEXT
    | SELF; "*"; NEXT ]
  | "35" RIGHTA
    [ "/"; term LEVEL "35"
    | "-"; term LEVEL "35" ]
  | "30" RIGHTA
    [ SELF; "^"; term LEVEL "30" ]
  | LEFTA
    [ IDENT "XX"; FIELD "xxx"; LIST0 arg ]
  | "10" LEFTA
    [ SELF; LIST1 arg
    | "@"; global; univ_annot; LIST0 NEXT
    | "@"; pattern_ident; LIST1 identref
    | binder_constr ]
  | "9" LEFTA
    [ ".."; term LEVEL "0"; ".." ]
  | "8" LEFTA
    [  ]
  | "1" LEFTA
    [ SELF; ".("; "@"; global; univ_annot; LIST0 (term LEVEL "9"); ")"
    | SELF; ".("; global; univ_annot; LIST0 arg; ")"
    | SELF; "%"; IDENT
    | SELF; "%_"; IDENT ]
  | "0" LEFTA
    [ "lib"; ":"; "@"; qualified_name
    | "lib"; ":"; qualified_name
    | QUOTATION "lp:"
    | "{"; "'"; pattern LEVEL "0"; "&"; term LEVEL "200"; "&"; term LEVEL
      "200"; "}"
    | "{"; "'"; pattern LEVEL "0"; "&"; term LEVEL "200"; "}"
    | "{"; "'"; pattern LEVEL "0"; ":"; term LEVEL "200"; "&"; term LEVEL
      "200"; "&"; term LEVEL "200"; "}"
    | "{"; "'"; pattern LEVEL "0"; ":"; term LEVEL "200"; "&"; term LEVEL
      "200"; "}"
    | "{"; "'"; pattern LEVEL "0"; ":"; term LEVEL "200"; "|"; term LEVEL
      "200"; "&"; term LEVEL "200"; "}"
    | "{"; "'"; pattern LEVEL "0"; ":"; term LEVEL "200"; "|"; term LEVEL
      "200"; "}"
    | "{"; "'"; pattern LEVEL "0"; "|"; term LEVEL "200"; "&"; term LEVEL
      "200"; "}"
    | "{"; "'"; pattern LEVEL "0"; "|"; term LEVEL "200"; "}"
    | "{"; term LEVEL "99"; "&"; term LEVEL "200"; "&"; term LEVEL "200"; "}"
    | "{"; term LEVEL "99"; "&"; term LEVEL "200"; "}"
    | "{"; term LEVEL "99"; ":"; term LEVEL "200"; "&"; term LEVEL "200"; "&";
      term LEVEL "200"; "}"
    | "{"; term LEVEL "99"; ":"; term LEVEL "200"; "&"; term LEVEL "200"; "}"
    | "{"; term LEVEL "99"; ":"; term LEVEL "200"; "|"; term LEVEL "200"; "&";
      term LEVEL "200"; "}"
    | "{"; term LEVEL "99"; ":"; term LEVEL "200"; "|"; term LEVEL "200"; "}"
    | "{"; term LEVEL "99"; "|"; term LEVEL "200"; "&"; term LEVEL "200"; "}"
    | "{"; term LEVEL "99"; "|"; term LEVEL "200"; "}"
    | "{"; term LEVEL "99"; "}"
    | IDENT "ltac"; ":"; "("; ltac_expr; ")"
    | "("; term LEVEL "200"; ","; term LEVEL "200"; ","; LIST1 (term LEVEL
      "200") SEP ","; ")"
    | "("; term LEVEL "200"; ","; term LEVEL "200"; ")"
    | "("; term LEVEL "200"; ")"
    | "{|"; record_declaration; '|}'
    | "`{"; term LEVEL "200"; "}"
    | "`("; term LEVEL "200"; ")"
    | NUMBER
    | atomic_constr
    | term_match
    | ident; fields; univ_annot
    | ident; univ_annot
    | string
    | test_array_opening; "["; "|"; array_elems; "|"; lconstr; type_cstr;
      test_array_closing; "|"; "]"; univ_annot ] ]
  
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test.v", line 325, column 12, character 7018:), 
   attribute elpi.phase (leaf-str interp)]
  skip int 1
  skip str 33
  skip trm (global (indt «bool»))
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test.v", line 325, column 12, character 7018:), 
   attribute elpi.phase (leaf-str interp)]
  skip int 1
  skip str 33
  skip trm (global (indt «bool»))
  nat -> bool -> True
       : Prop
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test.v", line 334, column 12, character 7204:), 
   attribute elpi.phase (leaf-str interp)]
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test.v", line 334, column 12, character 7204:), 
   attribute elpi.phase (leaf-str interp)]
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test.v", line 338, column 30, character 7305:), 
   attribute elpi.phase (leaf-str interp)]
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test.v", line 338, column 30, character 7305:), 
   attribute elpi.phase (leaf-str interp)]
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test.v", line 346, column 7, character 7481:), 
   attribute elpi.phase (leaf-str interp)]
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test.v", line 346, column 7, character 7481:), 
   attribute elpi.phase (leaf-str interp)]
  H
  goal [] (X0) (global (indt «True»)) X1 [trm (global (const «H»))]
  goal [] (X0) (global (indt «True»)) X1 
   [trm
     (app
       [global (indt «eq»), global (indt «True»), global (const «H»), 
        global (const «H»)])]
  goal [] (X0) (global (indt «True»)) X1 [trm (global (const «H»))]
  x1
       : nat
  w
       : nat
  File "./test.v", line 5, characters 3-155:
  Warning: Type is linear: name it _Type (discard) or Type_ (fresh variable)
  [elpi.typecheck,elpi,default]
