  $ . ../setup-project.sh
  $ dune build test.vo 2>&1 | sed '/The module is/s/Module[0-9]*/ModuleXX/'
  Hello [str world!]
  Hello [int 46]
  Hello [str there]
  Hello [str my, str friend]
  Hello [str this.is.a.qualified.name]
  Hello 
  [trm
    (app
      [global (indt «eq»), global (indt «nat»), global (indc «O»), 
       app [global (indc «S»), global (indc «O»)]])]
  Hello 
  [const-decl test 
    (some
      (app
        [global (indt «eq»), global (indt «nat»), global (indc «O»), 
         app [global (indc «S»), global (indc «O»)]])) (arity (sort prop))]
  Hello 
  [indt-decl
    (record test (sort (typ «Set»)) Build_test 
      (field [coercion off, canonical tt] f1 (global (indt «nat»)) c0 \
        field [coercion off, canonical tt] f2 
         (app
           [global (indt «eq»), global (indt «nat»), c0, 
            app [global (indc «S»), global (indc «O»)]]) c1 \ end-record))]
  The type of 
  app
   [global (indt «eq»), global (indt «nat»), 
    app [global (indc «S»), global (indc «O»)], global (indc «O»)] is 
  sort prop
  1 = true
       : Prop
  T= 
  app
   [global (indt «eq»), X0, app [global (indc «S»), global (indc «O»)], 
    global (indc «true»)]
  T1= 
  app
   [global (indt «eq»), global (indt «nat»), 
    app [global (indc «S»), global (indc «O»)], 
    app [global (const «bool2nat»), global (indc «true»)]]
  Ty= sort prop
  nK_bool = 2
       : nat
  nK_False = 0
       : nat
  Inductive tree' (A : Set) : Set :=
      leaf' : tree' A | node' : tree' A -> A -> tree' A -> tree' A.
  
  Arguments tree' A%type_scope
  Arguments leaf' A%type_scope
  Arguments node' A%type_scope _ _ _
  bob is 24 years old
  alice is 21 years old
  bob is 24 years old
  alice is 21 years old
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test.v", line 609, column 31, character 17326:), 
   attribute elpi.phase (leaf-str interp), attribute this (leaf-str ), 
   attribute more (node [attribute stuff (leaf-str 33)])]
  options= 
  [get-option elpi.test yes, get-option elpi.str some-string, 
   get-option elpi.loc File "./test.v", line 642, column 31, character 18163:, 
   get-option elpi.phase interp, get-option this tt, get-option more.stuff 33]
  33 tt
  That is all folks!
  going from source to target via plane
  synterp x := some _
  interp x := 
  some
   (app [global (indc «S»), app [global (indc «S»), global (indc «O»)]])
  The module is «test.test.ModuleXX»
  Box.Box.Box.Box.foo = fun n : nat => n + 2
       : nat -> nat
  
  Arguments Box.Box.Box.Box.foo n%nat_scope
  Module NextModule2 := Struct  End
  
  File "./test.v", line 609, characters 2-24:
  Warning: This command does not support these attributes: more, this.
  [unsupported-attributes,parsing,default]
  File "./test.v", line 642, characters 2-24:
  Warning: This command does not support these attributes: more, this.
  [unsupported-attributes,parsing,default]
  File "./test.v", line 643, characters 7-14:
  Warning: This command does not support this attribute: unknown.
  [unsupported-attributes,parsing,default]
