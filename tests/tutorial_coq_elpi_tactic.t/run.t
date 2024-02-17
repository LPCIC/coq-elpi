  $ . ../setup-project.sh
  $ dune build test.vo
  Goal: 
  [decl c1 `y` (global (indt «nat»)), decl c0 `x` (global (indt «nat»))] 
  |- X0 c0 c1 : 
  app
   [global (indt «eq»), global (indt «nat»), 
    app
     [global (const «Nat.add»), c0, 
      app [global (indc «S»), global (indc «O»)]], c1]
  (I, 0)
  conj : forall [A B : Prop], A -> B -> A /\ B
  
  conj is not universe polymorphic
  Arguments conj [A B]%type_scope _ _
  Expands to: Constructor Coq.Init.Logic.conj
  (ex_intro (fun t : Prop => True /\ True /\ t) True (conj I (conj I I)))
  [int 1, str x, str a b, 
   trm
    (app
      [global (indt «eq»), X0, 
       app [global (indc «S»), global (indc «O»)], global (indc «O»)])]
  Using H ?p of type Q
  Using H ?p of type Q
  Using p of type P
  [trm c0, trm c3, trm (app [c2, c3])]
  found P
  found P /\ P
  Goal: [decl c0 `x` (global (indt «nat»))] |- X0 c0 : 
  app
   [global (indt «eq»), global (indt «nat»), 
    app
     [global (const «Nat.add»), c0, 
      app [global (indc «S»), global (indc «O»)]], global (indc «O»)]
  Proof state:
   {c0} : decl c0 `x` (global (indt «nat»))
     ?- evar (X1 c0) 
         (app
           [global (indt «eq»), global (indt «nat»), 
            app
             [global (const «Nat.add»), c0, 
              app [global (indc «S»), global (indc «O»)]], 
            global (indc «O»)]) (X0 c0)  /* suspended on X1, X0 */
  EVARS:
   ?X57==[x |- x + 1 = 0] (goal evar) {?Goal}
   ?X56==[ |- => fun x : nat => ?Goal] (goal evar)
   ?X55==[x |- => nat] (parameter A of eq)
   ?X54==[ |- => nat] (type of x)
  
  SHELF:||
  FUTURE GOALS STACK:
   ||
  
  Coq-Elpi mapping:
  RAW:
  ?X57 <-> c0 \ X1 c0
  ELAB:
  ?X57 <-> X0
  
  #goals = 2
  [nabla c0 \
    nabla c1 \
     seal
      (goal [decl c1 `Q` (sort prop), decl c0 `P` (sort prop)] (X0 c0 c1) c0 
        (X1 c0 c1) []), 
   nabla c0 \
    nabla c1 \
     seal
      (goal [decl c1 `Q` (sort prop), decl c0 `P` (sort prop)] (X2 c0 c1) c1 
        (X3 c0 c1) [])]
  (fun (P Q : Prop) (p : P) (q : Q) => conj ?Goal (conj ?Goal0 ?Goal1))
  (fun (P Q : Prop) (p : P) (q : Q) => conj ?Goal (conj ?Goal0 ?Goal))
  foo = 46
       : nat
  bar = (false :: nil)%list
       : list bool
  baz = (46%nat :: nil)%list
       : list nat
  File "./test.v", line 631, characters 0-22:
  Warning: x is already taken, Elpi will make a name up [lib,elpi,default]
  File "./test.v", line 741, characters 3-225:
  Warning: B is linear: name it _B (discard) or B_ (fresh variable)
  [elpi.typecheck,elpi,default]
  File "./test.v", line 741, characters 3-225:
  Warning: A is linear: name it _A (discard) or A_ (fresh variable)
  [elpi.typecheck,elpi,default]
  File "./test.v", line 741, characters 3-225:
  Warning: Ctx is linear: name it _Ctx (discard) or Ctx_ (fresh variable)
  [elpi.typecheck,elpi,default]
  File "./test.v", line 842, characters 3-280:
  Warning: G2 is linear: name it _G2 (discard) or G2_ (fresh variable)
  [elpi.typecheck,elpi,default]
  File "./test.v", line 842, characters 3-280:
  Warning: G1 is linear: name it _G1 (discard) or G1_ (fresh variable)
  [elpi.typecheck,elpi,default]
