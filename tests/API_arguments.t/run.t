  $ . ../setup-project.sh
  $ dune build test.vo
  Query assignments:
    I = const «imp»
  X2.imp : forall (T : Type) (x : T), x = x -> Prop
  
  X2.imp is not universe polymorphic
  Arguments X2.imp T%type_scope x _
  Expands to: Constant test.test.X2.imp
  Query assignments:
    Spilled_1 = const «foo»
  foo 3
       : nat
  Query assignments:
    Spilled_1 = const «f»
    Spilled_2 = const «f»
    Spilled_3 = const «f»
    Spilled_4 = const «f»
    Spilled_5 = const «f»
  f : forall [S : Type], S -> Prop
  
  f is not universe polymorphic
  Arguments f [S]%type_scope _
    (where some original arguments have been renamed)
  f is transparent
  Expands to: Constant test.test.f
  f (S:=bool * bool)
       : bool * bool -> Prop
  Query assignments:
    Spilled_1 = const «f»
  f : forall [S : Type], S -> Prop
  
  f is not universe polymorphic
  Arguments f [S]%type_scope / _
    (where some original arguments have been renamed)
  The reduction tactics unfold f when applied to 1 argument
  f is transparent
  Expands to: Constant test.test.f
  f (S:=bool * bool)
       : bool * bool -> Prop
       = fun x : bool => x = x
       : bool -> Prop
