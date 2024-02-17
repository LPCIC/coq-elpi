  $ . ../setup-project.sh
  $ dune build test.vo
  foo =
  {f1 : Type & {f2 : f1 -> Type & forall t : f1, f2 t -> bool}}
       : Type
  mk_foo =
  fun (f1 : Type) (f2 : f1 -> Type) (f3 : forall t : f1, f2 t -> bool) =>
  existT (fun f4 : Type => {f5 : f4 -> Type & forall t : f4, f5 t -> bool}) f1
    (existT (fun f4 : f1 -> Type => forall t : f1, f4 t -> bool) f2 f3)
       : forall (f1 : Type) (f2 : f1 -> Type),
         (forall t : f1, f2 t -> bool) -> foo
  
  Arguments mk_foo f1%type_scope (f2 f3)%function_scope
