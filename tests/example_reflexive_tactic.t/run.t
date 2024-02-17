  $ . ../setup-project.sh
  $ dune build test.vo
  normP :
  forall {T : Type} {e : T} {op : T -> T -> T} {gamma : list T} {t1 t2 : lang},
  (forall a b c : T, op a (op b c) = op (op a b) c) ->
  (forall a : T, op e a = a) ->
  (forall a : T, op a e = a) ->
  norm t1 = norm t2 -> interp T e op gamma t1 = interp T e op gamma t2
  
  normP is not universe polymorphic
  Arguments normP {T}%type_scope {e} {op}%function_scope 
    {gamma}%list_scope {t1 t2} (p1 p2 p3)%function_scope 
    H
  normP is transparent
  Expands to: Constant test.test.normP
  (fun x y z t : Z =>
   normP Z.add_assoc Z.add_0_l Z.add_0_r
     (eq_refl
      <:
      norm (add (add (var 0) (var 1)) (add (add (var 2) zero) (var 3))) =
      norm (add (add (var 0) (add (var 1) (var 2))) (var 3))))
  Debug: In environment
  x, y, z, t : Z
  Unable to unify "var 1" with "var 0".
