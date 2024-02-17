  $ . ../setup-project.sh
  $ dune build test.vo
  f =
  fun (b : bool) (t : r) =>
  let q := negb b in
  fix rec (l1 l2 : list t) {struct l1} : bool :=
    match l1 with
    | nil => match l2 with
             | nil => b
             | (_ :: _)%list => q
             end
    | (x :: xs)%list =>
        match l2 with
        | nil => q
        | (y :: ys)%list => (op t x y && rec xs ys)%bool
        end
    end
       : bool -> forall t : r, list t -> list t -> bool
  
  Arguments f b%bool_scope t (l1 l2)%list_scope
  expanded_f =
  fun (b : bool) (T : Type) =>
  let X := T in
  fun op : T -> X -> bool =>
  let q := negb b in
  fix rec (l1 l2 : list T) {struct l1} : bool :=
    match l1 with
    | nil => match l2 with
             | nil => b
             | (_ :: _)%list => q
             end
    | (x :: xs)%list =>
        match l2 with
        | nil => q
        | (y :: ys)%list => (op x y && rec xs ys)%bool
        end
    end
       : bool -> forall T : Type, (T -> T -> bool) -> list T -> list T -> bool
  
  Arguments expanded_f b%bool_scope T%type_scope op%function_scope
    (l1 l2)%list_scope
  expanded_g =
  fun T : Type =>
  let X := T in
  fun (op : T -> X -> bool) (l s : list T) (h : bool) =>
  (forall (x : T) (y : X), op x y = false) /\ expanded_f true T op l s = h
       : forall T : Type, (T -> T -> bool) -> list T -> list T -> bool -> Prop
  
  Arguments expanded_g T%type_scope op%function_scope 
    (l s)%list_scope h%bool_scope
