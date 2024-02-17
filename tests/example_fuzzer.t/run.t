  $ . ../setup-project.sh
  $ dune build test.vo
  DEBUG: attempt at fuzzing binary op: global (indc «PLUS»)
  DEBUG: attempt at fuzzing binary op: global (const «Nat.add»)
  DEBUG: attempt at fuzzing binary op: global (indc «AND»)
  DEBUG: fuzzed!
  DEBUG: attempt at fuzzing binary op: global (const «andb»)
  DEBUG: attempt at fuzzing binary op: global (indc «OR»)
  DEBUG: fuzzed!
  DEBUG: attempt at fuzzing binary op: global (const «orb»)
  DEBUG: attempt at fuzzing binary op: global (indc «EQ»)
  DEBUG: attempt at fuzzing binary op: global (const «Nat.eqb»)
  Inductive eval1 : forall T : ty, Exp T -> Val T -> Prop :=
      E_Num1 : forall n : nat, eval1 N (NUM n) (iNv n)
    | E_Bool1 : forall b : bool, eval1 B (BOOL b) (iBv b)
    | E_Plus1 : forall (e1 e2 : Exp N) (n1 n2 : nat),
                eval1 N e1 (iNv n1) ->
                eval1 N e2 (iNv n2) -> eval1 N (PLUS e1 e2) (iNv (n1 + n2))
    | E_AND1 : forall (e1 e2 : Exp B) (b1 b2 : bool),
               eval1 B e1 (iBv b1) ->
               eval1 B e2 (iBv b2) -> eval1 B (AND e1 e2) (iBv (b1 && b2))
    | E_OR1 : forall (e1 e2 : Exp B) (b1 b2 : bool),
              eval1 B e1 (iBv b1) ->
              eval1 B e2 (iBv b2) -> eval1 B (AND e1 e2) (iBv (b1 || b2))
    | E_EQ1 : forall (e1 e2 : Exp N) (n1 n2 : nat),
              eval1 N e1 (iNv n1) ->
              eval1 N e2 (iNv n2) -> eval1 B (EQ e1 e2) (iBv (Nat.eqb n1 n2)).
  
  Arguments eval1 T _ _
  Arguments E_Num1 n%nat_scope
  Arguments E_Bool1 b%bool_scope
  Arguments E_Plus1 e1 e2 (n1 n2)%nat_scope _ _
  Arguments E_AND1 e1 e2 (b1 b2)%bool_scope _ _
  Arguments E_OR1 e1 e2 (b1 b2)%bool_scope _ _
  Arguments E_EQ1 e1 e2 (n1 n2)%nat_scope _ _
