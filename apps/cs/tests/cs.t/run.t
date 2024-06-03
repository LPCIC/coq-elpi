  $ DEPS="elpi elpi.apps.cs"
  $ . ../setup-project.sh
  $ dune build test.vo
  1
       : nat
  cs hook start
  cs hook got proj
  cs hook got structure
  cs hook got params & arg 1 0
  compile solver
  run solver
  
  found solution
  
  aha(id (A:=nat))
  eq_refl : {| sort := id (A:=nat) |} = id (A:=nat)
       : {| sort := id (A:=nat) |} = id (A:=nat)
  11
       : nat
  cs hook start
  cs hook got proj
  cs hook got structure
  cs hook got params & arg 1 1
  compile solver
  run solver
  
  found solution
  
  aha(id (A:=nat))
  eq_refl : {| sort := id (A:=nat) |} 1 = id 1
       : {| sort := id (A:=nat) |} 1 = id 1
  2
       : nat
  cs hook start
  cs hook got proj
  cs hook got structure
  cs hook got params & arg 1 0
  compile solver
  run solver
  
  solver failed
  
  cs hook start
  cs hook got proj
  cs hook start
  cs hook got proj
  cs hook got structure
  cs hook got params & arg 1 0
  compile solver
  run solver
  
  found solution
  
  aha(id (A:=nat))
  eq_refl : {| sort := id (A:=nat) |} = id1 nat
       : {| sort := id (A:=nat) |} = id1 nat
  3
       : nat
  cs hook start
  cs hook got proj
  cs hook start
  cs hook got proj
  cs hook got structure
  cs hook got params & arg 1 0
  compile solver
  run solver
  
  found solution
  
  aha(id (A:=nat))
  eq_refl : sort1 nat {| sort := id (A:=nat) |} = id (A:=nat)
       : sort1 nat {| sort := id (A:=nat) |} = id (A:=nat)
  4
       : nat
  cs hook start
  cs hook got proj
  cs hook start
  cs hook got proj
  cs hook start
  cs hook got proj
  cs hook got structure
  cs hook got params & arg 1 0
  compile solver
  run solver
  
  found solution
  
  aha(id (A:=nat))
  eq_refl : sort1 nat {| sort := id (A:=nat) |} = id1 nat
       : sort1 nat {| sort := id (A:=nat) |} = id1 nat
