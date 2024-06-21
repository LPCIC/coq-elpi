  $ DEPS="elpi elpi.apps.cs"
  $ . ../setup-project.sh
  $ dune build test.vo
  File "dune", line 6, characters 0-60:
  6 | (coq.theory
  7 |  (name test)
  8 |  (theories elpi elpi elpi.apps.cs))
  1
       : nat
  cs hook start
  cs hook got proj
  cs hook got structure
  cs hook got params & arg 1 0
  compile solver
  run solver
  
  found solution
  
  ahaid
  eq_refl : {| sort := id |} = id
       : {| sort := id |} = id
  11
       : nat
  cs hook start
  cs hook got proj
  cs hook got structure
  cs hook got params & arg 1 1
  compile solver
  run solver
  
  found solution
  
  ahaid
  eq_refl : {| sort := id |} 1 = id 1
       : {| sort := id |} 1 = id 1
  File "./test.v", line 18, characters 0-21:
  Error:
  The following term contains unresolved implicit arguments:
    id
  More precisely: 
  - ?A: Cannot infer the implicit parameter A of id whose type is "Type".
  
  [1]
