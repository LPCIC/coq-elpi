  $ . ../setup-project.sh
  $ dune build test.vo
  z
       : nat
  it = elpi_subproof
       : True
  it : True
  
  it is not universe polymorphic
  it is transparent
  Expands to: Constant test.test.it
  elpi_subproof = I
       : True
  elpi_subproof : True
  
  elpi_subproof is not universe polymorphic
  elpi_subproof is opaque
  Expands to: Constant test.test.elpi_subproof
  Closed under the global context
