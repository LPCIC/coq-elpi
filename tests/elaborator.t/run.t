  $ . ../setup-project.sh
  $ dune build test.vo
  Warning: in file test.v, external file elpi_elaborator.elpi is required
           from root elpi_elpi and has not been found in the loadpath!
           [module-not-found,filesystem,default]
  File "./test.v", line 1, characters 0-63:
  Error: No LoadPath found for elpi_elpi.
  
  [1]
