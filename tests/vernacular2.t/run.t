  $ . ../setup-project.sh
  $ dune build test.vo
  Warning: in file test.v, library test_vernacular1 is required
           from root elpi and has not been found in the loadpath!
           [module-not-found,filesystem,default]
  File "./test.v", line 1, characters 0-47:
  Error: Cannot find a physical path bound to logical path
  test_vernacular1 with prefix elpi.
  
  [1]
