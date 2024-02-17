  $ . ../setup-project.sh
  $ dune build test.vo
  Warning: in file test.v, library test_API is required
           from root elpi and has not been found in the loadpath!
           [module-not-found,filesystem,default]
  File "./test.v", line 3, characters 0-27:
  Error: Cannot find a physical path bound to logical path
  test_API with prefix elpi.
  
  [1]
