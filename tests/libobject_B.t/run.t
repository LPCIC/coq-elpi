  $ . ../setup-project.sh
  $ dune build test.vo
  Warning: in file test.v, library test_libobject_A is required
           from root elpi.tests and has not been found in the loadpath!
           [module-not-found,filesystem,default]
  File "./test.v", line 3, characters 0-48:
  Error: Cannot find a physical path bound to logical path
  test_libobject_A with prefix elpi.tests.
  
  [1]
