  $ . ../setup-project.sh
  $ dune build test.vo
  Warning: in file test.v, library test_link_order1 is required
           from root elpi.tests and has not been found in the loadpath!
           [module-not-found,filesystem,default]
  File "./test.v", line 2, characters 0-48:
  Error: Cannot find a physical path bound to logical path
  test_link_order1 with prefix elpi.tests.
  
  [1]
