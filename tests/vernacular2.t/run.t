  $ . ../setup-project.sh
  $ dune build test2.vo
  test2
  test1
  str hello
  test1
  too many arguments
  test1
  str hello my
  str Dear
  test1
  too many arguments
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test1.v", line 49, column 5, character 1005:), 
   attribute elpi.phase (leaf-str interp), attribute foo (leaf-str bar)]
  [get-option foo bar]
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test1.v", line 53, column 0, character 1039:), 
   attribute elpi.phase (leaf-str interp), attribute foo (leaf-str bar), 
   attribute poly (leaf-str )]
  [get-option foo bar, get-option poly tt]
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test1.v", line 54, column 0, character 1067:), 
   attribute elpi.phase (leaf-str interp), attribute foo (leaf-str bar), 
   attribute poly (leaf-str ), 
   attribute suppa (node [attribute duppa (leaf-str )])]
  [get-option foo bar, get-option poly tt]
  Query assignments:
    X = 3
  app [global (const «Nat.mul»), X0, X1] type
  File "./test1.v", line 48, characters 2-11:
  Warning: This command does not support this attribute: foo.
  [unsupported-attributes,parsing,default]
  test1
  str hello
  str x
  test1
  too many arguments
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test2.v", line 12, column 24, character 366:), 
   attribute elpi.phase (leaf-str interp), 
   attribute fwd_compat_attr (leaf-str )]
  [attribute elpi.test (leaf-str yes), 
   attribute elpi.str (leaf-str some-string), 
   attribute elpi.loc 
    (leaf-loc File "./test2.v", line 13, column 0, character 371:), 
   attribute elpi.phase (leaf-str interp), 
   attribute fwd_compat_attr (leaf-str )]
  File "./test2.v", line 7, characters 2-17:
  Warning: This command does not support this attribute: fwd_compat_attr.
  [unsupported-attributes,parsing,default]
  File "./test2.v", line 8, characters 2-17:
  Warning: This command does not support this attribute: fwd_compat_attr.
  [unsupported-attributes,parsing,default]
  File "./test2.v", line 9, characters 2-17:
  Warning: This command does not support this attribute: fwd_compat_attr.
  [unsupported-attributes,parsing,default]
  File "./test2.v", line 10, characters 2-17:
  Warning: This command does not support this attribute: fwd_compat_attr.
  [unsupported-attributes,parsing,default]
  File "./test2.v", line 11, characters 2-17:
  Warning: This command does not support this attribute: fwd_compat_attr.
  [unsupported-attributes,parsing,default]
  File "./test2.v", line 12, characters 2-17:
  Warning: This command does not support this attribute: fwd_compat_attr.
  [unsupported-attributes,parsing,default]
