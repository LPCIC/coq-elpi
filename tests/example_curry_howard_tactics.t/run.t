  $ . ../setup-project.sh
  $ dune build test.vo
  goal X0 c0 c1 c2 c3 is
   
  [decl c3 `H` (app [global (const «lt»), c0, c1]), 
   decl c2 `z` (global (indt «nat»)), decl c1 `y` (global (indt «nat»)), 
   decl c0 `x` (global (indt «nat»))] 
  -------
   
  prod `_` (app [global (const «lt»), c1, c2]) c4 \
   app [global (const «lt»), c0, c2]
  3
