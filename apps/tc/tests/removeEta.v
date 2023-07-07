From elpi Require Import compiler.

Elpi Query TC_solver lp:{{
  remove-eta2 {{fun x => 3 x}} {{3}}
}}.

Elpi Query TC_solver lp:{{
  remove-eta2 {{fun x => 3 x x}} {{fun x => 3 x x}}
}}.

Elpi Query TC_solver lp:{{
  remove-eta2 {{fun x => 3}} {{fun x => 3}}
}}.

Elpi Query TC_solver lp:{{
  remove-eta2 {{fun x => 3 (fun y => 4 y) x}} {{3 4}}
}}.

Elpi Query TC_solver lp:{{
  remove-eta2 {{fun x => 3 (fun y => x y)}} {{3}}
}}.

Elpi Query TC_solver lp:{{
  remove-eta2 {{fun x y => 3 x y}} {{3}}
}}.

Elpi Query TC_solver lp:{{
  remove-eta2 {{fun x y => 3 y x}} {{fun x y => 3 y x}}
}}.

Elpi Query TC_solver lp:{{
  remove-eta2 {{fun x y => 3 _ y}} {{fun x => 3 _}}
}}.

Elpi Query TC_solver lp:{{
  remove-eta2 {{fun x y => 3 _ _}} {{fun x y => 3 _ _}}
}}.