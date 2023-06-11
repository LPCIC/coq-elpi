From elpi Require Import compiler.

Elpi Query TC_solver lp:{{
  remove-eta (fun _ _ (x\ app [{{3}}, x])) (app [{{3}}]),
  remove-eta (fun _ _ (x\ app [{{3}}, x, x])) (fun _ _ (x\ app [{{3}}, x, x])),
  remove-eta (fun _ _ (x\ {{3}})) (fun _ _ (x\ {{3}}))
}}.