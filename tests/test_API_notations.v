From elpi Require Import elpi.

(***** Syndef *******************************)

Elpi Query lp:{{
    coq.notation.add-abbreviation "abbr" 2
      {{ fun x _ => x = x }} tt A,
    coq.say A
}}.

About abbr.
Check abbr 4 3.

Elpi Query lp:{{
  coq.notation.add-abbreviation "abbr2" 1
    {{ fun x _ => x = x }} tt _
}}.

About abbr2.
Check abbr2 2 3.

Elpi Query lp:{{
  coq.notation.abbreviation {coq.locate-abbreviation "abbr2"} [{{ fun x => x }}] T,
  coq.say T.
}}.

Elpi Query lp:{{
  coq.notation.abbreviation-body {coq.locate-abbreviation "abbr2"} 1
    (fun _ _ x\ fun _ _ _\ app[_,_,x,x]).
}}.

