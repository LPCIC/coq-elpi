DECLARE PLUGIN "elpi"

open Stdarg
open Ltac_plugin

VERNAC COMMAND EXTEND Elpi CLASSIFIED AS SIDEFF
| [ "Elpi" "Run" string(s) ] -> [ Coq_elpi.exec s ]
| [ "Elpi" "Init" string_list(s) ] -> [ Coq_elpi.init s ]
| [ "Elpi" "Accumulate" "File" string_list(s) ] -> [ Coq_elpi.load_files s ]
| [ "Elpi" "Accumulate" "Files" string_list(s) ] -> [ Coq_elpi.load_files s ]
| [ "Elpi" "Accumulate" string(s) ] -> [ Coq_elpi.load_string s ]
(* | [ "Elpi" "Load" string(s) ] -> [ Coq_elpi.load_string s ] *)
END

let pr_string _ _ _ (s : string) = Pp.str s

open Pcoq
open Pcoq.Constr

ARGUMENT EXTEND elpi
    PRINTED BY pr_string
 [ "xxxxxxx" ] -> [ "" ]
END

let () = Coq_elpi.is_coq_string := (fun x -> Genarg.(has_type x (glbwit wit_elpi)))
let () = Coq_elpi.get_coq_string := (fun x -> Genarg.(out_gen (glbwit wit_elpi) x))

open Compat

GEXTEND Gram
  GLOBAL: operconstr;

  operconstr: LEVEL "0"
    [ [ "lp"; ":"; id = IDENT ->
          let arg = Genarg.in_gen (Genarg.rawwit wit_elpi) id in
          Constrexpr.CHole (!@loc, None, Misctypes.IntroAnonymous, Some arg) ] 
    | [ "lp"; ":"; s = STRING -> 
          let arg = Genarg.in_gen (Genarg.rawwit wit_elpi) s in
          Constrexpr.CHole (!@loc, None, Misctypes.IntroAnonymous, Some arg) ] 
          ]
  ;
END


