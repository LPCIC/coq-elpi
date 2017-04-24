(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

DECLARE PLUGIN "elpi"

open Stdarg
open Ltac_plugin

module EV = Coq_elpi_vernacular

VERNAC COMMAND EXTEND Elpi CLASSIFIED AS SIDEFF
| [ "Elpi" "Run" string(s) ] -> [ EV.exec s ]
| [ "Elpi" "Init" string_list(s) ] -> [ EV.init s ]
| [ "Elpi" "Accumulate" "File" string_list(s) ] -> [ EV.load_files s ]
| [ "Elpi" "Accumulate" "Files" string_list(s) ] -> [ EV.load_files s ]
| [ "Elpi" "Accumulate" string(s) ] -> [ EV.load_string s ]
| [ "Elpi" "Trace" string_opt(s) ] -> [ EV.trace s ]
END

let pr_string _ _ _ (s : string) = Pp.str s

open Pcoq
open Pcoq.Constr

ARGUMENT EXTEND elpi
    PRINTED BY pr_string
 [ "xxxxxxx" ] -> [ "" ]
END

let () = Coq_elpi_glob_quotation.is_coq_string := (fun x -> Genarg.(has_type x (glbwit wit_elpi)))
let () = Coq_elpi_glob_quotation.get_coq_string := (fun x -> Genarg.(out_gen (glbwit wit_elpi) x))

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


