(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

DECLARE PLUGIN "elpi"
let () = Coq_elpi_vernacular.init ~paths:["."]

open Stdarg
open Ltac_plugin

open Pcoq
open Pcoq.Constr
open Pcoq.Prim

module EV = Coq_elpi_vernacular

let pr_loc _ _ _ (_ : Ploc.t option) = Pp.str""
ARGUMENT EXTEND elpi_loc PRINTED BY pr_loc
[ "xxxxxxxx" ] -> [ None ]   (* XXX To be removed when maxime's patches get merged *)
END

GEXTEND Gram GLOBAL: elpi_loc;
  elpi_loc: [[ -> Some loc ]];
END

let pr_fp _ _ _ = EV.pp_qualified_name

ARGUMENT EXTEND qualified_name PRINTED BY pr_fp
[ "xxxxxxxx" ] -> [ [] ]   (* XXX To be removed when maxime's patches get merged *)
END
GEXTEND Gram GLOBAL: qualified_name;
qualified_name : [[ i = IDENT; s = LIST0 FIELD -> i :: s ]];
END

let pp_prog_arg _ _ _ = EV.pp_prog_arg

ARGUMENT EXTEND elpi_program_arg PRINTED BY pp_prog_arg
| [ qualified_name(s) ] -> [ EV.Qualid s ]
| [ "-" qualified_name(s) ] -> [ EV.DashQualid s ]
| [ string(s) ] -> [ EV.String s ]
END

VERNAC COMMAND EXTEND Elpi CLASSIFIED AS SIDEFF
| [ "Elpi" "Accumulate" "File" string_list(s) ] -> [ EV.load_files s ]
| [ "Elpi" "Accumulate" "Files" string_list(s) ] -> [ EV.load_files s ]
| [ "Elpi" "Accumulate" elpi_loc(loc) string(s) ] -> [ EV.load_string (Option.get loc) s ]

| [ "Elpi" "Trace" string_opt(s) ] -> [ EV.trace s ]
| [ "Elpi" "Trace" int(start) int(stop) ] -> [ EV.trace_at start stop ]
| [ "Elpi" "Trace" "Off" ] -> [ EV.trace (Some "") ]
| [ "Elpi" "Bound" "Steps" int(steps) ] -> [ EV.bound_steps steps ]
| [ "Elpi" "Run" elpi_loc(loc) string(s) ] -> [ EV.exec (Option.get loc) s ]
| [ "Elpi" "Run"  qualified_name(program) elpi_loc(loc) string(s) ] ->
  [ EV.exec ~program (Option.get loc) s ]

| [ "Elpi" "Print" qualified_name(p) string_list(s) ] -> [ EV.print p s ]

| [ "Elpi" "Program" qualified_name(p) ] -> [ EV.set_current_program p ]
| [ "Elpi" elpi_loc(loc) qualified_name(program) elpi_program_arg_list(args) ] ->
  [ EV.run_command (Option.get loc) program args ]
END

let pr_string _ _ _ (s : string) = Pp.str s

ARGUMENT EXTEND elpi
    PRINTED BY pr_string
 [ "xxxxxxx" ] -> [ "" ] (* XXX To be removed when maxime's patches get merged *)
END

let () = Coq_elpi_glob_quotation.is_coq_string := (fun x -> Genarg.(has_type x (glbwit wit_elpi)))
let () = Coq_elpi_glob_quotation.get_coq_string := (fun x -> Genarg.(out_gen (glbwit wit_elpi) x))

GEXTEND Gram
  GLOBAL: operconstr;

  operconstr: LEVEL "0"
    [ [ "lp"; ":"; id = IDENT ->
          let arg = Genarg.in_gen (Genarg.rawwit wit_elpi) id in
          CAst.make ~loc:!@loc
             (Constrexpr.CHole (None, Misctypes.IntroAnonymous, Some arg)) ] 
    | [ "lp"; ":"; s = STRING -> 
          let arg = Genarg.in_gen (Genarg.rawwit wit_elpi) s in
          CAst.make ~loc:!@loc
            (Constrexpr.CHole (None, Misctypes.IntroAnonymous, Some arg)) ] 
          ]
  ;
END

(* vim:set ft=ocaml: *)
