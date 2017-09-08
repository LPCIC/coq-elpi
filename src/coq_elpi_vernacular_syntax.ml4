(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

DECLARE PLUGIN "elpi_plugin"

open Stdarg
open Ltac_plugin

open Pcoq
open Pcoq.Constr
open Pcoq.Prim

module EV = Coq_elpi_vernacular

let pr_elpi_string _ _ _ (_,s : Ploc.t * string) = Pp.str s
ARGUMENT EXTEND elpi_string PRINTED BY pr_elpi_string
[ "xxxxxxxx" ] -> [ (Ploc.dummy, "") ]   (* XXX To be removed when maxime's patches get merged *)
END
GEXTEND Gram GLOBAL: elpi_string;
elpi_string : [[ s = string -> loc, s ]];
END

let pr_fp _ _ _ (_,x) = EV.pr_qualified_name x

ARGUMENT EXTEND qualified_name PRINTED BY pr_fp
[ "xxxxxxxx" ] -> [ Ploc.dummy, [] ]   (* XXX To be removed when maxime's patches get merged *)
END
GEXTEND Gram GLOBAL: qualified_name;
qualified_name : [[ i = IDENT; s = LIST0 FIELD -> loc, i :: s ]];
END

let pp_prog_arg _ _ _ = EV.pr_prog_arg

ARGUMENT EXTEND elpi_program_arg PRINTED BY pp_prog_arg
| [ qualified_name(s) ] -> [ EV.Qualid (snd s) ]
| [ "-" qualified_name(s) ] -> [ EV.DashQualid (snd s) ]
| [ string(s) ] -> [ EV.String s ]
END

VERNAC COMMAND EXTEND Elpi CLASSIFIED AS SIDEFF
| [ "Elpi" "Accumulate" "File" string_list(s) ] -> [ EV.load_files s ]
| [ "Elpi" "Accumulate" "Files" string_list(s) ] -> [ EV.load_files s ]
| [ "Elpi" "Accumulate" elpi_string(s) ] ->
    [ EV.load_string s ]

| [ "Elpi" "Trace" string_opt(s) ] -> [ EV.trace s ]
| [ "Elpi" "Trace" int(start) int(stop) ] -> [ EV.trace_at start stop ]
| [ "Elpi" "Trace" "Off" ] -> [ EV.trace (Some "") ]
| [ "Elpi" "Bound" "Steps" int(steps) ] -> [ EV.bound_steps steps ]
| [ "Elpi" "Run" elpi_string(s) ] ->
    [ EV.run_in_program s ]
| [ "Elpi" "Run"  qualified_name(program) elpi_string(s) ] ->
    [ EV.run_in_program ~program s ]

| [ "Elpi" "Print" qualified_name(p) string_list(s) ] -> [ EV.print p s ]

| [ "Elpi" "Program" qualified_name(p) ] -> [ EV.set_current_program (snd p) ]
| [ "Elpi" "Command" qualified_name(p) elpi_string_opt(s) ] ->
    [ EV.set_current_program ~kind:EV.Command (snd p);
      Option.iter EV.load_string s ]
| [ "Elpi" "Tactic" qualified_name(p) elpi_string_opt(s) ] ->
    [ EV.set_current_program ~kind:EV.Tactic (snd p);
      Option.iter EV.load_string s ]
| [ "Elpi" qualified_name(program) elpi_program_arg_list(args) ] ->
    [ EV.run_program program args ]
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

TACTIC EXTEND elpi_tac
| [ "elpi" qualified_name(program) ] ->
  [ EV.run_tactic program ist ]
| [ "elpi" "run" elpi_string(s) ] ->
  [ EV.run_in_tactic s ist ]
| [ "elpi" "run"  qualified_name(program) elpi_string(s) ] ->
  [ EV.run_in_tactic s ~program ist ]
  
END

(* vim:set ft=ocaml: *)
