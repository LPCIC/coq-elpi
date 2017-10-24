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
module U = Coq_elpi_utils

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

let pp_prog_arg _ _ _ = EV.Prog.pr_arg

ARGUMENT EXTEND elpi_program_arg PRINTED BY pp_prog_arg
| [ qualified_name(s) ] -> [ EV.Prog.Qualid (snd s) ]
| [ "-" qualified_name(s) ] -> [ EV.Prog.DashQualid (snd s) ]
| [ string(s) ] -> [ EV.Prog.String s ]
END

VERNAC COMMAND EXTEND Elpi CLASSIFIED AS SIDEFF
| [ "Elpi" "Accumulate" "File" string_list(s) ] -> [ EV.load_files s ]
| [ "Elpi" "Accumulate" "Files" string_list(s) ] -> [ EV.load_files s ]
| [ "Elpi" "Accumulate" elpi_string(s) ] -> [ EV.load_string s ]
| [ "Elpi" "Accumulate" qualified_name(p) "File" string_list(s) ] ->
  [ EV.set_current_program (snd p);EV.load_files s ]
| [ "Elpi" "Accumulate" qualified_name(p) "Files" string_list(s) ] ->
  [ EV.set_current_program (snd p);EV.load_files s ]
| [ "Elpi" "Accumulate" qualified_name(p) elpi_string(s) ] ->
  [ EV.set_current_program (snd p);EV.load_string s ]

| [ "Elpi" "Trace" string_opt(s) ] -> [ EV.trace s ]
| [ "Elpi" "Trace" int(start) int(stop) ] -> [ EV.trace_at start stop ]
| [ "Elpi" "Trace" "Off" ] -> [ EV.trace (Some "") ]
| [ "Elpi" "Bound" "Steps" int(steps) ] -> [ EV.bound_steps steps ]

| [ "Elpi" "Print" qualified_name(p) string_list(s) ] -> [ EV.print p s ]

| [ "Elpi" "Command" qualified_name(p) elpi_string_opt(s) ] ->
    [ EV.set_current_program ~kind:EV.Command (snd p);
      Option.iter EV.load_string s ]
| [ "Elpi" "Tactic" qualified_name(p) elpi_string_opt(s) ] ->
    [ EV.set_current_program ~kind:EV.Tactic (snd p);
      Option.iter EV.load_string s ]

| [ "Elpi" "Query" elpi_string(s) ] ->
    [ EV.run_in_program s ]
| [ "Elpi" "Query"  qualified_name(program) elpi_string(s) ] ->
    [ EV.run_in_program ~program s ]
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

let pr_glob_constr_and_expr = function
  | (_, Some c) -> Ppconstr.pr_constr_expr c
  | (c, None) -> Printer.pr_glob_constr c

let pp_tac_arg _ _ _ = EV.Tac.pr_arg (fun (_,x) -> pr_glob_constr_and_expr x)
let pp_glob_tac_arg _ _ _ = EV.Tac.pr_arg pr_glob_constr_and_expr
let pp_raw_tac_arg _ _ _ = EV.Tac.pr_arg Ppconstr.pr_constr_expr

let glob_elpi_tac_arg glob_sign = function
  | EV.Tac.Qualid _ as x -> x
  | EV.Tac.Int _ as x -> x
  | EV.Tac.String _ as x -> x
  | EV.Tac.Term t -> EV.Tac.Term (Tacintern.intern_constr glob_sign t)

let interp_elpi_tac_arg ist evd = function
  | EV.Tac.Qualid _ as x -> evd.Evd.sigma, x
  | EV.Tac.Int _ as x -> evd.Evd.sigma, x
  | EV.Tac.String _ as x -> evd.Evd.sigma, x
  | EV.Tac.Term t -> evd.Evd.sigma, (EV.Tac.Term(ist,t))

let subst_elpi_tac_arg mod_subst = function
  | EV.Tac.Qualid _ as x -> x
  | EV.Tac.Int _ as x -> x
  | EV.Tac.String _ as x -> x
  | EV.Tac.Term t ->
      EV.Tac.Term (Tacsubst.subst_glob_constr_and_expr mod_subst t)

ARGUMENT EXTEND elpi_tac_arg
PRINTED BY pp_tac_arg
INTERPRETED BY interp_elpi_tac_arg
GLOBALIZED BY glob_elpi_tac_arg
SUBSTITUTED BY subst_elpi_tac_arg
RAW_PRINTED BY pp_raw_tac_arg
GLOB_PRINTED BY pp_glob_tac_arg
| [ qualified_name(s) ] -> [ EV.Tac.Qualid (snd s) ]
| [ string(s) ] -> [ EV.Tac.String s ]
| [ integer(n) ] -> [ EV.Tac.Int n ]
| [ constr(t) ] -> [ EV.Tac.Term t ]
END

TACTIC EXTEND elpi_tac
| [ "elpi" qualified_name(program) elpi_tac_arg_list(args) ] ->
  [ EV.run_tactic program ist args ]
| [ "elpi" "query" elpi_string(s) elpi_tac_arg_list(args) ] ->
  [ EV.run_in_tactic s ist args ]
| [ "elpi" "query"  qualified_name(program) elpi_string(s) elpi_tac_arg_list(args) ] ->
  [ EV.run_in_tactic s ~program ist args ]
  
END

(* vim:set ft=ocaml: *)
