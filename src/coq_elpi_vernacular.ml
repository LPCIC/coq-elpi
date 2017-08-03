(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module E = Elpi_API
module EC = E.Compile
module EP = E.Parse
module EPP = E.Pp

module G = Globnames
module C = Constr
open Names

(* ******************** Vernacular commands ******************************* *)

let init ~paths =
  let paths = paths @ [Envars.coqlib()^"/user-contrib/elpi/"] in
  ignore(E.Setup.init List.(flatten (map (fun x -> ["-I";x]) paths)) ".")

let program_src = Summary.ref ~name:"elpi-decls-src" []
let program_ast = Summary.ref ~name:"elpi-decls" []
let trace_options = Summary.ref ~name:"elpi-trace" []
let max_steps = Summary.ref ~name:"elpi-steps" max_int

let bound_steps n =
  if n <= 0 then max_steps := max_int else max_steps := n

let load_files s =
  let new_ast = EP.program ~no_pervasives:true s in
  program_ast := !program_ast @ [new_ast];
  program_src := !program_src @ List.map (fun x -> `File x) s

let file_pragma loc =
  Printf.sprintf "#line %d \"%s\"\n" loc.Loc.line_nb loc.Loc.fname

let load_string loc s =
  let fname, oc = Filename.open_temp_file "coq" ".elpi" in
  output_string oc (file_pragma loc);
  output_string oc s;
  close_out oc;
  let new_ast = EP.program ~no_pervasives:true [fname] in
  Sys.remove fname;
  program_ast := !program_ast @ [new_ast];
  program_src := !program_src @ [ `Text s ]

let exec loc query =
  let program = EC.program !program_ast in
  let query_ast = EP.goal (file_pragma loc ^ query) in
  let query = EC.query program query_ast in
  EC.static_check ~extra_checker:["coq-elpi_typechecker.elpi"] program query;
  E.Setup.trace !trace_options;
  match E.Execute.once ~max_steps:!max_steps program query with
  | E.Execute.Failure -> CErrors.user_err Pp.(str "elpi fails")
  | E.Execute.NoMoreSteps -> CErrors.user_err Pp.(str "elpi run out of steps")
  | E.Execute.Success (assignments, { Elpi_API.Data.constraints; custom_constraints }) ->
       let open Elpi_API.Data in let open Coq_elpi_utils in
       List.iter (fun (name, term) ->
         Feedback.msg_debug Pp.(str name ++ str " = " ++ str (pp2string EPP.term term)))
         assignments;
       Feedback.msg_debug Pp.(str"Syntactic constraints:" ++ spc() ++
         str (pp2string EPP.constraints  constraints));
       Feedback.msg_debug Pp.(str"Universe constraints:" ++ spc() ++
         Termops.pr_evar_universe_context
           (E.Extend.CustomConstraint.read custom_constraints Coq_elpi_API.univ_constraints))
;;

let default_trace start stop =
  Printf.sprintf
    "-trace-on -trace-at run %d %d -trace-only (run|select|assign)"
    start stop

let trace opts =
  let opts = Option.default (default_trace 1 max_int) opts in
  let opts = Str.(global_replace (regexp "\\([|()]\\)") "\\\\\\1" opts) in
  let opts = CString.split ' ' opts in
  trace_options := opts

let trace_at start stop = trace (Some (default_trace start stop))

let print args =
  let past = EP.program ["utils/elpi2mathjx.elpi"] in
  let p = EC.program [past] in
  let tmp, oc = Filename.open_temp_file "coq" ".elpi" in
  let args =
    match args with
    | [] -> tmp :: "coq-elpi.html" :: []
    | x :: xs -> tmp :: x :: xs in
  let args = List.map (Printf.sprintf "\"%s\"") args in
  List.iter (function
    | `File f -> output_string oc ("accumulate "^f^".")
    | `Text s -> output_string oc s) !program_src;
  close_out oc;
  let gast = EP.goal ("main ["^String.concat "," args^"].") in
  let g = EC.query p gast in
  E.Setup.trace !trace_options;
  match E.Execute.once p g with
  | E.Execute.Failure -> CErrors.user_err Pp.(str "elpi fails printing")
  | E.Execute.NoMoreSteps -> assert false
  | E.Execute.Success _ -> ()

