(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module E = Elpi_API.Runtime
module EC = Elpi_API.Compiler
module EP = Elpi_API.Parser

module G = Globnames
module C = Constr
open Names

(* ******************** Vernacular commands ******************************* *)

let init ~paths =
  ignore(Elpi_API.init List.(flatten (map (fun x -> ["-I";x]) paths)))

let program_src = Summary.ref ~name:"elpi-decls-src" []
let program_ast = Summary.ref ~name:"elpi-decls" []
let trace_options = Summary.ref ~name:"elpi-trace" []

let load_files s =
  let new_ast = EP.parse_program ~no_pervasives:true s in
  program_ast := !program_ast @ new_ast;
  program_src := !program_src @ List.map (fun x -> `File x) s

let file_pragma loc =
  Printf.sprintf "#line %d \"%s\"\n" loc.Loc.line_nb loc.Loc.fname

let load_string loc s =
  let fname, oc = Filename.open_temp_file "coq" ".elpi" in
  output_string oc (file_pragma loc);
  output_string oc s;
  close_out oc;
  let new_ast = EP.parse_program ~no_pervasives:true [fname] in
  Sys.remove fname;
  program_ast := !program_ast @ new_ast;
  program_src := !program_src @ [ `Text s ]

let exec loc query =
  let program = EC.program_of_ast !program_ast in
  let query_ast = EP.parse_goal (file_pragma loc ^ query) in
  let query = EC.query_of_ast program query_ast in
  Elpi_API.Compiler.typecheck ~extra_checker:["coq-elpi_typechecker.elpi"] program query;
  Elpi_API.trace !trace_options;
  let fails = E.execute_once ~print_constraints:true program query in
  if fails then CErrors.user_err Pp.(str "elpi fails") 

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
  let past = EP.parse_program ["utils/elpi2mathjx.elpi"] in
  let p = EC.program_of_ast past in
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
  let gast = EP.parse_goal ("main ["^String.concat "," args^"].") in
  let g = EC.query_of_ast p gast in
  Elpi_API.trace !trace_options;
  let fails = E.execute_once ~print_constraints:true p g in
  if fails then CErrors.user_err Pp.(str "error printing") 

