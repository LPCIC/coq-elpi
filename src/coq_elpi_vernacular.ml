(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module G = Globnames
module E = Elpi_API.Runtime
module EC = Elpi_API.Compiler
module C = Constr
open Names

(* ******************** Vernacular commands ******************************* *)

let init ~paths =
  ignore(Elpi_API.init List.(flatten (map (fun x -> ["-I";x]) paths)))

let program_ast = Summary.ref ~name:"elpi-decls" []
let trace_options = Summary.ref ~name:"elpi-trace" []

let load_files s =
  let new_ast = Elpi_parser.parse_program ~no_pervasives:true s in
  program_ast := !program_ast @ new_ast

let file_pragma loc =
  Printf.sprintf "#line %d \"%s\"\n" loc.Loc.line_nb loc.Loc.fname

let load_string loc s =
  let fname, oc = Filename.open_temp_file "coq" ".elpi" in
  output_string oc (file_pragma loc);
  output_string oc s;
  close_out oc;
  let new_ast = Elpi_parser.parse_program ~no_pervasives:true [fname] in
  Sys.remove fname;
  program_ast := !program_ast @ new_ast

let exec loc query =
  let program = EC.program_of_ast !program_ast in
  let query_ast = Elpi_parser.parse_goal (file_pragma loc ^ query) in
  let query = EC.query_of_ast program query_ast in
  Elpi_API.Compiler.typecheck ~extra_checker:["coq-elpi_typechecker.elpi"] program query;
  Elpi_API.trace !trace_options;
  let fails = E.execute_once ~print_constraints:true program query in
  if fails then CErrors.user_err Pp.(str "elpi fails") 

let default_trace =
  "-trace-on -trace-at run 1 "^string_of_int max_int^" -trace-only run"

let trace opts =
  let opts = Option.default default_trace opts in
  let opts = Str.(global_replace (regexp "\\([|()]\\)") "\\\\\\1" opts) in
  let opts = CString.split ' ' opts in
  trace_options := opts      

