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
  ignore(Elpi_API.init List.(flatten (map (fun x -> ["-I";x]) paths)));
  EC.enable_typechecking ()

let program_ast = Summary.ref ~name:"elpi-decls" []
let trace_options = Summary.ref ~name:"elpi-trace" []

let load_files s =
  let new_ast = Elpi_parser.parse_program ~no_pervasives:true s in
  program_ast := !program_ast @ new_ast

let load_string s =
  let fname, oc = Filename.open_temp_file "coq" ".elpi" in
  output_string oc s;
  close_out oc;
  let new_ast = Elpi_parser.parse_program ~no_pervasives:true [fname] in
  Sys.remove fname;
  program_ast := !program_ast @ new_ast

let exec query =
  let program = EC.program_of_ast !program_ast in
  let query_ast = Elpi_parser.parse_goal query in
  let query = EC.query_of_ast program query_ast in
  Elpi_API.trace !trace_options;
  let fails = E.execute_once ~print_constraints:true program query in
  if fails then CErrors.user_err Pp.(str "elpi fails") 

let default_trace = "-trace-on -trace-at run 1 10 -trace-only run"

let trace opts =
  let opts = Option.default default_trace opts in
  let opts = CString.split ' ' opts in
  trace_options := opts      

