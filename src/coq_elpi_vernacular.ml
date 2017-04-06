module G = Globnames
module E = Elpi_runtime
module C = Constr
open Names

(* ******************** Vernacular commands ******************************* *)

let init ~paths =
  Elpi_parser.init ~paths;
  Elpi_runtime.enable_typechecking ()

let program_ast = Summary.ref ~name:"elpi-decls" []

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
  let program = E.program_of_ast !program_ast in
  let query_ast = Elpi_parser.parse_goal query in
  let query = E.query_of_ast program query_ast in
  let fails = E.execute_once ~print_constraints:true program query in
  if fails then CErrors.user_err Pp.(str "elpi fails") 

