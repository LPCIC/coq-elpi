let init ~paths =  Elpi_parser.init ~paths

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
  let program = Elpi_runtime.program_of_ast !program_ast in
  let query_ast = Elpi_parser.parse_goal query in
  let query = Elpi_runtime.query_of_ast program query_ast in
  let fails = Elpi_runtime.execute_once ~print_constraints:true program query in
  if fails then CErrors.user_err Pp.(str "elpi fails") 

(* Custom predicates *)
let () =
  let open Elpi_util in
  Elpi_runtime.register_custom "$say" (fun ~depth ~env _ args ->
      let b = Buffer.create 80 in
      let fmt = Format.formatter_of_buffer b in
      Format.fprintf fmt "@[<hov 1>%a@]@\n%!"
        Elpi_runtime.Pp.(pplist (uppterm depth [] 0 env) " ") args;
    Feedback.msg_info (Pp.str (Buffer.contents b));
    [])
;;


