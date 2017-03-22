let paths = Summary.ref ~name:"elpi-paths" []

let path s = paths := s :: !paths (* TODO: libstack *)

let program_ast = Summary.ref ~name:"elpi-decls" []

let load_file s =
        (* FIXME: elpi_parser is statefule (not to load twice) *)
  let new_ast = Elpi_parser.parse_program ~paths:!paths ~filenames:[s] in
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


