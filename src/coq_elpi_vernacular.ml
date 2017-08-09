(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module E = Elpi_API
module EC = E.Compile
module EP = E.Parse
module EPP = E.Pp
module EA = E.Extend.Ast

module G = Globnames
module C = Constr
open Names

type qualified_name = string list [@@deriving ord]
let pp_qualified_name = Pp.prlist_with_sep (fun () -> Pp.str".") Pp.str
type prog_arg = 
  | String of string
  | Qualid of qualified_name
  | DashQualid of qualified_name
let pp_prog_arg = function
  | String s -> Pp.qstring s
  | Qualid s -> pp_qualified_name s
  | DashQualid s -> Pp.(str"- " ++ pp_qualified_name s)

module SLMap = Map.Make(struct
  type t = qualified_name
  let compare = compare_qualified_name
end)

(* ******************** Vernacular commands ******************************* *)

let init () =
  let build_dir = Coq_elpi_config.elpi_dir in
  let installed_dir =
    let coqlib = Envars.coqlib() in
    if Sys.is_directory coqlib then
      coqlib ^ "/user-contrib/elpi/"
    else (* JsCoq does not initialize coqlib, but paths are relative to pkgs *)
      "elpi/" in
  let paths = [ "."; build_dir; installed_dir ] in
  ignore(E.Setup.init List.(flatten (map (fun x -> ["-I";x]) paths)) ".")

let ensure_initialized =
  let init = lazy(init ()) in
  fun () -> Lazy.force init
;;

let default_program = ["elpi"]

let current_program = Summary.ref ~name:"elpi-cur-program-name" default_program

type src = File of string | EmbeddedString of Loc.t * string

let program_src_ast = Summary.ref ~name:"elpi-programs" SLMap.empty

(* We load pervasives once and forall at the beginning *)
let get p =
  ensure_initialized ();
  try SLMap.find p !program_src_ast
  with Not_found ->
    let pervasives =
      [File "pervasives.elpi", EP.program ~no_pervasives:false []] in
    program_src_ast := SLMap.add p pervasives !program_src_ast;
    pervasives

let in_program : qualified_name * (src * E.Ast.program) list -> Libobject.obj =
  let append name v = get name @ v in
  Libobject.declare_object { Libobject.(default_object "ELPI") with
    Libobject.open_function = (fun _ (_,(name,src_ast)) ->
      program_src_ast := SLMap.add name (append name src_ast) !program_src_ast);
    Libobject.cache_function = (fun (_,(name,src_ast)) ->
      program_src_ast := SLMap.add name (append name src_ast) !program_src_ast);
    Libobject.load_function = (fun _ (_,(name,src_ast)) ->
      program_src_ast := SLMap.add name (append name src_ast) !program_src_ast);
}

let add v =
  if !current_program <> default_program then
    let obj = in_program (!current_program, v) in
    Lib.add_anonymous_leaf obj
  else
    let name = !current_program in
    program_src_ast := SLMap.add name (get name @ v) !program_src_ast
;;

let trace_options = Summary.ref ~name:"elpi-trace" []
let max_steps = Summary.ref ~name:"elpi-steps" max_int

let set_current_program n = current_program := n

let bound_steps n =
  if n <= 0 then max_steps := max_int else max_steps := n

let mk_pragma line file = Printf.sprintf "#line %d \"%s\"\n" line file
let pragma_of_loc loc =
  mk_pragma loc.Loc.line_nb loc.Loc.fname
let pragma_of_ploc loc =
  pragma_of_loc (Pcoq.to_coqloc loc)

let load_files s =
  ensure_initialized ();
  let new_src_ast = List.map (fun fname ->
    File fname, EP.program ~no_pervasives:true [fname]) s in
  add new_src_ast
 ;;

let load_string loc s =
  ensure_initialized ();
  let pragma = pragma_of_ploc loc in
  let fname, oc = Filename.open_temp_file "coq" ".elpi" in
  output_string oc pragma;
  output_string oc s;
  close_out oc;
  let new_ast = EP.program ~no_pervasives:true [fname] in
  Sys.remove fname;
  add [EmbeddedString(Pcoq.to_coqloc loc,s), new_ast]
;;

let run ~static_check program_ast query_ast =
  let program = EC.program program_ast in
  let query = EC.query program query_ast in
  if static_check then
    EC.static_check ~extra_checker:["coq-elpi_typechecker.elpi"] program query;
  E.Setup.trace !trace_options;
  match E.Execute.once ~max_steps:!max_steps program query with
  | E.Execute.Failure -> CErrors.user_err Pp.(str "elpi fails")
  | E.Execute.NoMoreSteps -> CErrors.user_err Pp.(str "elpi run out of steps")
  | E.Execute.Success
    (assignments, { Elpi_API.Data.constraints; custom_constraints }) ->
       let open Elpi_API.Data in let open Coq_elpi_utils in
       List.iter (fun (name, term) ->
         Feedback.msg_debug
           Pp.(str name ++ str " = " ++ str (pp2string EPP.term term)))
         assignments;
       let scst = pp2string EPP.constraints  constraints in
       if scst <> "" then
         Feedback.msg_debug Pp.(str"Syntactic constraints:" ++ spc()++str scst);
       let ccst =
         E.Extend.CustomConstraint.read custom_constraints
           Coq_elpi_API.univ_constraints in
       if not (UState.is_empty ccst) then
         Feedback.msg_debug Pp.(str"Universe constraints:" ++ spc() ++
           Termops.pr_evar_universe_context ccst)
;;

let exec ?(program = !current_program) loc query =
  ensure_initialized ();
  let program_ast = List.map snd (get program) in
  let query_ast = EP.goal (pragma_of_ploc loc ^ query) in
  run ~static_check:true program_ast query_ast
;;

let mkSeq = function
  | [] -> EA.mkNil
  | l -> EA.mkSeq (l @ [EA.mkNil])

let run_command loc name args =
  let predicate = EA.mkCon "main" in
  let args = args |> List.map (function
    | String s -> EA.mkString s
    | Qualid s -> EA.mkString (String.concat "." s)
    | DashQualid s -> EA.mkString ("-" ^ String.concat "." s)) in
  let program_ast =
    try List.map snd (SLMap.find name !program_src_ast)
    with Not_found ->  CErrors.user_err
      Pp.(str"elpi: command " ++ pp_qualified_name name ++ str" not found") in
  let query_ast =
    EA.query_of_term ~loc (EA.mkApp [predicate ; mkSeq args]) in
  run ~static_check:false program_ast query_ast
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

let print program args =
  let past = EP.program ["elpi2mathjx.elpi"] in
  let p = EC.program [past] in
  let tmp, oc = Filename.open_temp_file "coq" ".elpi" in
  let args, fname =
    let default_fname = "coq-elpi.html" in
    match args with
    | [] -> tmp :: default_fname :: [], default_fname
    | x :: xs -> tmp :: x :: xs, x in
  let args = List.map (Printf.sprintf "\"%s\"") args in
  List.iter (function
    | File f, _ -> output_string oc ("accumulate "^f^".")
    | EmbeddedString (loc,s), _ ->
        output_string oc (pragma_of_loc loc);
        output_string oc s)
    (get program);
  close_out oc;
  let gast = EP.goal ("main ["^String.concat "," args^"].") in
  let g = EC.query p gast in
  E.Setup.trace !trace_options;
  match E.Execute.once p g with
  | E.Execute.Failure -> CErrors.user_err Pp.(str "elpi fails printing")
  | E.Execute.NoMoreSteps -> assert false
  | E.Execute.Success _ ->
     Feedback.msg_info Pp.(str"Program printed to " ++ str fname)

