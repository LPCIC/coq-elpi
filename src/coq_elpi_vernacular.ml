(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module E = Elpi_API
module EC = E.Compile
module EP = E.Parse
module EPP = E.Pp
module EA = E.Extend.Ast
module ED = E.Extend.Data

module G = Globnames
module C = Constr
open Names

module Loc = struct
  include Loc
  let pp fmt { fname; line_nb } = Format.fprintf fmt "%s:%d" fname line_nb 
  let show { fname; line_nb } = Format.sprintf "%s:%d" fname line_nb
  let compare = Pervasives.compare
end

type qualified_name = string list [@@deriving ord, show]
let pr_qualified_name = Pp.prlist_with_sep (fun () -> Pp.str".") Pp.str
type prog_arg = 
  | String of string
  | Qualid of qualified_name
  | DashQualid of qualified_name
let pr_prog_arg = function
  | String s -> Pp.qstring s
  | Qualid s -> pr_qualified_name s
  | DashQualid s -> Pp.(str"- " ++ pr_qualified_name s)

type program_kind = Command | Tactic

module SLMap = Map.Make(struct
  type t = qualified_name
  let compare = compare_qualified_name
end)

let run_static_check program query =
  EC.static_check ~extra_checker:["coq-elpi_typechecker.elpi"] program query

(* ******************** Vernacular commands ******************************* *)

module Programs : sig
  type src =
    | File of string
    | EmbeddedString of Loc.t * string

  val get : Ploc.t * qualified_name -> (src * Elpi_API.Ast.program) list
  
  val set_current_program : ?kind:program_kind -> qualified_name -> unit
  val current_program : unit -> Ploc.t * qualified_name
  val add : (src * Elpi_API.Ast.program) list -> unit

  val ensure_initialized : unit -> unit

end = struct

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

type src =
  | File of string
  | EmbeddedString of Loc.t * string
[@@deriving show, ord]
module SrcSet = Set.Make(struct type t = src let compare = compare_src end)

type src_list = src list [@@deriving show]

let program_src_ast = Summary.ref ~name:"elpi-programs" SLMap.empty

(* We load pervasives once and forall at the beginning *)
let get p =
  ensure_initialized ();
  try SLMap.find p !program_src_ast
  with Not_found ->
    if p <> default_program then []
    else [File "pervasives.elpi", EP.program ~no_pervasives:false []]

let append_to name l =
  let prog = get name in
  let rec aux seen = function
    | [] -> List.filter (fun (s,_) ->
              let duplicate = SrcSet.mem s seen in
              if duplicate then
                Feedback.msg_warning
                  Pp.(str"elpi: skipping duplicate accumulation of " ++
                    str(show_src s) ++ str" into "++pr_qualified_name name);
              not duplicate) l
    | (src, _) as x :: xs -> x :: aux (SrcSet.add src seen) xs in
  aux SrcSet.empty prog

let in_program : qualified_name * (src * E.Ast.program) list -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI") with
    Libobject.open_function = (fun _ (_,(name,src_ast)) ->
      program_src_ast :=
        SLMap.add name (append_to name src_ast) !program_src_ast);
    Libobject.cache_function = (fun (_,(name,src_ast)) ->
      program_src_ast :=
        SLMap.add name (append_to name src_ast) !program_src_ast);
}

let add v =
  if !current_program <> default_program then
    let obj = in_program (!current_program, v) in
    Lib.add_anonymous_leaf obj
  else
    let name = !current_program in
    program_src_ast := SLMap.add name (append_to name v) !program_src_ast
;;

let set_current_program ?kind n =
  ensure_initialized ();
  current_program := n;
  try ignore(SLMap.find n !program_src_ast)
  with Not_found ->
    let pervasives_ast =
      File "pervasives.elpi", EP.program ~no_pervasives:false [] in
    let other_fnames = match kind with
      | None -> []
      | Some Command -> ["coq-lib.elpi"]
      | Some Tactic -> ["coq-lib.elpi";"coq-refiner.elpi"] in
    let other_ast =
      List.map (fun x -> File x,EP.program ~no_pervasives:true [x])
        other_fnames in
    add (pervasives_ast::other_ast)

let current_program () = Ploc.dummy, !current_program

let get (_,x) = get x

end

open Programs
let set_current_program = set_current_program

let trace_options = Summary.ref ~name:"elpi-trace" []
let max_steps = Summary.ref ~name:"elpi-steps" max_int

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

let load_string (loc,s) =
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
  if static_check then run_static_check program query;
  E.Setup.trace !trace_options;
  E.Execute.once ~max_steps:!max_steps program query
;;

let run_print ~static_check program_ast query_ast =
  let open Elpi_API.Data in let open Coq_elpi_utils in
  match run ~static_check program_ast query_ast with
  | E.Execute.Failure -> CErrors.user_err Pp.(str "elpi fails")
  | E.Execute.NoMoreSteps -> CErrors.user_err Pp.(str "elpi run out of steps")
  | E.Execute.Success { arg_names; assignments ; constraints; custom_constraints } ->
       StrMap.iter (fun name pos ->
         let term = assignments.(pos) in
         Feedback.msg_debug
           Pp.(str name ++ str " = " ++ str (pp2string EPP.term term)))
         arg_names;
       let scst = pp2string EPP.constraints  constraints in
       if scst <> "" then
         Feedback.msg_debug Pp.(str"Syntactic constraints:" ++ spc()++str scst);
       let _, evd = Coq_elpi_HOAS.get_env_evd custom_constraints in
       let ccst = Evd.evar_universe_context evd in
       if not (UState.is_empty ccst) then
         Feedback.msg_debug Pp.(str"Universe constraints:" ++ spc() ++
           Termops.pr_evar_universe_context ccst)
;;

let run_in_program ?(program = current_program ()) (loc, query) =
  ensure_initialized ();
  let program_ast = List.map snd (get program) in
  let query_ast = EP.goal (pragma_of_ploc loc ^ query) in
  run_print ~static_check:true program_ast query_ast
;;

let mkSeq = function
  | [] -> EA.mkNil
  | l -> EA.mkSeq (l @ [EA.mkNil])

let run_program (loc, name as prog) args =
  let predicate = EA.mkCon "main" in
  let args = args |> List.map (function
    | String s -> EA.mkString s
    | Qualid s -> EA.mkString (String.concat "." s)
    | DashQualid s -> EA.mkString ("-" ^ String.concat "." s)) in
  let program_ast =
    try List.map snd (get prog)
    with Not_found ->  CErrors.user_err
      Pp.(str"elpi: command " ++ pr_qualified_name name ++ str" not found") in
  let query_ast =
    EA.query_of_term ~loc (EA.mkApp [predicate ; mkSeq args]) in
  run_print ~static_check:false program_ast query_ast
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

let print (_, name as program) args =
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
    | File f, _ ->
        if f <> "pervasives.elpi" then
          output_string oc ("accumulate "^Filename.chop_extension f^".\n")
    | EmbeddedString (loc,s), _ ->
        output_string oc (pragma_of_loc loc);
        output_string oc s;
        output_string oc "\n"
    )
    (get program);
  close_out oc;
  let gast = EP.goal ("main ["^String.concat "," args^"].") in
  let g = EC.query p gast in
  E.Setup.trace !trace_options;
  match E.Execute.once p g with
  | E.Execute.Failure -> CErrors.user_err Pp.(str "elpi fails printing")
  | E.Execute.NoMoreSteps -> assert false
  | E.Execute.Success _ ->
     Feedback.msg_info Pp.(str"Program " ++ pr_qualified_name name ++
       str" printed to " ++ str fname)

open Proofview
open Tacticals.New
open Tactics.New

let run_hack ~static_check program_ast query =
  let program = EC.program program_ast in
  let query = E.Extend.Compile.query program query in
  if static_check then run_static_check program query;
  E.Setup.trace !trace_options;
  E.Execute.once ~max_steps:!max_steps program query
;;

let run_tactic program ist =
  tclBIND tclEVARMAP (fun evd -> Goal.nf_enter begin fun gl ->
  let k = Goal.goal gl in
  let query = Coq_elpi_HOAS.goal2query evd k ?main:None in
  let program_ast = List.map snd (get program) in
  match run_hack ~static_check:false program_ast query with
  | E.Execute.Success solution ->
       Coq_elpi_HOAS.solution2evar_map solution
  | _ -> tclZEROMSG Pp.(str "elpi fails")
end)

let run_in_tactic ?(program = current_program ()) (loc, query) ist =
  tclBIND tclEVARMAP (fun evd -> Goal.nf_enter begin fun gl ->
  let k = Goal.goal gl in
  let query = Coq_elpi_HOAS.goal2query ~main:query evd k in
  let program_ast = List.map snd (get program) in
  match run_hack ~static_check:true program_ast query with
  | E.Execute.Success solution ->
       Coq_elpi_HOAS.solution2evar_map solution
  | _ -> tclZEROMSG Pp.(str "elpi fails")
end)


