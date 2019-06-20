(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module EC = API.Compile
module EP = API.Parse
module EPP = API.Pp
module EU = API.Utils
module ET = API.RawData

let parse_file x = 
  try EP.program ~print_accumulated_files:false x
  with EP.ParseError(loc, msg) ->
    let loc = Coq_elpi_utils.to_coq_loc loc in
    CErrors.user_err ~loc ~hdr:"elpi" (Pp.str msg)

let parse_string loc x =
  let x = Stream.of_string x in
  try EP.program_from_stream ~print_accumulated_files:false loc x
  with EP.ParseError(loc, msg) ->
    let loc = Coq_elpi_utils.to_coq_loc loc in
    CErrors.user_err ~loc ~hdr:"elpi" (Pp.str msg)

let parse_goal x =
  try EP.goal x
  with EP.ParseError(loc, msg) ->
    let loc = Coq_elpi_utils.to_coq_loc loc in
    CErrors.user_err ~loc ~hdr:"elpi" (Pp.str msg)


type qualified_name = string list [@@deriving ord]
let pr_qualified_name = Pp.prlist_with_sep (fun () -> Pp.str".") Pp.str
let show_qualified_name = String.concat "."
let pp_qualified_name fmt l = Format.fprintf fmt "%s" (String.concat "." l)
  
type 'a arg = 
  | Int of int
  | String of string
  | Qualid of qualified_name
  | DashQualid of qualified_name
  | Term of 'a
let pr_arg f = function
  | Int n -> Pp.int n
  | String s -> Pp.qstring s
  | Qualid s -> pr_qualified_name s
  | DashQualid s -> Pp.(str"- " ++ pr_qualified_name s)
  | Term s -> f s
let glob_arg glob_sign = function
  | Qualid _ as x -> x
  | DashQualid _ as x -> x
  | Int _ as x -> x
  | String _ as x -> x
  | Term t -> Term (Ltac_plugin.Tacintern.intern_constr glob_sign t)
let interp_arg ist evd = function
  | Qualid _ as x -> evd.Evd.sigma, x
  | DashQualid _ as x -> evd.Evd.sigma, x
  | Int _ as x -> evd.Evd.sigma, x
  | String _ as x -> evd.Evd.sigma, x
  | Term t -> evd.Evd.sigma, (Term(ist,t))

type program_kind = Command | Tactic

module SLMap = Map.Make(struct
  type t = qualified_name
  let compare = compare_qualified_name
end)

(* ******************** Vernacular commands ******************************* *)

module Programs : sig
type src =
  | File of src_file
  | EmbeddedString of src_string
  | Database of qualified_name
and src_file = {
  fname : string;
  fast : API.Ast.program
}
and src_string = {
  sloc : API.Ast.Loc.t;
  sdata : string;
  sast : API.Ast.program
}

  val get_header : unit -> API.Setup.program_header * API.Ast.program
  val get : qualified_name -> API.Ast.program list
  
  val set_current_program : ?kind:program_kind -> Loc.t * qualified_name -> unit
  val current_program : unit -> Loc.t * qualified_name
  val add : src list -> unit

  val load_api : string list -> unit
  val load_checker : string -> unit
  val load_printer : string -> unit
  val load_command : string -> unit
  val load_tactic : string -> unit

  val ensure_initialized : unit -> unit

  val declare_db : qualified_name -> unit
  val add_db : qualified_name -> API.Ast.program list -> unit
  val db_exists : qualified_name -> bool

  val checker : unit -> API.Ast.program
  val printer : unit -> API.Ast.program

end = struct

type src =
  | File of src_file
  | EmbeddedString of src_string
  | Database of qualified_name
and src_file = {
  fname : string;
  fast : API.Ast.program [@compare fun _ _ -> 0 ] [@opaque]
}
and src_string = {
  sloc : API.Ast.Loc.t;
  sdata : string;
  sast : API.Ast.program [@compare fun _ _ -> 0] [@opaque]
}
[@@deriving show, ord]

let _ = show_src_file
let _ = show_src_string

module SrcSet = Set.Make(struct type t = src let compare = compare_src end)

let current_program = Summary.ref ~name:"elpi-cur-program-name" None

let program_src_ast = Summary.ref ~name:"elpi-programs" SLMap.empty

let db_name_ast = Summary.ref ~name:"elpi-db" SLMap.empty

let ast_of_src = function
  | File { fast = a } -> [a]
  | EmbeddedString { sast = a } -> [a]
  | Database name ->
     try List.(flatten (map snd (SLMap.find name !db_name_ast)))
     with Not_found ->
       CErrors.user_err Pp.(str "Unknown Db " ++ str (show_qualified_name name))

let get_paths () =
  let build_dir = Coq_elpi_config.elpi_dir in
  let installed_dirs =
    let valid_dir d = try Sys.is_directory d with Sys_error _ -> false in
    (Envars.coqlib () ^ "/user-contrib") :: Envars.coqpath
    |> List.map (fun p -> p ^ "/elpi/")
    |> ((@) [".";".."]) (* Hem, this sucks *)
    |> ((@) (try let ic, _ as p = Unix.open_process "elpi -where 2>/dev/null" in
                 let w = input_line ic in
                 let _ = Unix.close_process p in [w]
             with _ -> []))
    |> List.filter valid_dir
  in
  "." :: build_dir :: installed_dirs

(* API.Setup called *)
let program_header_ast = Pervasives.ref None

(* elpi.vo loaded *)
let api_ast = Summary.ref ~name:"elpi-api" None
let in_elpi_api : API.Ast.program -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-API") with
    Libobject.load_function = (fun _ (_,x) -> api_ast := Some x);
}

let builtin_declarations =
  let open Elpi.Builtin in
  Coq_elpi_builtins.coq_builtins @
  io_builtins @ elpi_builtins @ elpi_nonlogical_builtins @ elpi_stdlib

let init () =
  let builtins =
    API.BuiltIn.declare
      ~file_name:"coq-builtin.elpi" 
      (Elpi.Builtin.core_builtins @ builtin_declarations) in
  let pheader, _ = API.Setup.init ~builtins ~basedir:"."
    List.(flatten (map (fun x -> ["-I";x]) (get_paths ()))) in
  program_header_ast := Some pheader
;;

let ensure_initialized =
  let init = lazy (init ()) in
  fun () -> Lazy.force init
;;

let load_api apis =
  ensure_initialized ();
  (* This is a bit hackish, since the path is $CWD *)
  let oc = open_out "coq-builtin.elpi" in
  let fmt = Format.formatter_of_out_channel oc in
  Format.fprintf fmt
    "%% This file is automatically generated from coq_elpi_builtin.ml@\n";
  Format.fprintf fmt "%% See also %a@\n"
     (API.RawPp.list Format.pp_print_string " ") apis;
  API.BuiltIn.document fmt builtin_declarations;
  Format.pp_print_flush fmt ();
  close_out oc;
  let api = parse_file apis in
  api_ast := Some api;
  Lib.add_anonymous_leaf (in_elpi_api api)

let get_header () =
  ensure_initialized ();
  match !program_header_ast, !api_ast with
  | _, None -> CErrors.user_err Pp.(str "Call Elpi Api first");
  | Some x, Some y -> x, y
  | None, _ -> assert false

(* We load pervasives and coq-lib once and forall at the beginning *)
let get ?(fail_if_not_exists=false) p =
  ensure_initialized ();
  try SLMap.find p !program_src_ast
  with Not_found ->
    if fail_if_not_exists then
      CErrors.user_err
        Pp.(str "No Elpi Command/Tactic named " ++ pr_qualified_name p)
    else
      []

let append_to_prog name l =
  let prog = get name in
  let rec aux seen = function
    | [] -> List.filter (fun s ->
              let duplicate = SrcSet.mem s seen in
              if duplicate then
                Feedback.msg_warning
                  Pp.(str"elpi: skipping duplicate accumulation of " ++
                    str(show_src s) ++ str" into "++pr_qualified_name name);
              not duplicate) l
    | x :: xs -> x :: aux (SrcSet.add x seen) xs in
  aux SrcSet.empty prog

let in_program : qualified_name * src list -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI") with
    Libobject.open_function = (fun _ (_,(name,src_ast)) ->
      program_src_ast :=
        SLMap.add name (append_to_prog name src_ast) !program_src_ast);
    Libobject.cache_function = (fun (_,(name,src_ast)) ->
      program_src_ast :=
        SLMap.add name (append_to_prog name src_ast) !program_src_ast);
}

let add v =
  match !current_program with
  | None -> CErrors.user_err Pp.(str "No current Elpi Command/Tactic")
  | Some (_,name) ->
      let obj = in_program (name, v) in
      Lib.add_anonymous_leaf obj
;;


let db_exists name = SLMap.mem name !db_name_ast

let append_to_db name (uuid,data as l) =
  try SLMap.find name !db_name_ast @ [l]
  with Not_found -> [l]

let in_db : qualified_name * API.Ast.program list -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-DB") with
    Libobject.open_function = (fun _ (uuid,(name,p)) ->
      db_name_ast :=
        SLMap.add name (append_to_db name (uuid,p)) !db_name_ast);
    Libobject.cache_function = (fun (uuid,(name,p)) ->
      db_name_ast :=
        SLMap.add name (append_to_db name (uuid,p)) !db_name_ast);
}

let declare_db name =
  if db_exists name then ()
  else Lib.add_anonymous_leaf (in_db (name,[]))

let add_db name l =
  if db_exists name then Lib.add_anonymous_leaf (in_db (name,l))
  else CErrors.user_err
    Pp.(str "Db " ++ pr_qualified_name name ++ str" not found") 


let lp_command_ast = Summary.ref ~name:"elpi-lp-command" None
let in_lp_command_ast : src -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-COMMAND") with
    Libobject.load_function = (fun _ (_,x) -> lp_command_ast := Some x);
}
let load_command s =
  ensure_initialized ();
  let ast = File {
    fname = s;
    fast = parse_file [s]
  } in
  lp_command_ast := Some ast;
  Lib.add_anonymous_leaf (in_lp_command_ast ast)
let command () =
  match !lp_command_ast with
  | None -> CErrors.user_err Pp.(str "Elpi CommandTemplate was not called")
  | Some ast -> ast

let lp_tactic_ast = Summary.ref ~name:"elpi-lp-tactic" None
let in_lp_tactic_ast : src -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-TACTIC") with
    Libobject.load_function = (fun _ (_,x) -> lp_tactic_ast := Some x);
}
let load_tactic s =
  ensure_initialized ();
  let ast = File {
    fname = s;
    fast = parse_file [s]
  } in
  lp_tactic_ast := Some ast;
  Lib.add_anonymous_leaf (in_lp_tactic_ast ast)
let tactic () =
  match !lp_tactic_ast with
  | None -> CErrors.user_err Pp.(str "Elpi TacticTemplate was not called")
  | Some ast -> ast

let set_current_program ?kind (loc,n) =
  ensure_initialized ();
  current_program := Some (loc,n);
  try ignore(SLMap.find n !program_src_ast)
  with Not_found ->
    match kind with
    | None ->
        CErrors.user_err Pp.(
          str "Elpi Command/Tactic " ++ pr_qualified_name n ++
          str " never declared")
    | Some kind ->
    let other_ast = match kind with
      | Command -> command ()
      | Tactic  -> tactic () in
    add [other_ast]

let current_program () = 
  match !current_program with
  | None -> CErrors.user_err Pp.(str "No current Elpi Command/Tactic")
  | Some x -> x

let get x =
  List.(flatten (map ast_of_src (get ~fail_if_not_exists:true x)))
  
let lp_checker_ast = Summary.ref ~name:"elpi-lp-checker" None
let in_lp_checker_ast : API.Ast.program -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-CHECKER") with
    Libobject.load_function = (fun _ (_,x) -> lp_checker_ast := Some x);
}
let load_checker s =
  ensure_initialized ();
  let ast = parse_file [s] in
  lp_checker_ast := Some ast;
  Lib.add_anonymous_leaf (in_lp_checker_ast ast)
let checker () =
  match !lp_checker_ast with
  | None -> CErrors.user_err Pp.(str "Elpi Checker was not called")
  | Some ast -> ast

let lp_printer_ast = Summary.ref ~name:"elpi-lp-printer" None
let in_lp_printer_ast : API.Ast.program -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-PRINTER") with
    Libobject.load_function = (fun _ (_,x) -> lp_printer_ast := Some x);
}
let load_printer s =
  ensure_initialized ();
  let ast = parse_file [s] in
  lp_printer_ast := Some ast;
  Lib.add_anonymous_leaf (in_lp_printer_ast ast)
let printer () =
  match !lp_printer_ast with
  | None -> CErrors.user_err Pp.(str "Elpi Printer was not called")
  | Some ast -> ast

end

open Programs
let set_current_program = set_current_program

let load_command = load_command
let load_tactic = load_tactic
let load_printer = load_printer
let load_checker = load_checker
let load_hoas_def = load_api

let run_static_check query =
  (* We turn a failure into a proper error in etc/coq-elpi_typechecker.elpi *)
  let header, api = get_header () in
  ignore(EC.static_check header ~checker:[api;checker ()] query)

let trace_options = Summary.ref ~name:"elpi-trace" []
let max_steps = Summary.ref ~name:"elpi-steps" max_int
let debug_vars = Summary.ref ~name:"elpi-debug" EC.StrSet.empty

let debug vl = debug_vars := List.fold_right EC.StrSet.add vl EC.StrSet.empty 

let cc_flags () =
  { EC.default_flags with EC.defined_variables = !debug_vars }

let bound_steps n =
  if n <= 0 then max_steps := max_int else max_steps := n

let load_files s =
  ensure_initialized ();
  try
    let new_src_ast = List.map (fun fname ->
      File {
        fname;
        fast = parse_file [fname]
      }) s in
    add new_src_ast
  with Failure s ->  CErrors.user_err Pp.(str s)
 ;;

let load_string (loc,s) =
  ensure_initialized ();
  let new_ast = parse_string loc s in
  add [EmbeddedString { sloc = loc; sdata = s; sast = new_ast}]
;;

let load_db name =
  if db_exists name then add [Database name]
  else CErrors.user_err
    Pp.(str "Db " ++ pr_qualified_name name ++ str" not found") 

let declare_db name (loc,s) =
  ensure_initialized ();
  declare_db name;
  add_db name [parse_string loc s]

let run ~static_check ?(flags = cc_flags ()) program_ast query =
  let header, api = get_header () in
  let program = EC.program ~flags header (api :: program_ast) in
  let query =
    match query with
    | `Ast query_ast -> EC.query program query_ast
    | `Fun query_builder -> API.RawQuery.compile program query_builder in
  API.Setup.trace [];
  if static_check then run_static_check query;
  API.Setup.trace !trace_options;
  API.Execute.once ~max_steps:!max_steps (EC.link query)
;;

let run_and_print ~print ~static_check ?flags program_ast query_ast =
  let open API.Data in let open Coq_elpi_utils in
  match run ~static_check ?flags
        program_ast query_ast
  with
  | API.Execute.Failure -> CErrors.user_err Pp.(str "elpi fails")
  | API.Execute.NoMoreSteps -> CErrors.user_err Pp.(str "elpi run out of steps")
  | API.Execute.Success {
     assignments ; constraints; state
    } ->
    if print then begin
      StrMap.iter (fun name term ->
        Feedback.msg_debug
          Pp.(str name ++ str " = " ++ str (pp2string EPP.term term)))
        assignments;
      let scst = pp2string EPP.constraints  constraints in
      if scst <> "" then
        Feedback.msg_debug Pp.(str"Syntactic constraints:" ++ spc()++str scst);
      let _, evd = Coq_elpi_HOAS.get_global_env_evd state in
      let ccst = Evd.evar_universe_context evd in
      if not (UState.is_empty ccst) then
        Feedback.msg_debug Pp.(str"Universe constraints:" ++ spc() ++
          Termops.pr_evar_universe_context ccst)
    end;
    (* We add clauses declared via coq.elpi.accumulate *)
    let clauses_to_add =
      API.State.get Coq_elpi_builtins.clauses_for_later
        state in
    List.iter (fun (dbname,ast) ->
      add_db (Coq_elpi_utils.string_split_on_char '.' dbname) [ast])
      clauses_to_add
;;

let run_in_program ?(program = current_program ()) (loc, query) =
  ensure_initialized ();
  let program_ast = get (snd program) in
  let query_ast = `Ast (parse_goal loc query) in
  run_and_print ~print:true ~static_check:true program_ast query_ast
;;

let typecheck ?(program = current_program ()) () =
  let program_ast = get (snd program) in
  let query_ast = parse_goal (API.Ast.Loc.initial "(typecheck)") "true." in
  let header, api = get_header () in
  let program =
    EC.program ~flags:EC.default_flags header (api :: program_ast) in
  let query = EC.query program query_ast in
  API.Setup.trace !trace_options;
  run_static_check query
;;

let to_arg = function
  | Int n -> Coq_elpi_goal_HOAS.Int n
  | String x -> Coq_elpi_goal_HOAS.String x
  | Qualid x -> Coq_elpi_goal_HOAS.String (String.concat "." x)
  | DashQualid x -> Coq_elpi_goal_HOAS.String ("-" ^ String.concat "." x)
  | Term g -> Coq_elpi_goal_HOAS.Term g

let mainc = ET.Constants.from_stringc "main"

let run_program (loc, name as prog) args =
  let args = args
    |> List.map (glob_arg (Genintern.empty_glob_sign (Global.env())))
    |> List.map (interp_arg (Ltac_plugin.Tacinterp.default_ist ()) Evd.({ sigma = from_env (Global.env()); it = 0 }))
    |> List.map snd in
  let args = args |> List.map to_arg in
  let query ~depth state =
    let state, args = CList.fold_left_map
      (Coq_elpi_goal_HOAS.in_elpi_global_arg ~depth (Global.env()))
      state args in
    state, (Coq_elpi_utils.of_coq_loc loc, ET.mkApp mainc (EU.list_to_lp_list args) []) in
  let program_ast = get (snd prog) in
  run_and_print ~print:false ~static_check:false program_ast (`Fun query)
;;

let mk_trace_opts start stop preds =
  [ "-trace-on"
  ; "-trace-at"; "run"; string_of_int start; string_of_int stop
  ; "-trace-only"; "run"
  ; "-trace-only"; "select"
  ; "-trace-only"; "assign"
  ; "-trace-maxbox"; "30"
  ] @ List.(flatten (map (fun x -> ["-trace-only-pred"; x]) preds))

let trace start stop preds opts =
  if start = 0 && stop = 0 then trace_options := []
  else trace_options := mk_trace_opts start stop preds @ opts

let print (_,name as prog) args = 
  let args, fname =
    let default_fname = String.concat "." name ^ ".html" in
    let default_blacklist = [
      "elaborator.elpi" ;"reduction.elpi" ;"coq-lib.elpi"
    ] in
    match args with
    | [] -> default_blacklist, default_fname
    | x :: xs -> xs, x in
  let args = List.map API.RawOpaqueData.of_string args in
  let program_ast = get (snd prog) in
  let query_ast = parse_goal (API.Ast.Loc.initial "(print)") "true." in
  let header, api = get_header () in
  let program =
    EC.program ~flags:EC.default_flags header (api :: program_ast) in
  let query = EC.query program query_ast in
  let quotedP, _  = API.Quotation.quote_syntax query in
  let printer_ast = printer () in
  let loc = { API.Ast.Loc.
    source_name = "(Elpi Print)";
    source_start = 0;
    source_stop = 0;
    line = -1;
    line_starts_at = 0; } in
  let q ~depth state =
    assert(depth=0); (* else, we should lift the terms down here *)
    let q = ET.mkApp (ET.Constants.from_stringc "main-quoted")
      (EU.list_to_lp_list quotedP)
      [API.RawOpaqueData.of_string fname; EU.list_to_lp_list args] in
    state, (loc,q) in
  let flags =
   { (cc_flags ()) with EC.allow_untyped_builtin = true } in
  run_and_print ~flags ~print:false ~static_check:false [printer_ast] (`Fun q)
;;

open Proofview
open Tacticals.New

let run_tactic program ist args =
  let args = List.map to_arg args in
  let loc = Coq_elpi_utils.of_coq_loc (fst program) in
  Goal.enter begin fun gl ->
  tclBIND tclEVARMAP begin fun evd -> 
  tclBIND tclENV begin fun env -> 
  let k = Goal.goal gl in
  let query = `Fun (Coq_elpi_HOAS.goal2query env evd k loc ?main:None args ~in_elpi_arg:Coq_elpi_goal_HOAS.in_elpi_arg) in
  let program_ast = get (snd program) in
  match run ~static_check:false program_ast query with
  | API.Execute.Success solution ->
       Coq_elpi_HOAS.tclSOLUTION2EVD solution
  | API.Execute.NoMoreSteps -> tclZEROMSG Pp.(str "elpi run out of steps")
  | _ -> tclZEROMSG Pp.(str "elpi fails")
end end end

let run_in_tactic ?(program = current_program ()) (loc,query) ist args =
  let args = List.map to_arg args in
  Goal.enter begin fun gl ->
  tclBIND tclEVARMAP begin fun evd ->
  tclBIND tclENV begin fun env -> 
  let k = Goal.goal gl in
  let query = `Fun (Coq_elpi_HOAS.goal2query env ~main:query evd k loc args ~in_elpi_arg:Coq_elpi_goal_HOAS.in_elpi_arg) in
  let program_ast = get (snd program) in
  match run ~static_check:true program_ast query with
  | API.Execute.Success solution ->
       Coq_elpi_HOAS.tclSOLUTION2EVD solution
  | API.Execute.NoMoreSteps -> tclZEROMSG Pp.(str "elpi run out of steps")
  | _ -> tclZEROMSG Pp.(str "elpi fails")
end end end


