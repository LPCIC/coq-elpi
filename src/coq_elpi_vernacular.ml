(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module E = Elpi_API
module EC = E.Compile
module EP = E.Parse
module EPP = E.Pp
module EU = E.Extend.Utils
module ET = E.Extend.Data

module Loc = struct
  include Loc
  let pp fmt { fname; line_nb } = Format.fprintf fmt "%s:%d" fname line_nb 
  let compare = Pervasives.compare
end

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
  fast : Elpi_API.Ast.program
}
and src_string = {
  sloc : Loc.t;
  sdata : string;
  sast : Elpi_API.Ast.program
}

  val get : Ploc.t * qualified_name -> Elpi_API.Ast.program list
  
  val set_current_program : ?kind:program_kind -> qualified_name -> unit
  val current_program : unit -> Ploc.t * qualified_name
  val add : src list -> unit

  val init : api:string -> unit
  val load_syntax : string -> unit
  val load_checker : string -> unit
  val load_printer : string -> unit
  val load_command : string -> unit
  val load_tactic : string -> unit

  val ensure_initialized : unit -> unit

  val declare_db : qualified_name -> unit
  val add_db : qualified_name -> Elpi_API.Ast.program list -> unit
  val db_exists : qualified_name -> bool

  val checker : unit -> Elpi_API.Ast.program
  val printer : unit -> Elpi_API.Ast.program

end = struct

type src =
  | File of src_file
  | EmbeddedString of src_string
  | Database of qualified_name
and src_file = {
  fname : string;
  fast : Elpi_API.Ast.program [@compare fun _ _ -> 0 ] [@opaque]
}
and src_string = {
  sloc : Loc.t;
  sdata : string;
  sast : Elpi_API.Ast.program [@compare fun _ _ -> 0] [@opaque]
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
    |> List.filter valid_dir
  in
  "." :: build_dir :: installed_dirs

let lp_syntax_src = Summary.ref ~name:"elpi-lp-syntax" None
let in_lp_syntax_src : string -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-SYNTAX") with
    Libobject.load_function = (fun _ (_,x) -> lp_syntax_src := Some x);
}
let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s
let load_syntax fname =
  let paths = get_paths () in
  let src_dir = 
    try List.find (fun p -> Sys.file_exists (p ^"/"^ fname)) paths
    with Not_found -> 
        CErrors.user_err Pp.(str fname ++ str " not found in paths: " ++ str (String.concat ":" paths))
  in
  let src = load_file (src_dir ^"/"^ fname) in
  lp_syntax_src := Some src;
  Lib.add_anonymous_leaf (in_lp_syntax_src src)

let init () =
  let lp_syntax =
    match !lp_syntax_src with
    | None -> 
        CErrors.user_err Pp.(str"Call Elpi Syntax first, then Elpi Api")
    | Some src ->
        let fname, oc = Filename.open_temp_file "coq" ".elpi" in
        output_string oc src;
        close_out oc;
        fname
  in
  ignore(E.Setup.init ~lp_syntax List.(flatten (map (fun x -> ["-I";x]) (get_paths ()))) ".")

let ensure_initialized =
  let init = lazy(init ()) in
  fun () -> Lazy.force init
;;

let empty_program_ast = Summary.ref ~name:"elpi-empty-program" None
let in_empty_program : src list -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-EMPTY") with
    Libobject.load_function = (fun _ x -> empty_program_ast := Some x);
}
let init ~api =
  ensure_initialized ();
  Lib.add_anonymous_leaf
    (in_empty_program
      [File { fname = "pervasives.elpi";
              fast = EP.program ~no_pervasives:false [] };
       File { fname = api;
              fast = EP.program ~no_pervasives:true [api] } ])
;;

(* We load pervasives and coq-lib once and forall at the beginning *)
let get ?(fail_if_not_exists=false) p =
  ensure_initialized ();
  try SLMap.find p !program_src_ast
  with Not_found ->
    if fail_if_not_exists then
      CErrors.user_err
        Pp.(str "No Elpi Command/Tactic named " ++ pr_qualified_name p)
    else match !empty_program_ast with
      | Some (_,x) -> x
      | None -> CErrors.user_err Pp.(str "Elpi Api must be called first")

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
  | Some name ->
      let obj = in_program (name, v) in
      Lib.add_anonymous_leaf obj
;;


let eq_uuid (fp,kn) (fp1,kn1) =
  Libnames.eq_full_path fp fp1 &&
  Names.KerName.equal kn kn1

let db_exists name = SLMap.mem name !db_name_ast

let append_to_db name (uuid,data as l) =
  try
    let old = SLMap.find name !db_name_ast in
    if List.exists (fun (u1,_) -> eq_uuid u1 uuid) old then old
    else old @ [l]
  with Not_found -> [l]

let in_db : qualified_name * Elpi_API.Ast.program list -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-DB") with
    Libobject.open_function = (fun _ (uuid,(name,p)) ->
      db_name_ast :=
        SLMap.add name (append_to_db name (uuid,p)) !db_name_ast);
    Libobject.cache_function = (fun (uuid,(name,p)) ->
      db_name_ast :=
        SLMap.add name (append_to_db name (uuid,p)) !db_name_ast);
}


let add_db name l = Lib.add_anonymous_leaf (in_db (name,l))
let declare_db name = add_db name []

let lp_command_ast = Summary.ref ~name:"elpi-lp-command" None
let in_lp_command_ast : src -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-COMMAND") with
    Libobject.load_function = (fun _ (_,x) -> lp_command_ast := Some x);
}
let load_command s =
  ensure_initialized ();
  let ast = File { fname = s; fast = EP.program ~no_pervasives:true [s] } in
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
  let ast = File { fname = s; fast = EP.program  ~no_pervasives:true [s] } in
  lp_tactic_ast := Some ast;
  Lib.add_anonymous_leaf (in_lp_tactic_ast ast)
let tactic () =
  match !lp_tactic_ast with
  | None -> CErrors.user_err Pp.(str "Elpi TacticTemplate was not called")
  | Some ast -> ast

let set_current_program ?kind n =
  ensure_initialized ();
  current_program := Some n;
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
  | Some name -> Ploc.dummy, name

let get (_,x) =
  List.(flatten (map ast_of_src (get ~fail_if_not_exists:true x)))
  
let lp_checker_ast = Summary.ref ~name:"elpi-lp-checker" None
let in_lp_checker_ast : Elpi_API.Ast.program -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-CHECKER") with
    Libobject.load_function = (fun _ (_,x) -> lp_checker_ast := Some x);
}
let load_checker s =
  ensure_initialized ();
  let ast = EP.program [s] in
  lp_checker_ast := Some ast;
  Lib.add_anonymous_leaf (in_lp_checker_ast ast)
let checker () =
  match !lp_checker_ast with
  | None -> CErrors.user_err Pp.(str "Elpi Checker was not called")
  | Some ast -> ast

let lp_printer_ast = Summary.ref ~name:"elpi-lp-printer" None
let in_lp_printer_ast : Elpi_API.Ast.program -> Libobject.obj =
  Libobject.declare_object { Libobject.(default_object "ELPI-LP-PRINTER") with
    Libobject.load_function = (fun _ (_,x) -> lp_printer_ast := Some x);
}
let load_printer s =
  ensure_initialized ();
  let ast = EP.program[s] in
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
let load_syntax = load_syntax
let load_printer = load_printer
let load_checker = load_checker
let load_api s = init ~api:s

let run_static_check program query =
  (* We turn a failure into a proper error in etc/coq-elpi_typechecker.elpi *)
  ignore(EC.static_check ~checker:[checker ()] program query)

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
  try
    let new_src_ast = List.map (fun fname ->
      File { fname; fast = EP.program ~no_pervasives:true [fname]}) s in
    add new_src_ast
  with Failure s ->  CErrors.user_err Pp.(str s)
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
  add [EmbeddedString { sloc = Pcoq.to_coqloc loc; sdata = s; sast = new_ast}]
;;

let load_db name =
  if db_exists name then add [Database name]
  else CErrors.user_err
    Pp.(str "Db " ++ pr_qualified_name name ++ str" not found") 

let declare_db name (loc,s) =
  ensure_initialized ();
  declare_db name;
  let pragma = pragma_of_ploc loc in
  let fname, oc = Filename.open_temp_file "coq" ".elpi" in
  output_string oc pragma;
  output_string oc s;
  close_out oc;
  add_db name [EP.program ~no_pervasives:true [fname]]

let run ~static_check ?allow_undeclared_custom_predicates program_ast query =
  let program = EC.program ?allow_undeclared_custom_predicates program_ast in
  let query =
    match query with
    | `Ast query_ast -> EC.query program query_ast
    | `Fun query_builder -> E.Extend.Compile.query program query_builder in
  if static_check then run_static_check program query;
  E.Setup.trace !trace_options;
  E.Execute.once ~max_steps:!max_steps program query
;;

let run_and_print 
  ~print ~static_check ?allow_undeclared_custom_predicates
  program_ast query_ast
=
  let open Elpi_API.Data in let open Coq_elpi_utils in
  match run ~static_check ?allow_undeclared_custom_predicates
        program_ast query_ast
  with
  | E.Execute.Failure -> CErrors.user_err Pp.(str "elpi fails")
  | E.Execute.NoMoreSteps -> CErrors.user_err Pp.(str "elpi run out of steps")
  | E.Execute.Success {
     arg_names; assignments ; constraints; custom_constraints
    } ->
    if print then begin
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
    end;
    (* We add clauses declared via coq-elpi-accumulate *)
    let clauses_to_add =
      E.Extend.CustomConstraint.get Coq_elpi_API.clauses_for_later
        custom_constraints in
    List.iter (fun (dbname,ast) ->
      add_db (Coq_elpi_utils.string_split_on_char '.' dbname) [ast])
      clauses_to_add
;;

let run_in_program ?(program = current_program ()) (loc, query) =
  ensure_initialized ();
  let program_ast = get program in
  let query_ast = `Ast (EP.goal (pragma_of_ploc loc ^ query)) in
  run_and_print ~print:true ~static_check:true program_ast query_ast
;;

let typecheck ?(program = current_program ()) () =
  let program_ast = get program in
  let query_ast = EP.goal "true." in
  let program = EC.program program_ast in
  let query = EC.query program query_ast in
  run_static_check program query
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
    let state, args = CList.fold_map
      (Coq_elpi_goal_HOAS.in_elpi_global_arg ~depth (Global.env()))
      state args in
    state, ET.App(mainc,EU.list_to_lp_list args,[]) in
  let program_ast = get prog in
  run_and_print ~print:false ~static_check:false program_ast (`Fun query)
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

let print (_,name as prog) args = 
  let args, fname =
    let default_fname = String.concat "." name ^ ".html" in
    let default_blacklist = [
      "elaborator.elpi" ;"reduction.elpi" ;"coq-lib.elpi"
      ;"coq-api.elpi" ;"lp-lib.elpi" ;"pervasives.elpi"
    ] in
    match args with
    | [] -> default_blacklist, default_fname
    | x :: xs -> xs, x in
  let args = List.map ET.C.of_string args in
  let program_ast = get prog in
  let query_ast = EP.goal "true." in
  let program = EC.program program_ast in
  let query = EC.query program query_ast in
  let quotedP, _  = E.Extend.Compile.quote_syntax program query in
  let printer_ast = printer () in
  let q ~depth state =
    assert(depth=0); (* else, we should lift the terms down here *)
    let q = ET.App(ET.Constants.from_stringc "main-quoted",quotedP,
      [ET.C.of_string fname; EU.list_to_lp_list args]) in
    state, q in
  run_and_print
    ~print:false ~static_check:false ~allow_undeclared_custom_predicates:true
    [printer_ast] (`Fun q)
;;

open Proofview
open Tacticals.New

let run_tactic program ist args =
  let args = List.map to_arg args in
  Goal.nf_enter begin fun gl -> tclBIND tclEVARMAP begin fun evd -> 
  let k = Goal.goal gl in
  let query = `Fun (Coq_elpi_goal_HOAS.goal2query evd k ?main:None args) in
  let program_ast = get program in
  match run ~static_check:false program_ast query with
  | E.Execute.Success solution ->
       Coq_elpi_goal_HOAS.tclSOLUTION2EVD solution
  | E.Execute.NoMoreSteps -> tclZEROMSG Pp.(str "elpi run out of steps")
  | _ -> tclZEROMSG Pp.(str "elpi fails")
end end

let run_in_tactic ?(program = current_program ()) (loc, query) ist args =
  let args = List.map to_arg args in
  Goal.nf_enter begin fun gl -> tclBIND tclEVARMAP begin fun evd ->
  let k = Goal.goal gl in
  let query = `Fun (Coq_elpi_goal_HOAS.goal2query ~main:query evd k args) in
  let program_ast = get program in
  match run ~static_check:true program_ast query with
  | E.Execute.Success solution ->
       Coq_elpi_goal_HOAS.tclSOLUTION2EVD solution
  | E.Execute.NoMoreSteps -> tclZEROMSG Pp.(str "elpi run out of steps")
  | _ -> tclZEROMSG Pp.(str "elpi fails")
end end


