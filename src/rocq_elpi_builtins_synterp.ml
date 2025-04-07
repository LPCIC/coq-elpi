(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

[%%import "rocq_elpi_config.mlh"]

module API = Elpi.API
module State = API.State
module Conv = API.Conversion
module CConv = API.ContextualConversion
module B = struct
  include API.BuiltInData
  include Elpi.Builtin
end
module Pred = API.BuiltInPredicate
module U = API.Utils

open Names

open Rocq_elpi_utils
open Rocq_elpi_HOAS

let prop = { B.any with Conv.ty = Conv.TyName "prop" }

let id = { B.string with
  API.Conversion.ty = Conv.TyName "id";
  pp_doc = (fun fmt () ->
    Format.fprintf fmt "%% [id] is a name that matters, we piggy back on Elpi's strings.@\n";
    Format.fprintf fmt "%% Note: [name] is a name that does not matter.@\n";
    Format.fprintf fmt "typeabbrev id string.@\n@\n")
}

type scope = ExecutionSite | CurrentModule | Library

let options : (options, API.Data.constraints) CConv.ctx_readback =
  fun ~depth hyps constraints state ->
    state, get_options ~depth hyps state, constraints, []

let scope = let open Conv in let open API.AlgebraicData in declare {
  ty = TyName "scope";
  doc = "Specify to which module the clause should be attached to";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("execution-site","The module inside which the Elpi program is run",N,
      B ExecutionSite,
      M (fun ~ok ~ko -> function ExecutionSite -> ok | _ -> ko ()));
    K("current","The module being defined (see begin/end-module)",N,
      B CurrentModule,
      M (fun ~ok ~ko -> function CurrentModule -> ok | _ -> ko ()));
    K("library","The outermost module (carrying the file name)",N,
      B Library,
      M (fun ~ok ~ko -> function Library -> ok | _ -> ko ()))
  ]
} |> CConv.(!<)

let grafting = let open Conv in let open API.AlgebraicData in declare {
  ty = TyName "grafting";
  doc = "Specify if the clause has to be grafted before, grafted after or replace a named clause";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("before","",A(id,N),
        B (fun x -> (`Before,x)),
        M (fun ~ok ~ko -> function (`Before,x) -> ok x | _ -> ko ()));
    K("after","",A(id,N),
        B (fun x -> (`After,x)),
        M (fun ~ok ~ko -> function (`After,x) -> ok x | _ -> ko ()));
    K("remove","",A(id,N),
      B (fun x -> (`Remove,x)),
      M (fun ~ok ~ko -> function (`Remove,x) -> ok x | _ -> ko ()));
    K("replace","",A(id,N),
      B (fun x -> (`Replace,x)),
      M (fun ~ok ~ko -> function (`Replace,x) -> ok x | _ -> ko ()));
  ]
} |> CConv.(!<)

type clause = string option * ([ `After | `Before | `Remove | `Replace ] * string) option * API.Data.term

let clause = let open Conv in let open API.AlgebraicData in declare {
  ty = TyName "clause";
  doc = {|clauses

A clause like
 :name "foo" :before "bar" foo X Y :- bar X Z, baz Z Y
is represented as
 clause "foo" (before "bar") (pi x y z\ foo x y :- bar x z, baz z y)
that is exactly what one would load in the context using =>.

The name and the grafting specification can be left unspecified.|};
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("clause","",A(B.unspec id,A(B.unspec grafting,A(prop,N))),
      B (fun id graft c -> unspec2opt id, unspec2opt graft, c),
      M (fun ~ok ~ko (id,graft,c) -> ok (opt2unspec id) (opt2unspec graft) c));
  ]
} |> CConv.(!<)

let set_accumulate_to_db_synterp, get_accumulate_to_db_synterp =
  let f = ref (fun ~loc:_ _ -> assert false) in
  (fun x -> f := x),
  (fun () -> !f)

let clauses_for_later_synterp : _ State.component =
  State.declare_component ~name:"rocq-elpi:clauses_for_later" ~descriptor:synterp_state
    ~init:(fun () -> [])
    ~start:(fun x -> x)
    ~pp:(fun fmt l ->
        List.iter (fun (dbname, code,vars,scope) ->
          Format.fprintf fmt "db:%s code:%a scope:%a\n"
              (String.concat "." dbname)
            Elpi.API.Pp.Ast.program code Rocq_elpi_utils.pp_scope scope) l) ()
        
            
type located =
  | LocGref of Names.GlobRef.t
  | LocModule of Names.ModPath.t
  | LocModuleType of Names.ModPath.t
  | LocAbbreviation of Globnames.abbreviation

let located = let open Conv in let open API.AlgebraicData in declare {
  ty = TyName "located";
  doc = "Result of coq.locate-all";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("loc-gref","",A(gref,N),
        B (fun x -> LocGref x),
        M (fun ~ok ~ko -> function LocGref x -> ok x | _ -> ko ()));
    K("loc-modpath","",A(modpath,N),
        B (fun x -> LocModule x),
        M (fun ~ok ~ko -> function LocModule x -> ok x | _ -> ko ()));
    K("loc-modtypath","",A(modtypath,N),
        B (fun x -> LocModuleType x),
        M (fun ~ok ~ko -> function LocModuleType x -> ok x | _ -> ko ()));
    K("loc-abbreviation","",A(abbreviation,N),
        B (fun x -> LocAbbreviation x),
        M (fun ~ok ~ko -> function LocAbbreviation x -> ok x | _ -> ko ()));
  ]
} |> CConv.(!<)
          

let list = B.list
let pair = B.pair
let option = B.option

let invocation_site_loc : API.Ast.Loc.t State.component =
  State.declare_component ~name:"rocq-elpi:invocation-site-loc" ~descriptor:interp_state
  ~pp:(fun fmt x -> Format.fprintf fmt "%a" API.Ast.Loc.pp x)
  ~init:(fun () -> API.Ast.Loc.initial "(should-not-happen)")
  ~start:(fun x -> x) ()
let invocation_site_loc_synterp : API.Ast.Loc.t State.component =
  State.declare_component ~name:"rocq-elpi:invocation-site-loc" ~descriptor:synterp_state
  ~pp:(fun fmt x -> Format.fprintf fmt "%a" API.Ast.Loc.pp x)
  ~init:(fun () -> API.Ast.Loc.initial "(should-not-happen)")
  ~start:(fun x -> x) ()

[%%if elpi >= (1, 20, 0)]
let compat_graft x = x
[%%else]
let compat_graft = Option.map (function `Remove, _ -> nYI "clause removal" | ((`Replace | `Before | `After), _) as x -> x)
[%%endif]

type accumulation_item = qualified_name * API.Ast.program * Id.t list * Rocq_elpi_utils.clause_scope
let accumulate_clauses ~clauses_for_later ~accumulate_to_db ~preprocess_clause ~scope ~dbname clauses ~depth ~options state =
  let invocation_loc = State.get invocation_site_loc_synterp state in
  let loc = invocation_loc in
  let dbname = Rocq_elpi_utils.string_split_on_char '.' dbname in
  let clauses scope =
   clauses |> CList.rev_map (fun (name,graft,clause) ->
     let vars, clause = preprocess_clause ~depth clause in
     let graft = compat_graft graft in
     let clause = U.clause_of_term ?name ?graft ~depth loc clause in
     (dbname,clause,vars,scope)) in
  let local = (options : options).local = Some true in
  let super_global = options.local = Some false in
  match scope with
  | B.Unspec | B.Given ExecutionSite ->
      let scope = if super_global then SuperGlobal else if local then Local else Regular in
      State.update clauses_for_later state (fun l ->
        clauses scope @ l), (), []
  | B.Given Library ->
      if local then CErrors.user_err Pp.(str "coq.elpi.accumulate: library scope is incompatible with @local!");
      State.update clauses_for_later state (fun l ->
        clauses Rocq_elpi_utils.Global @ l), (), []
  | B.Given CurrentModule ->
       let scope = if local then Local else Regular in
       let f = accumulate_to_db in
       f ~loc:(to_coq_loc loc) (clauses scope);
       state, (), []

let locate_module, locate_module_type =
  let open API.BuiltIn in
  let open Pred in
  let open Notation in
  MLCode(Pred("coq.locate-module",
    In(id, "ModName",
    Out(modpath, "ModPath",
    Easy "locates a module.  It's a fatal error if ModName cannot be located. *E*")),
    (fun s _ ~depth ->
    let qualid = Libnames.qualid_of_string s in
    let mp =
      try Nametab.locate_module qualid
      with Not_found ->
        err Pp.(str "Module not found: " ++ Libnames.pr_qualid qualid) in
    !:mp)),
    DocAbove),
  MLCode(Pred("coq.locate-module-type",
    In(id, "ModName",
    Out(modtypath, "ModPath",
    Easy "locates a module.  It's a fatal error if ModName cannot be located. *E*")),
    (fun s _ ~depth ->
      let qualid = Libnames.qualid_of_string s in
      let mp =
        try Nametab.locate_modtype qualid
        with Not_found ->
          err Pp.(str "Module type not found: " ++ Libnames.pr_qualid qualid) in
      !:mp)),
    DocAbove)
    
let modpath_to_path, modtypath_to_path, modpath_to_library, modtypath_to_library =
  let open API.BuiltIn in
  let open Pred in
  let open Notation in
  let open CConv in
  MLCode(Pred("coq.modpath->path",
    In(modpath, "MP",
    Out(B.list B.string, "FullPath",
    Read(unit_ctx, "extract the full kernel name, each component is a separate list item"))),
  (fun mp _ ~depth h c state -> !: (mp2path mp))),
  DocAbove),
  MLCode(Pred("coq.modtypath->path",
    In(modtypath, "MTP",
    Out(B.list B.string, "FullPath",
    Read(unit_ctx, "extract the full kernel name, each component is a separate list item"))),
  (fun mtyp _ ~depth h c state -> !: (mp2path mtyp))),
  DocAbove),
  MLCode(Pred("coq.modpath->library",
    In(modpath, "MP",
    Out(modpath, "LibraryPath",
    Read(unit_ctx, "extract the enclosing module which can be Required"))),
  (fun mp _ ~depth h c state -> !: ModPath.(MPfile (dp mp)))),
  DocAbove),
  MLCode(Pred("coq.modtypath->library",
    In(modtypath, "MTP",
    Out(modpath, "LibraryPath",
    Read(unit_ctx, "extract the enclosing module which can be Required"))),
  (fun mtyp _ ~depth h c state -> !: ModPath.(MPfile (dp mtyp)))),
  DocAbove)

let current_path, current_section_path =
  let open API.BuiltIn in
  let open Pred in
  let open Notation in
  let open CConv in
  MLCode(Pred("coq.env.current-path",
    Out(list B.string, "Path",
    Read(unit_ctx, "lists the current module path")),
  (fun _ ~depth _ _ state -> !: (mp2path (Lib.current_mp ())))),
  DocAbove),
  MLCode(Pred("coq.env.current-section-path",
    Out(list B.string, "Path",
    Read(unit_ctx, "lists the current section path")),
  (fun _ ~depth _ _ state ->
     let base = Lib.current_dirpath false in
     let base_w_sections = Lib.current_dirpath true in
     let sections = Libnames.drop_dirpath_prefix base base_w_sections in
     !: (mp2path (Names.ModPath.MPfile sections)))),
  DocAbove)
  
module SynterpAction = struct
  open Declaremods
  type action =
    | BeginModule of (string * ModPath.t option * (string * ModPath.t) list) * module_params_expr * module_expr module_signature
    | BeginModuleType of (string * (string * ModPath.t) list) * module_params_expr * module_expr list
    | BeginSection of string
    | EndModule of ModPath.t
    | EndModuleType of ModPath.t
    | EndSection
    | ApplyModule of (string * ModPath.t option * ModPath.t * ModPath.t list * Declaremods.inline) * module_params_expr * module_expr list * module_expr module_signature
    | ApplyModuleType of (string * ModPath.t * ModPath.t list * Declaremods.inline) * module_params_expr * module_expr list * module_expr list
    | IncludeModule of (ModPath.t * Declaremods.inline) * module_expr list
    | IncludeModuleType of (ModPath.t * Declaremods.inline) * module_expr list
    | ImportModule of ModPath.t
    | ExportModule of ModPath.t



(*
    | EVernacNotation of { local : bool; decl : Metasyntax.notation_interpretation_decl }
    | EVernacSetOption of { export : bool; key : Goptions.option_name; value : Vernacexpr.option_setting }
  *)

  type t = { action : action; resulting_state : Vernacstate.Synterp.t }
  let synterp_state_after { resulting_state } = resulting_state

  let pp_action = function
  | BeginModule ((id,_,_),_,_) ->
    Pp.(str "begin-module" ++ spc () ++ qstring id)
  | BeginModuleType ((id,_),_,_) ->
    Pp.(str "begin-module-type" ++ spc () ++ qstring id)
  | EndModule mp ->
    Pp.(str "end-module" ++ spc () ++ (str @@ ModPath.to_string mp))
  | EndModuleType mp ->
    Pp.(str "end-module-type" ++ spc () ++ (str @@ ModPath.to_string mp))
  | BeginSection id ->
    Pp.(str "begin-section" ++ spc () ++ qstring id)
  | EndSection ->
    Pp.(str "end-section" ++ spc ())
  | ApplyModule ((id,_,_,_,_),_,_,_) ->
    Pp.(str "apply-module" ++ spc () ++ qstring id)
  | ApplyModuleType ((id,_,_,_),_,_,_) ->
    Pp.(str "apply-module-type" ++ spc () ++ qstring id)
  | IncludeModule ((mp,_),_) ->
    Pp.(str "include-module" ++ spc () ++ (str @@ ModPath.to_string mp))
  | IncludeModuleType ((mp,_),_) ->
    Pp.(str "include-module-type" ++ spc () ++ (str @@ ModPath.to_string mp))
  | ImportModule mp ->
    Pp.(str "import-module" ++ spc () ++ (str @@ ModPath.to_string mp))
  | ExportModule mp ->
    Pp.(str "export-module" ++ spc () ++ (str @@ ModPath.to_string mp))
  let pp { action } = pp_action action

  module Tree = struct
    module Group : sig
      type group

      val group : group API.Conversion.t

      val new_group : string -> group

      val group_name : group -> string

      val debug_pp_group : group -> Pp.t
    end = struct
      type group = {uid : int; name : string}

      let group : group API.Conversion.t =
        let open API.OpaqueData in
        declare {
          name = "group";
          doc = "Synterp action group";
          pp = (fun fmt {uid; name} -> Format.fprintf fmt "{uid=%i;name=%S}" uid name);
          compare = Stdlib.compare;
          hash = Hashtbl.hash;
          hconsed = false;
          constants = [];
        }

      let new_group : string -> group =
        let r = ref (-1) in fun name -> incr r; {uid = !r; name}

      let group_name : group -> string = fun g -> g.name

      let debug_pp_group : group -> Pp.t = fun {uid; name} ->
        Pp.(str name ++ str " (uid=" ++ int uid ++ str ")")
    end
    include Group

    type node =
      | Group of group * tree
      | Action of t

    and tree = node list

    let rec to_list : tree -> t list = fun t ->
      let fn n =
        match n with
        | Group (_, t) -> to_list t
        | Action a -> [a]
      in
      List.concat_map fn t

    let rec debug_pp : tree -> Pp.t = fun ns ->
      let fn acc n =
        let open Pp in
        match n with
        | Action a ->
            acc ++
            str "Action: " ++ pp a ++ fnl ()
        | Group (g, ns) ->
            acc ++
            str "Entering group: " ++ debug_pp_group g ++ fnl () ++
            debug_pp ns ++
            str "Leaving  group: " ++ debug_pp_group g ++ fnl ()
      in
      List.fold_left fn Pp.(str "") ns
  end

  module WZipper = struct
    open Tree

    (* Tree with the outermost item list reversed. *)
    type rev_tree = node list

    type path =
      | P_top
      | P_group of group * rev_tree * path

    type zipper = rev_tree * path

    let empty = ([], P_top)

    let rec collect : zipper -> tree = fun (rev_items, path) ->
      match path with
      | P_top                     -> List.rev rev_items
      | P_group(group, items, path) ->
          let s =
            let items = List.rev rev_items in
            Group(group, items)
          in
          collect (s :: items, path)

    let to_list : zipper -> t list = fun z ->
      Tree.to_list (collect z)

    let add_action : zipper -> t -> zipper = fun (rev_items, path) a ->
      (Action a :: rev_items, path)

    let open_group : zipper -> string -> zipper * group = fun (rev_items, path) group ->
      let group = new_group group in
      (([], P_group(group,rev_items,path)), group)

    let close_group : zipper -> group -> (zipper, [`GroupMismatch of group|`NoGroup]) result = fun (group_items, path) group ->
      match path with
      | P_group (group', items, path) when group' = group ->
        Ok (Group (group, List.rev group_items) :: items, path)
      | P_group (group', _, _) -> Error (`GroupMismatch group')
      | P_top -> Error `NoGroup

  end

  module RZipper = struct
    open Tree

    type path =
      | P_top
      | P_group of group * tree * path

    type zipper = path * tree

    let empty : zipper = (P_top, [])

    let rec collect : zipper -> tree = fun (path, items) ->
      match path with
      | P_top                       -> items
      | P_group(group, group_items, path) ->
          let s = Group(group, items) in
          collect (path, s :: group_items)

    let of_w : WZipper.zipper -> zipper = fun wz ->
      (P_top, WZipper.collect wz)

    let open_group : zipper -> string -> (zipper * group, [`GroupMismatch of group | `LeadingAction of t | `Empty]) result = fun (path, items) group ->
      match items with
      | Group (group', group_items) :: items when group_name group' = group ->
        Ok ((P_group(group', items, path), group_items), group')
      | Group (group', _) :: _ -> Error (`GroupMismatch group')
      | Action a :: _ -> Error (`LeadingAction a)
      | [] -> Error `Empty

    let close_group : zipper -> group -> (zipper, [`GroupMismatch of group| `NoGroup]) result = fun (path, group_items) group ->
      match path with
      | P_group (group', items, path) when group_items = [] && group' = group ->
        Ok (path, items)
      | P_group (group', _, _) -> Error (`GroupMismatch group')
      | P_top -> Error `NoGroup

    let pop_action : zipper -> (t * zipper, [`LeadingGroup of group | `Empty]) result = fun (path, items) ->
      match items with
      | Action a :: items -> Ok (a, (path, items))
      | Group (group, _) :: _ -> Error (`LeadingGroup group)
      | [] -> Error `Empty

    let pop_group : zipper -> string -> (t list * zipper, [`GroupMismatch of group | `LeadingAction of t | `Empty]) result = fun (path, items) group ->
      match items with
      | Group (group', group_items) :: items when group_name group' = group ->
        let actions = Tree.to_list group_items in
        Ok (actions, (path, items))
      | Group (group', _) :: _ -> Error (`GroupMismatch group')
      | Action a :: _ -> Error (`LeadingAction a)
      | [] -> Error `Empty

    let is_empty : zipper -> [`Empty|`Group of group|`Action of t] = fun rz ->
      match pop_action rz with
      | Error `Empty -> `Empty
      | Error (`LeadingGroup g) -> (`Group g)
      | Ok (a, _) -> `Action a
  end

  let action =
    let open Conv in let open API.AlgebraicData in declare {
    ty = TyName "synterp-action";
    doc = "Action executed during the parsing phase (aka synterp)";
    pp = (fun fmt a -> Pp.pp_with fmt (pp_action a));
    constructors = [
      K("begin-module","",A(id,N),B(fun x -> nYI "readback action"),M (fun ~ok ~ko -> function BeginModule ((x,_,_),_,_) -> ok x | _ -> ko ()));
      K("begin-module-type","",A(id,N),B(fun x -> nYI "readback action"),M (fun ~ok ~ko -> function BeginModuleType ((x,_),_,_) -> ok x | _ -> ko ()));
      K("begin-section","",A(id,N),B(fun x -> nYI "readback action"),M (fun ~ok ~ko -> function BeginSection x -> ok x | _ -> ko ()));
      K("end-module","",A(modpath,N),B(fun x -> nYI "readback action"),M (fun ~ok ~ko -> function EndModule x -> ok x | _ -> ko ()));
      K("end-module-type","",A(modtypath,N),B(fun x -> nYI "readback action"),M (fun ~ok ~ko -> function EndModuleType x -> ok x | _ -> ko ()));
      K("end-section","",N,B EndSection,M (fun ~ok ~ko -> function EndSection -> ok | _ -> ko ()));
      K("apply-module-functor","",A(id,N),B(fun x -> nYI "readback action"),M (fun ~ok ~ko -> function ApplyModule ((x,_,_,_,_),_,_,_) -> ok x | _ -> ko ()));
      K("apply-module-type-functor","",A(id,N),B(fun x -> nYI "readback action"),M (fun ~ok ~ko -> function ApplyModuleType ((x,_,_,_),_,_,_) -> ok x | _ -> ko ()));
      K("include-module","",A(modpath,N),B(fun x -> nYI "readback action"),M (fun ~ok ~ko -> function IncludeModule ((x,_),_) -> ok x | _ -> ko ()));
      K("include-module-type","",A(modtypath,N),B(fun x -> nYI "readback action"),M (fun ~ok ~ko -> function IncludeModuleType ((x,_),_) -> ok x | _ -> ko ()));
      K("import-module","",A(modpath,N),B(fun x -> nYI "readback action"),M (fun ~ok ~ko -> function ImportModule x -> ok x | _ -> ko ()));
      K("export-module","",A(modpath,N),B(fun x -> nYI "readback action"),M (fun ~ok ~ko -> function ExportModule x -> ok x | _ -> ko ()));
    ]
  } |> CConv.(!<)
  
  let log : WZipper.zipper State.component =
    State.declare_component ~name:"rocq-elpi:synterp-action-write" ~descriptor:synterp_state
    ~pp:(fun fmt x -> Format.fprintf fmt "<todo>")
    ~init:(fun () -> WZipper.empty)
    ~start:(fun x -> x) ()

  exception Error of Pp.t
  let synterp_interp_error x = raise (Error x)

  let get_parsing_actions_synterp =
    let open API.BuiltIn in
    let open Pred in
    let open Notation in
    let open CConv in
  
    [
      
     MLData action;
     MLData Tree.group;
 
     MLCode (Pred("coq.synterp-actions",
       Out(list action,"A",
       Read(unit_ctx,"Get the list of actions performed during the parsing phase (aka synterp) up to now.")),
       (fun _ ~depth _ _ state -> !: (List.map (fun { action } -> action) @@ List.rev (WZipper.to_list (State.get log state))))),
      DocAbove);

     MLCode(Pred("coq.begin-synterp-group",
       In(id, "ID",
       Out(Tree.group, "Group",
       Full(unit_ctx,"Create and open a new synterp action group with the given name."))),
     (fun name _ ~depth _ _ state ->
       let (s, k) = State.update_return log state (fun wz -> WZipper.open_group wz name) in
       s, ((), Some k), [])),
     DocAbove);

     MLCode(Pred("coq.end-synterp-group",
       In(Tree.group, "Group",
       Full(unit_ctx,"End the synterp action group Group. Group must refer to the most recently openned group.")),
     (fun name ~depth _ _ state ->
       State.update log state (fun wz ->
         match WZipper.close_group wz name with
         | Ok wz -> wz
         | Error `NoGroup ->
           synterp_interp_error Pp.(hov 0 (strbrk ("The command tried to close a synterp action group (" ^ Tree.group_name name ^ ") but there is no group to close.")))
         | Error (`GroupMismatch name') ->
           synterp_interp_error Pp.(hov 0 (strbrk ("The command tried to close a synterp action group (" ^ Tree.group_name name ^ ") but the current group has name " ^ Tree.group_name name' ^ ".")))
         ), (), [])),
     DocAbove);
    ]

  let read : RZipper.zipper State.component =
    State.declare_component ~name:"rocq-elpi:synterp-action-read" ~descriptor:interp_state
    ~pp:(fun fmt x -> Format.fprintf fmt "<todo>")
    ~init:(fun () -> RZipper.empty)
    ~start:(fun x -> x) ()


  let push action state =
    State.update log state (fun l -> WZipper.add_action l { action; resulting_state = Vernacstate.Synterp.freeze () })

  let common_err = "Interp actions must match synterp actions. For example if a module was imported during the synterp phase, then it must also be imported during the interp one."

  let pop case state =
    State.update_return read state (fun rz ->
      match RZipper.pop_action rz with
      | Ok (a, rz) -> Vernacstate.Synterp.unfreeze a.resulting_state; rz, a.action
      | Error (`LeadingGroup g) ->
        synterp_interp_error Pp.(hov 0 (strbrk ("The command created an action group (" ^ Tree.group_name g ^ ") in the synterp phase but did not open the group in the interp phase.")))
      | Error `Empty ->
        synterp_interp_error Pp.(hov 0 (strbrk ("The command did perform no (more) actions during the parsing phase (aka synterp), while during the execution phase (aka interp) it tried to perform a") ++ spc() ++ str case ++ spc() ++ str "action." ++ spc() ++ strbrk common_err)))

  type 'a replay = 'a -> State.t -> State.t * ModPath.t option 

  [%%if coq = "8.20"]
  let interp_close_section = Lib.Interp.close_section
  [%%else]
  let interp_close_section = Declaremods.Interp.close_section
  [%%endif]

  let replay1 action state =
    match action with
    | BeginModule((name,_,_),binders_ast,ty) ->
        if Global.sections_are_opened () then
          err Pp.(str"This code cannot be run within a section since it opens a module");
        let id = Id.of_string name in
        let mp = Declaremods.Interp.start_module None id binders_ast ty in
        let loc = to_coq_loc @@ State.get invocation_site_loc state in
        Dumpglob.dump_moddef ~loc mp "mod";
        (state, None)
    | BeginModuleType((name,_),binders_ast,ty) ->
        if Global.sections_are_opened () then
          err Pp.(str"This code cannot be run within a section since it opens a module");
        let id = Id.of_string name in
        let mp = Declaremods.Interp.start_modtype id binders_ast ty in
        let loc = to_coq_loc @@ State.get invocation_site_loc state in
        Dumpglob.dump_moddef ~loc mp "modtype";
        (state, None)
    | EndModule mp ->
        let mp1 = Declaremods.Interp.end_module () in
        assert(ModPath.equal mp mp1);
        (Rocq_elpi_HOAS.grab_global_env_drop_sigma state, Some mp)
    | EndModuleType mp ->
        let mp1 = Declaremods.Interp.end_modtype () in
        assert(ModPath.equal mp mp1);
        (Rocq_elpi_HOAS.grab_global_env_drop_sigma state, Some mp)
    | BeginSection name ->
        let id = Id.of_string name in
        let lid = CAst.make ~loc:(to_coq_loc @@ State.get invocation_site_loc state) id in
        Dumpglob.dump_definition lid true "sec";
        Lib.Interp.open_section id;
        (state, None)
    | EndSection ->
        let loc = to_coq_loc @@ State.get invocation_site_loc state in
        Dumpglob.dump_reference ~loc
          (DirPath.to_string (Lib.current_dirpath true)) "<>" "sec";
        interp_close_section ();
        (Rocq_elpi_HOAS.grab_global_env_drop_sigma state, None)
    | ImportModule mp ->
        Declaremods.import_module ~export:Lib.Import Libobject.unfiltered mp;
        (state, None)
    | ExportModule mp ->
        Declaremods.Interp.import_module ~export:Lib.Export Libobject.unfiltered mp;
        (state, None)
    | IncludeModule(_,me) ->
        Declaremods.Interp.declare_include me;
        (state, None)
    | IncludeModuleType (_,me) ->
        Declaremods.Interp.declare_include me;
        (state, None)
    | ApplyModule ((name,_,_,_,_),params,mexpr_ast,ty) ->
        if Global.sections_are_opened () then
          err Pp.(str"This elpi code cannot be run within a section since it defines a module");
        let id = Id.of_string name in
        let mp = Declaremods.Interp.declare_module id params ty mexpr_ast in
        let loc = to_coq_loc @@ State.get invocation_site_loc state in
        Dumpglob.dump_moddef ~loc mp "mod";
        (state, Some mp)
    | ApplyModuleType ((name,_,_,_),params,mexpr_ast1,mexpr_ast2) ->
        if Global.sections_are_opened () then
          err Pp.(str"This elpi code cannot be run within a section since it defines a module");
        let id = Id.of_string name in
        let mp = Declaremods.Interp.declare_modtype id params mexpr_ast1 mexpr_ast2 in
        let loc = to_coq_loc @@ State.get invocation_site_loc state in
        Dumpglob.dump_moddef ~loc mp "modtype";
        (state, Some mp)

  let replay_group state name =
    let rz = State.get read state in
    let (group, rz) =
      match RZipper.pop_group rz name with
      | Ok res -> res
      | Error `Empty ->
        synterp_interp_error Pp.(hov 0 (strbrk ("The command tried to replay an action group (" ^ name ^ ") in the interp phase but there are no remaining synterp actions or groups.")))
      | Error (`LeadingAction a) ->
        synterp_interp_error Pp.(hov 0 (strbrk ("The command tried to replay an action group (" ^ name ^ ") in the interp phase but the next synterp action (") ++ pp a ++ strbrk ("is an action and not a group.")))
      | Error (`GroupMismatch name') ->
        synterp_interp_error Pp.(hov 0 (strbrk ("The command tried to replay an action group (" ^ name ^ ") in the interp phase but the next action group is named " ^ Tree.group_name name' ^ ".")))
    in
    let state = State.set read state rz in
    List.fold_left (fun state {action; resulting_state} ->
      Vernacstate.Synterp.unfreeze resulting_state;
      fst (replay1 action state)
    ) state group

  let wrong_synterp_action x a =
    synterp_interp_error Pp.(v 0 (str "At parsing time, the program did perform action:" ++ fnl () ++
      h (pp_action a) ++ fnl () ++
      str"while at execution time it tried to perform action:" ++ fnl () ++
      str x ++ fnl () ++
      h (strbrk common_err)))
  let check_inconsistent_synterp_action eq ppx ppy x y a =
    if not (eq x y) then
      synterp_interp_error Pp.(v 0 (str "The program did perform action:" ++ fnl () ++
      h (pp_action a) ++ fnl () ++
      str"at both parsing and execution time, but on different inputs:" ++ fnl () ++
      v 0 (str "- " ++ ppx x ++ str " (synterp)"
           ++ cut () ++
           str "- " ++ ppy y ++ str " (interp)") ++ fnl () ++
      h (strbrk common_err)))
  
  let check_inconsistent_synterp_action_string =
    check_inconsistent_synterp_action (=) Pp.str Pp.str
  let check_inconsistent_synterp_action_modpath =
    check_inconsistent_synterp_action ModPath.equal (fun x -> Pp.str @@ ModPath.to_string x) (fun x -> Pp.str @@ ModPath.to_string x)

  let eqU f x = function
   | B.Given y -> f x y
   | B.Unspec -> true

  let check_inconsistent_synterp_action_applym =
    let eq (n1,t1,f1,a1,i1) (n2,t2,f2,a2,i2) =
      n1 = n2 &&
      eqU (Option.equal ModPath.equal) t1 t2 && 
      eqU ModPath.equal f1 f2 &&
      eqU (CList.equal ModPath.equal) a1 a2 &&
      eqU (=) i1 i2
    in
    let ppx (n,t,f,a,i) = Pp.str n in
    let ppy (n,t,f,a,i) = Pp.str n in
    check_inconsistent_synterp_action eq ppx ppy

  let check_inconsistent_synterp_action_applymt =
    let eq (n1,f1,a1,i1) (n2,f2,a2,i2) =
      n1 = n2 &&
      eqU ModPath.equal f1 f2 &&
      eqU (CList.equal ModPath.equal) a1 a2 &&
      eqU (=) i1 i2
    in
    let ppx (n,f,a,i) = Pp.str n in
    let ppy (n,f,a,i) = Pp.str n in
    check_inconsistent_synterp_action eq ppx ppy
    
  let check_inconsistent_synterp_action_m =
    let eq (n1,t1,a1) (n2,t2,a2) =
      n1 = n2 &&
      eqU (Option.equal ModPath.equal) t1 t2 && 
      eqU (CList.equal (fun (x1,y1) (x2,y2) -> x1 = x2 && ModPath.equal y1 y2)) a1 a2
    in
    let ppx (n,t,a) = Pp.str n in
    let ppy (n,t,a) = Pp.str n in
    check_inconsistent_synterp_action eq ppx ppy
  
  let check_inconsistent_synterp_action_mt =
    let eq (n1,a1) (n2,a2) =
      n1 = n2 &&
      eqU (CList.equal (fun (x1,y1) (x2,y2) -> x1 = x2 && ModPath.equal y1 y2)) a1 a2
    in
    let ppx (n,a) = Pp.str n in
    let ppy (n,a) = Pp.str n in
    check_inconsistent_synterp_action eq ppx ppy

  let check_inconsistent_synterp_action_includem =
    let eq (n1,t1) (n2,t2) =
      ModPath.equal n1 n2 &&
      eqU (=) t1 t2
    in
    let ppx (n,a) = Pp.str @@ ModPath.to_string n in
    let ppy (n,a) = Pp.str @@ ModPath.to_string n in
    check_inconsistent_synterp_action eq ppx ppy
      
  let pop_BeginModule (id,_,_ as x) state =
    let case = Printf.sprintf "begin-module \"%s\"" id in
    let state, a = pop case state in
    match a with
    | BeginModule(x',_,_) -> check_inconsistent_synterp_action_m x' x a; replay1 a state
    | _ -> wrong_synterp_action case a
  let pop_BeginModuleType (id, _ as x') state =
    let case = Printf.sprintf "begin-module-type \"%s\"" id in
    let state, a = pop case state in
    match a with
    | BeginModuleType(x,_,_) -> check_inconsistent_synterp_action_mt x x' a; replay1 a state
    | _ -> wrong_synterp_action case a
  let pop_BeginSection x' state =
    let case = Printf.sprintf "begin-section \"%s\"" x' in
    let state, a = pop case state in
    match a with
    | BeginSection x -> check_inconsistent_synterp_action_string x x' a; replay1 a state
    | _ -> wrong_synterp_action case a
  let pop_EndModule () state =
    let case = "end-module" in
    let state, a = pop case state in
    match a with
    | EndModule _ -> replay1 a state
    | _ -> wrong_synterp_action case a
  let pop_EndModuleType () state =
    let case = "end-module-type" in
    let state, a = pop case state in
    match a with
    | EndModuleType _ -> replay1 a state
    | _ -> wrong_synterp_action case a
  let pop_EndSection () state =
    let case = "end-section" in
    let state, a = pop case state in
    match a with
    | EndSection -> replay1 a state
    | _ -> wrong_synterp_action case a
  let pop_ApplyModule a' state =
    let case = "apply-module" in
    let state, ac = pop case state in
    match ac with
    | ApplyModule (a,_,_,_) -> check_inconsistent_synterp_action_applym a a' ac; replay1 ac state
    | _ -> wrong_synterp_action case ac
  let pop_ApplyModuleType a' state =
    let case = "apply-module-type" in
    let state, ac = pop case state in
    match ac with
    | ApplyModuleType (a,_,_,_) -> check_inconsistent_synterp_action_applymt a a' ac; replay1 ac state
    | _ -> wrong_synterp_action case ac
  let pop_IncludeModule a' state =
    let case = "include-module" in
    let state, ac = pop case state in
    match ac with
    | IncludeModule (a,_) -> check_inconsistent_synterp_action_includem a a' ac; replay1 ac state
    | _ -> wrong_synterp_action case ac
  let pop_IncludeModuleType a' state =
    let case = "include-module-type" in
    let state, ac = pop case state in
    match ac with
    | IncludeModuleType (a,_) -> check_inconsistent_synterp_action_includem a a' ac; replay1 ac state
    | _ -> wrong_synterp_action case ac
            
  let pop_ImportModule a' state =
    let case = "import-module" in
    let state, ac = pop case state in
    match ac with
    | ImportModule a -> check_inconsistent_synterp_action_modpath a a' ac; replay1 ac state
    | _ -> wrong_synterp_action case ac
  let pop_ExportModule a' state =
    let case = "export-module" in
    let state, ac = pop case state in
    match ac with
    | ExportModule a -> check_inconsistent_synterp_action_modpath a a' ac; replay1 ac state
    | _ -> wrong_synterp_action case ac


  let builtins_interp =
    let open API.BuiltIn in
    let open Pred in
    let open Notation in
    let open CConv in
  
    [
      
    LPDoc "-- Synterp ----------------------------------------------------------";
    
    MLData action;
    MLData Tree.group;

    MLCode (Pred("coq.next-synterp-action",
        Out(action,"A",
        Read(unit_ctx,"Get the next action performed during parsing (aka synterp), that is also the next action to be performed during execution (aka interp). See also coq.replay-synterp-action")),
        (fun _ ~depth _ _ state -> !: (
            match RZipper.pop_action (State.get read state) with
            | Ok ({ action }, _) -> action
            | _ -> raise No_clause
          ))),
      DocAbove);

    MLCode(Pred("coq.replay-synterp-action-group",
      In(id, "ID",
      Full(unit_ctx,"Execute all actions of synterp action group ID. ID must be the name of the next group, it must not be opened already, and there must not be any actions before it.")),
    (fun name ~depth _ _ state ->
      let state = replay_group state name in
      state, (), [])),
    DocAbove);

    MLCode(Pred("coq.begin-synterp-group",
      In(id, "ID",
      Out(Tree.group, "Group",
      Full(unit_ctx,"Match a begin-synterp-group synterp operation. ID must be the name of the next synterp action group and there must not be any actions before it."))),
    (fun name _ ~depth _ _ state ->
      let (s, k) =
        State.update_return read state (fun rz ->
          match RZipper.open_group rz name with
          | Ok rz -> rz
          | Error `Empty ->
            synterp_interp_error Pp.(hov 0 (strbrk ("The command tried to match a begin-synterp-group operation on group " ^ name ^ " but there are no groups or actions left in the current state.")))
          | Error (`GroupMismatch name') ->
            synterp_interp_error Pp.(hov 0 (strbrk ("The command tried to match a begin-synterp-group operation on group " ^ name ^ " but the next group to match has name " ^ Tree.group_name name' ^ ".")))
          | Error (`LeadingAction a) ->
            synterp_interp_error Pp.(hov 0 (strbrk ("The command tried to match a begin-synterp-group operation on group " ^ name ^ " but the next item to match is an action (") ++ pp a ++ strbrk "), not a group."))
        )
      in s, ((), Some k), [])),
    DocAbove);

    MLCode(Pred("coq.end-synterp-group",
      In(Tree.group, "Group",
      Full(unit_ctx,"Match a end-synterp-group synterp operation. Group must be the currently opened synterp action group and the group must not have any more synterp actions or groups left to replay.")),
    (fun name ~depth _ _ state ->
      State.update read state (fun rz ->
        match RZipper.close_group rz name with
        | Ok wz -> wz
        | Error `NoGroup ->
          synterp_interp_error Pp.(hov 0 (strbrk ("The command tried to match an end-synterp-group operation on group " ^ Tree.group_name name ^ " but there is no group to end.")))
        | Error (`GroupMismatch name') ->
          synterp_interp_error Pp.(hov 0 (strbrk ("The command tried to match an end-synterp-group operation on group " ^ Tree.group_name name ^ " but the next group to close has name " ^ Tree.group_name name' ^ ".")))
        ), (), [])),
    DocAbove);

    ]

end

let rec dirpath_of_modpath = function
| ModPath.MPfile d -> DirPath.repr d
| ModPath.MPdot(mp,l) -> Label.to_id l :: dirpath_of_modpath mp
| _ -> assert false

let module_ast_of_modpath x =
  let open Libnames in
  qualid_of_dirpath (DirPath.make (dirpath_of_modpath x))

let module_ast_of_modtypath x =
  let open Constrexpr in let open Libnames in
  CAst.make @@ CMident (qualid_of_dirpath (DirPath.make (dirpath_of_modpath x))),
  Declaremods.DefaultInline

let attribute_decl a = let open API.AlgebraicData in Decl {
  ty = Conv.TyName "attribute";
  doc = "Generic attribute";
  pp = (fun fmt a -> Format.fprintf fmt "TODO");
  constructors = [
    K("attribute","",A(B.string,A(a,N)),
      B (fun s a -> s,a),
      M (fun ~ok ~ko -> function (s,a) -> ok s a));
  ]
}
let attribute_alloc = let open API.AlgebraicData in
  allocate_constructors (Param (fun a -> attribute_decl a))

let attribute a = let open API.AlgebraicData in declare_allocated attribute_alloc (attribute_decl a) |> CConv.(!<)

type attribute_data =
  | AttributeString of string
  | AttributeLoc of API.Ast.Loc.t
type attribute_value =
  | AttributeEmpty
  | AttributeList of (string * attribute_value) list
  | AttributeLeaf of attribute_data

let attribute_value = let open API.AlgebraicData in let open CConv in declare {
  ty = Conv.TyName "attribute-value";
  doc = "Generic attribute value";
  pp = (fun fmt a -> Format.fprintf fmt "TODO");
  constructors = [
    K("leaf-str","",A(B.string,N),
      B (fun s ->
          if s = "" then AttributeEmpty
          else AttributeLeaf (AttributeString s)),
      M (fun ~ok ~ko -> function
          | AttributeEmpty -> ok ""
          | AttributeLeaf (AttributeString x) -> ok x
          | _ -> ko ()));
    K("leaf-loc","",A(B.loc,N),
      B (fun s ->
          AttributeLeaf (AttributeLoc s)),
      M (fun ~ok ~ko -> function
           | AttributeLeaf (AttributeLoc x) -> ok x
           | _ -> ko ()));
    K("node","",C((fun self -> !> (B.list (attribute (!< self)))),N),
      B (fun l -> AttributeList l),
      M (fun ~ok ~ko -> function AttributeList l -> ok l | _ -> ko ())
    )
  ]
} |> CConv.(!<)

let attribute = attribute attribute_value

[%%if coq = "8.20"]
let synterp_close_section = Lib.Synterp.close_section
[%%else]
let synterp_close_section = Declaremods.Synterp.close_section
[%%endif]

let coq_synterp_builtins =
  let open API.BuiltIn in
  let open Pred in
  let open Notation in
  let open CConv in
  [
    LPCode Rocq_elpi_builtins_arg_HOAS.code;
    LPDoc "Coq terms are not visible at synterp time, they are always holes";
    LPCode "kind term type.";
    LPCode "kind gref type.";
    LPCode "kind abbreviation type.";
    LPDoc "-- Parsing time APIs ----------------------------------------------------";
    MLData id;
    MLData modpath;
    MLData modtypath;
    locate_module;
    locate_module_type;
    MLData located;
  MLCode(Pred("coq.locate-all",
    In(id, "Name",
    Out(B.list located,  "Located",
    Easy {|finds all possible meanings of a string. Does not fail.|})),
  (fun s _ ~depth ->
      let qualid = Libnames.qualid_of_string s in
      let l = ref [] in
      let add x = l := !l @ [x] in
      begin
        try add @@ LocModule (Nametab.locate_module qualid)
        with Not_found -> ()
      end;
      begin
        try add @@ LocModuleType (Nametab.locate_modtype qualid)
        with Not_found -> ()
      end;
    !: !l)),
  DocAbove);

  MLData module_inline_default;
  
  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.begin-module-functor",
    In(id, "The name of the functor",
    In(option modtypath, "Its module type",
    In(list (pair id modtypath), "Parameters of the functor",
    Full(unit_ctx, "Starts a functor *E*")))),
  (fun name mp binders ~depth _ _  state ->
     if Lib.sections_are_opened () then
       err Pp.(str"This code cannot be run within a section since it opens a module");
     let ty =
       match mp with
       | None -> Declaremods.Check []
       | Some mp -> Declaremods.(Enforce (module_ast_of_modtypath mp)) in
     let id = Id.of_string name in
     let binders_ast =
       List.map (fun (id, mty) ->
         [CAst.make (Id.of_string id)], (module_ast_of_modtypath mty))
         binders in
     let _, x, y = Declaremods.Synterp.start_module None id binders_ast ty in
     let state = SynterpAction.(push (BeginModule((name,mp,binders), x, y))) state in
   
     state, (), [])),
  DocNext);

  LPCode {|
pred coq.env.begin-module i:id, i:option modtypath.
coq.env.begin-module Name MP :-
  coq.env.begin-module-functor Name MP [].
|};

  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.end-module",
    Out(modpath, "ModPath",
    Full(unit_ctx, "end the current module that becomes known as ModPath *E*")),
  (fun _ ~depth _ _ state ->
    let mp0 = Lib.current_mp () in
     let mp = Declaremods.Synterp.end_module () in
     let state = SynterpAction.(push (EndModule mp)) state in
     assert(ModPath.equal mp0 mp);
     state, !: mp, [])),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.begin-module-type-functor",
    In(id, "The name of the functor",
    In(list (pair id modtypath), "The parameters of the functor",
    Full(unit_ctx,"Starts a module type functor *E*"))),
  (fun name binders ~depth _ _ state ->
     if Lib.sections_are_opened () then
      err Pp.(str"This code cannot be run within a section since it opens a module");
     let id = Id.of_string name in
     let binders_ast =
       List.map (fun (id, mty) ->
         [CAst.make (Id.of_string id)], (module_ast_of_modtypath mty))
         binders in
     let _,y,z = Declaremods.Synterp.start_modtype id binders_ast [] in
     let state = SynterpAction.(push (BeginModuleType((name,binders),y,z))) state in

      state, (), [])),
  DocNext);

  LPCode {|
pred coq.env.begin-module-type i:id.
coq.env.begin-module-type Name :-
  coq.env.begin-module-type-functor Name [].
|};

  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.end-module-type",
    Out(modtypath, "ModTyPath",
    Full(unit_ctx, "end the current module type that becomes known as ModPath *E*")),
  (fun _ ~depth _ _ state ->
     let mp0 = Lib.current_mp () in
     let _mp = Declaremods.Synterp.end_modtype () in
     (* BUG in COQ assert(ModPath.equal mp0 mp);*)
     let state = SynterpAction.(push (EndModuleType(mp0))) state in
     state, !: mp0, [])),
  DocAbove);

  MLCode(Pred("coq.env.apply-module-functor",
    In(id, "The name of the new module",
    In(option modtypath, "Its module type",
    In(modpath, "The functor being applied",
    In(list modpath, "Its arguments",
    In(module_inline_default, "Arguments inlining",
    Out(modpath, "The modpath of the new module",
    Full(unit_ctx, "Applies a functor *E*"))))))),
  (fun name mp f arguments inline _ ~depth _ _ state ->
     let ty =
       match mp with
       | None -> Declaremods.Check []
       | Some mp -> Declaremods.(Enforce (module_ast_of_modtypath mp)) in
     let id = Id.of_string name in
     let fa = CAst.make (Constrexpr.CMident (module_ast_of_modpath f)) in
     let mexpr_ast_args = List.map module_ast_of_modpath arguments in
      let mexpr_ast =
         List.fold_left (fun hd arg -> CAst.make (Constrexpr.CMapply(hd,arg))) fa mexpr_ast_args in
      let mp1, a,b,c = Declaremods.Synterp.declare_module id [] ty [mexpr_ast,inline] in
      let state = SynterpAction.(push (ApplyModule((name,mp,f,arguments,inline),a,b,c))) state in
      state, !: mp1, [])),
  DocNext);
  
  MLCode(Pred("coq.env.apply-module-type-functor",
    In(id, "The name of the new module type",
    In(modtypath, "The functor",
    In(list modpath, "Its arguments",
    In(module_inline_default, "Arguments inlining",
    Out(modtypath, "The modtypath of the new module type",
    Full(unit_ctx, "Applies a type functor *E*")))))),
  (fun name f arguments inline _ ~depth _ _ state ->
     let id = Id.of_string name in
     let fa,_ = module_ast_of_modtypath f in
     let mexpr_ast_args = List.map module_ast_of_modpath arguments in
     let mexpr_ast =
        List.fold_left (fun hd arg -> CAst.make (Constrexpr.CMapply(hd,arg))) fa mexpr_ast_args in
     let mp, a,b,c = Declaremods.Synterp.declare_modtype id [] [] [mexpr_ast,inline] in
      let state = SynterpAction.(push (ApplyModuleType((name,f,arguments,inline),a,c,b (* c,b is intended, see Coq API*)))) state in
      state, !: mp, [])),
  DocNext);

  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.include-module",
    In(modpath, "ModPath",
    In(module_inline_default, "Inline",
    Full(unit_ctx, "is like the vernacular Include, Inline can be omitted *E*"))),
  (fun mp inline ~depth _ _ state ->
     let fpath = match mp with
       | ModPath.MPdot(mp,l) ->
           Libnames.make_path (ModPath.dp mp) (Label.to_id l)
       | _ -> nYI "functors" in
     let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
     let i = CAst.make tname, inline in
     let me = Declaremods.Synterp.declare_include [i] in
     let state = SynterpAction.(push (IncludeModule ((mp,inline),me))) state in
     state, (), [])),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.include-module-type",
    In(modtypath, "ModTyPath",
    In(module_inline_default, "Inline",
    Full(unit_ctx, "is like the vernacular Include Type, Inline can be omitted  *E*"))),
  (fun mp inline  ~depth _ _ state ->
     let fpath = Nametab.path_of_modtype mp in
     let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
     let i = CAst.make tname, inline in
     let me = Declaremods.Synterp.declare_include [i] in
     let state = SynterpAction.(push (IncludeModuleType ((mp,inline),me))) state in
     state, (), [])),
  DocAbove);

  MLCode(Pred("coq.env.import-module",
    In(modpath, "ModPath",
    Full(unit_ctx, "is like the vernacular Import *E*")),
  (fun mp ~depth _ _ state ->
     Declaremods.Synterp.import_module ~export:Lib.Import Libobject.unfiltered mp;
     let state = SynterpAction.(push (ImportModule mp)) state in
     state, (), [])),
  DocAbove);

  MLCode(Pred("coq.env.export-module",
    In(modpath, "ModPath",
    Full(unit_ctx, "is like the vernacular Export *E*")),
  (fun mp ~depth _ _ state ->
     Declaremods.Synterp.import_module ~export:Lib.Export Libobject.unfiltered mp;
     let state = SynterpAction.(push (ExportModule mp)) state in
     state, (), [])),
  DocAbove);

  MLCode(Pred("coq.env.begin-section",
    In(id, "Name",
    Full(unit_ctx, "starts a section named Name *E*")),
  (fun name ~depth _ _ state ->
     let id = Id.of_string name in
     Lib.Synterp.open_section id;
     let state = SynterpAction.(push (BeginSection name)) state in
     state, (), [])),
  DocAbove);

  MLCode(Pred("coq.env.end-section",
    Full(unit_ctx, "end the current section *E*"),
  (fun ~depth _ _ state ->
     synterp_close_section ();
     let state = SynterpAction.(push EndSection) state in
     state, (), [])),
  DocAbove);

  modpath_to_path; modtypath_to_path; modpath_to_library; modtypath_to_library;
  current_path; current_section_path;
  
  MLData clause;
  MLData grafting;
  MLData scope;

  LPCode {|
% see coq.elpi.accumulate-clauses
pred coq.elpi.accumulate i:scope, i:id, i:clause.
coq.elpi.accumulate S N C :- coq.elpi.accumulate-clauses S N [C].
|};

  MLCode(Pred("coq.elpi.accumulate-clauses",
    In(B.unspec scope, "Scope",
    In(id, "DbName",
    In(B.list clause, "Clauses",
    Full (options , {|
Declare that, once the program is over, the given clauses has to be
added to the given db (see Elpi Db).
Clauses usually belong to Coq modules: the Scope argument lets one
select which module:
- execution site (default) is the module in which the pogram is
  invoked
- current is the module currently being constructed (see
  begin/end-module)
- library is the current file (the module that is named after the file)
The clauses are visible as soon as the enclosing module is Imported.
Clauses cannot be accumulated inside functors.
Supported attributes:
- @local! (default: false, discard at the end of section or module)
- @global! (default: false, always active, only if Scope is execution-site, discouraged)|} )))),
  (fun scope dbname clauses ~depth options _ state ->
    accumulate_clauses
      ~clauses_for_later:clauses_for_later_synterp
      ~accumulate_to_db:(get_accumulate_to_db_synterp())
      ~preprocess_clause:(fun ~depth x -> [], x)
      ~scope ~dbname clauses ~depth ~options state)),
  DocAbove);

  ] @ SynterpAction.get_parsing_actions_synterp @ [
  MLData attribute_value;
  MLData attribute;
  ]

let synterp_api_doc = ". bla bla"

