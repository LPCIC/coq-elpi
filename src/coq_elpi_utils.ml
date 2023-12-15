(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API

let of_coq_loc l = {
  API.Ast.Loc.source_name =
    (match l.Loc.fname with Loc.InFile {file} -> file | Loc.ToplevelInput -> "(stdin)");
  source_start = l.Loc.bp;
  source_stop = l.Loc.ep;
  line = l.Loc.line_nb;
  line_starts_at = l.Loc.bol_pos;
}
let to_coq_loc {
  API.Ast.Loc.source_name = source_name;
  line = line;
  line_starts_at = line_starts_at;
  source_start = source_start;
  source_stop = source_stop;
} = Loc.create (Loc.InFile {dirpath=None; file=source_name}) line line_starts_at source_start source_stop

let err ?loc msg =
  let loc = Option.map to_coq_loc loc in
  CErrors.user_err ?loc msg

exception LtacFail of int * Pp.t

let ltac_fail_err ?loc n msg =
  let loc = Option.map to_coq_loc loc in
  Loc.raise ?loc (LtacFail(n,msg))

let feedback_fmt_write, feedback_fmt_flush =
  let b = Buffer.create 2014 in
  Buffer.add_substring b,
  (fun () ->
     let s = Buffer.to_bytes b in
     let s =
       let len = Bytes.length s in
       if len > 0 && Bytes.get s (len - 1) = '\n'
       then Bytes.sub_string s 0 (len - 1)
       else Bytes.to_string s in
     Feedback.msg_notice Pp.(str s);
     Buffer.clear b)

let elpi_cat = CWarnings.create_category ~name:"elpi" ()
let elpi_depr_cat =
  CWarnings.create_category
    ~from:[elpi_cat;CWarnings.CoreCategories.deprecated]
    ~name:"elpi.deprecated" ()

let () = API.Setup.set_error (fun ?loc s -> err ?loc Pp.(str s))
let () = API.Setup.set_anomaly (fun ?loc s -> err ?loc Pp.(str s))
let () = API.Setup.set_type_error (fun ?loc s -> err ?loc Pp.(str s))
let warn = CWarnings.create ~name:"runtime" ~category:elpi_cat Pp.str
let () = API.Setup.set_warn (fun ?loc x -> warn ?loc:(Option.map to_coq_loc loc) x)
let () = API.Setup.set_std_formatter (Format.make_formatter feedback_fmt_write feedback_fmt_flush)
let () = API.Setup.set_err_formatter (Format.make_formatter feedback_fmt_write feedback_fmt_flush)


let nYI s = err Pp.(str"Not Yet Implemented: " ++ str s)

let pp2string pp x =
  let b = Buffer.create 80 in
  let fmt = Format.formatter_of_buffer b in
  Format.pp_set_margin fmt (Option.default 80 (Topfmt.get_margin ()));
  Format.fprintf fmt "%a%!" pp x;
  Buffer.contents b

module C = Constr
module EC = EConstr

let safe_destApp sigma t =
  match EC.kind sigma t with
  | C.App(hd,args) -> EC.kind sigma hd, args
  | x -> x, [||]

let mkGHole =
  DAst.make
    (Glob_term.(GHole GInternalHole))
    
let mkApp ~depth t l =
  match l with
  | [] -> t
  | x :: xs ->
    match API.RawData.look ~depth t with
    | API.RawData.Const c -> API.RawData.mkApp c x xs
    | _ -> assert false

let string_split_on_char c s =
  let len = String.length s in
  let rec aux n x =
    if x = len then [String.sub s n (x-n)]
    else if s.[x] = c then String.sub s n (x-n) :: aux (x+1) (x+1)
    else aux n (x+1)
  in
    aux 0 0

let rec mk_gforall ty = function
  | (name,r,bk,None,t) :: ps -> DAst.make @@ Glob_term.GProd(name,r,bk,t, mk_gforall ty ps)
  | (name,r,_,Some bo,t) :: ps -> DAst.make @@ Glob_term.GLetIn(name,r,bo,Some t, mk_gforall ty ps)
  | [] -> ty

let rec mk_gfun ty = function
  | (name,r,bk,None,t) :: ps -> DAst.make @@ Glob_term.GLambda(name,r,bk,t, mk_gfun ty ps)
  | (name,r,_,Some bo,t) :: ps -> DAst.make @@ Glob_term.GLetIn(name,r,bo,Some t, mk_gfun ty ps)
  | [] -> ty

let manual_implicit_of_binding_kind name = function
  | Glob_term.NonMaxImplicit -> CAst.make (Some (name,false))
  | Glob_term.MaxImplicit -> CAst.make (Some (name,true))
  | Glob_term.Explicit -> CAst.make None

let binding_kind_of_manual_implicit x =
  match x.CAst.v with
  | Some (_,false) -> Glob_term.NonMaxImplicit
  | Some (_,true) -> Glob_term.MaxImplicit
  | None -> Glob_term.Explicit

let manual_implicit_of_gdecl (name,_,bk,_,_) = manual_implicit_of_binding_kind name bk

let lookup_inductive env i =
  let mind, indbo = Inductive.lookup_mind_specif env i in
  if Array.length mind.Declarations.mind_packets <> 1 then
    nYI "API(env) mutual inductive";
  mind, indbo


let locate_qualid qualid =
  try
    match Nametab.locate_extended qualid with
    | Globnames.TrueGlobal gr -> Some (`Gref gr)
    | Globnames.Abbrev sd ->
       match Abbreviation.search_abbreviation sd with
       | _, Notation_term.NRef(gr,_) -> Some (`Gref gr)
       | _ -> Some (`Abbrev sd)
  with Not_found -> None

let locate_simple_qualid qualid =
  match locate_qualid qualid with
  | Some (`Gref x) -> x 
  | Some (`Abbrev _) ->
      nYI ("complex call to Locate: " ^ (Libnames.string_of_qualid qualid))
  | None ->
      err Pp.(str "Global reference not found: " ++ Libnames.pr_qualid qualid)

let locate_gref s =
  let s = String.trim s in
  try
    let i = String.index s ':' in
    let id = String.sub s (i+1) (String.length s - (i+1)) in
    let ref = Coqlib.lib_ref id in
    let path = Nametab.path_of_global ref in
    let qualid = Libnames.qualid_of_path path in
    locate_simple_qualid qualid
  with Not_found -> (* String.index *)
    let qualid = Libnames.qualid_of_string s in
    locate_simple_qualid qualid

let uint63 : Uint63.t Elpi.API.Conversion.t =
  let open Elpi.API.OpaqueData in
  declare {
    name = "uint63";
    doc = "";
    pp = (fun fmt i -> Format.fprintf fmt "%s" (Uint63.to_string i));
    compare = Uint63.compare;
    hash = Uint63.hash;
    hconsed = false;
    constants = [];
  }

let float64 : Float64.t Elpi.API.Conversion.t =
  let open Elpi.API.OpaqueData in
  declare {
    name = "float64";
    doc = "";
    pp = (fun fmt i -> Format.fprintf fmt "%s" (Float64.to_string i));
    compare = Float64.total_compare;
    hash = Float64.hash;
    hconsed = false;
    constants = [];
  }

let debug = CDebug.create ~name:"elpi" ()

  let projection : Names.Projection.t Elpi.API.Conversion.t =
    let open Elpi.API.OpaqueData in
    declare {
      name = "projection";
      doc = "";
      pp = (fun fmt i -> Format.fprintf fmt "%s" (Names.Projection.to_string i));
      compare = Names.Projection.CanOrd.compare;
      hash = Names.Projection.CanOrd.hash;
      hconsed = false;
      constants = [];
    }
  
let fold_elpi_term f acc ~depth t =
  let module E = Elpi.API.RawData in
  match t with
  | E.Const _ | E.Nil | E.CData _ -> acc
  | E.App(_,x,xs) -> List.fold_left (f ~depth) (f ~depth acc x) xs
  | E.Cons(x,xs) -> f ~depth (f ~depth acc x) xs
  | E.Builtin(_,xs) -> List.fold_left (f ~depth) acc xs
  | E.Lam x -> f ~depth:(depth+1) acc x
  | E.UnifVar(_,xs) -> List.fold_left (f ~depth) acc xs


type clause_scope = Local | Regular | Global | SuperGlobal
let pp_scope fmt = function
  | Local -> Format.fprintf fmt "local"
  | Regular -> Format.fprintf fmt "regular"
  | Global -> Format.fprintf fmt "global"
  | SuperGlobal -> Format.fprintf fmt "superglobal"

let rec list_map_acc f acc = function
  | [] -> acc, []
  | x :: xs ->
      let acc, x = f acc x in
      let acc, xs = list_map_acc f acc xs in
      acc, x :: xs

let rec fix_detype x = match DAst.get x with
  | Glob_term.GEvar _ -> mkGHole
  | _ -> Glob_ops.map_glob_constr fix_detype x
let detype ?(keepunivs=false) env sigma t =
  (* To avoid turning named universes into unnamed ones *)
  let options =
    if keepunivs then Flags.with_option Constrextern.print_universes
    else Flags.without_option Constrextern.print_universes in
  let gbody =
    options (Detyping.detype Detyping.Now Names.Id.Set.empty env sigma) t in
  fix_detype gbody

let detype_closed_glob env sigma closure =
  let gbody = Detyping.detype_closed_glob Names.Id.Set.empty env sigma closure in
  fix_detype gbody

type qualified_name = string list
let compare_qualified_name = Stdlib.compare
let pr_qualified_name = Pp.prlist_with_sep (fun () -> Pp.str".") Pp.str
let show_qualified_name = String.concat "."
let pp_qualified_name fmt l = Format.fprintf fmt "%s" (String.concat "." l)

let option_map_acc f s = function
  | None -> s, None
  | Some x ->
      let s, x = f s x in
      s, Some x

let option_map_acc2 f s = function
  | None -> s, None, []
  | Some x ->
      let s, x, gl = f s x in
      s, Some x, gl
    
let option_default f = function
  | Some x -> x
  | None -> f ()

let coq_version_parser version =
  let (!!) x = try int_of_string x with Failure _ -> -100 in
  match Str.split (Str.regexp_string ".") version with
  | major :: minor :: patch :: _ -> !!major, !!minor, !!patch
  | [ major ] -> !!major,0,0
  | [] -> 0,0,0
  | [ major; minor ] ->
      match Str.split (Str.regexp_string "+") minor with
      | [ minor ] -> !!major, !!minor, 0
      | [ ] -> !!major, !!minor, 0
      | minor :: prerelease :: _ ->
          if Str.string_match (Str.regexp_string "beta") prerelease 0 then
            !!major, !!minor, !!("-"^String.sub prerelease 4 (String.length prerelease - 4))
          else if Str.string_match (Str.regexp_string "alpha") prerelease 0 then
            !!major, !!minor, !!("-"^String.sub prerelease 5 (String.length prerelease - 5))
          else !!major, !!minor, -100


let mp2path x =
  let open Names in
  let rec mp2sl = function
    | MPfile dp -> CList.rev_map Id.to_string (DirPath.repr dp)
    | MPbound id ->
        let _,id,dp = MBId.repr id in
        mp2sl (MPfile dp) @ [ Id.to_string id ]
    | MPdot (mp,lbl) -> mp2sl mp @ [Label.to_string lbl] in
  mp2sl x

let gr2path gr =
  let open Names in
  match gr with
  | Names.GlobRef.VarRef v -> mp2path (Safe_typing.current_modpath (Global.safe_env ()))
  | Names.GlobRef.ConstRef c -> mp2path @@ Constant.modpath c
  | Names.GlobRef.IndRef (i,_) -> mp2path @@ MutInd.modpath i
  | Names.GlobRef.ConstructRef ((i,_),j) -> mp2path @@ MutInd.modpath i
