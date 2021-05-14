(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API

let of_coq_loc l = {
  API.Ast.Loc.source_name =
    (match l.Loc.fname with Loc.InFile x -> x | Loc.ToplevelInput -> "(stdin)");
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
} = Loc.create (Loc.InFile source_name) line line_starts_at source_start source_stop

let err ?loc msg =
  let loc = Option.map to_coq_loc loc in
  CErrors.user_err ~hdr:"elpi" ?loc msg

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

let () = API.Setup.set_error (fun ?loc s -> err ?loc Pp.(str s))
let () = API.Setup.set_anomaly (fun ?loc s -> err ?loc Pp.(str s))
let () = API.Setup.set_type_error (fun ?loc s -> err ?loc Pp.(str s))
let warn = CWarnings.create ~name:"runtime" ~category:"elpi" Pp.str
let () = API.Setup.set_warn (fun ?loc x -> warn ?loc:(Option.map to_coq_loc loc) x)
let () = API.Setup.set_std_formatter (Format.make_formatter feedback_fmt_write feedback_fmt_flush)
let () = API.Setup.set_err_formatter (Format.make_formatter feedback_fmt_write feedback_fmt_flush)


let nYI s = err Pp.(str"Not Yet Implemented: " ++ str s)

let pp2string pp x =
  let b = Buffer.create 80 in
  let fmt = Format.formatter_of_buffer b in
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
    (Glob_term.GHole(Evar_kinds.InternalHole,Namegen.IntroAnonymous,None))
    
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
  | (name,bk,None,t) :: ps -> DAst.make @@ Glob_term.GProd(name,bk,t, mk_gforall ty ps)
  | (name,_,Some bo,t) :: ps -> DAst.make @@ Glob_term.GLetIn(name,bo,Some t, mk_gforall ty ps)
  | [] -> ty

let rec mk_gfun ty = function
  | (name,bk,None,t) :: ps -> DAst.make @@ Glob_term.GLambda(name,bk,t, mk_gfun ty ps)
  | (name,_,Some bo,t) :: ps -> DAst.make @@ Glob_term.GLetIn(name,bo,Some t, mk_gfun ty ps)
  | [] -> ty

let manual_implicit_of_binding_kind name = function
  | Glob_term.NonMaxImplicit -> CAst.make (Some (name,false))
  | Glob_term.MaxImplicit -> CAst.make (Some (name,true))
  | Glob_term.Explicit -> CAst.make None

let manual_implicit_of_gdecl (name,bk,_,_) = manual_implicit_of_binding_kind name bk

let lookup_inductive env i =
  let mind, indbo = Inductive.lookup_mind_specif env i in
  if Array.length mind.Declarations.mind_packets <> 1 then
    nYI "API(env) mutual inductive";
  if Declareops.inductive_is_polymorphic mind then
    nYI "API(env) poly mutual inductive";
  mind, indbo


let locate_qualid qualid =
  try
    match Nametab.locate_extended qualid with
    | Globnames.TrueGlobal gr -> Some (`Gref gr)
    | Globnames.SynDef sd ->
       match Syntax_def.search_syntactic_definition sd with
       | _, Notation_term.NRef gr -> Some (`Gref gr)
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
