(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API

let synterp_quotations = API.Quotation.new_quotations_descriptor ()
let synterp_hoas = API.RawData.new_hoas_descriptor ()
let synterp_state = API.State.new_state_descriptor ()
let interp_quotations = API.Quotation.new_quotations_descriptor ()
let interp_hoas = API.RawData.new_hoas_descriptor ()
let interp_state = API.State.new_state_descriptor ()

let source_name_of_fname = function
  | Loc.InFile { file } -> Format.asprintf "%s" file 
  | Loc.ToplevelInput -> "(stdin)" 

let fname_of_source_name ~dirpath s =
  if s = "(stdin)" then Loc.ToplevelInput
  else Loc.InFile { dirpath; file = s }

let of_coq_loc l =
  let client_payload =
    match l.Loc.fname with
    | ToplevelInput -> None
    | InFile { dirpath } -> Option.map Obj.repr dirpath in
  {
    API.Ast.Loc.client_payload;
    source_name = source_name_of_fname l.Loc.fname;
    source_start = l.Loc.bp;
    source_stop = l.Loc.ep;
    line = l.Loc.line_nb;
    line_starts_at = l.Loc.bol_pos;
  }

let to_coq_loc { API.Ast.Loc.source_name; client_payload; line; line_starts_at; source_start; source_stop } =
  let dirpath = Option.map Obj.obj client_payload in
  Loc.create (fname_of_source_name ~dirpath source_name) line line_starts_at source_start source_stop

let err ?loc msg =
  let loc = Option.map to_coq_loc loc in
  CErrors.user_err ?loc msg

let pp_oloc = function
  | None -> Pp.mt ()
  | Some loc -> Pp.str @@ Format.asprintf "%a " API.Ast.Loc.pp loc

(* If the error comes from another file (see Loc.mergeable) Coq drops the precise loc
   and reports it on the whole execution site. If so, we print the
   more precise loc as part of the error message. 
   
   We also copy here Loc.merge since it may anyway discard the better loc,
   in that case we feedback it
   *)
let coq_would_drop_loc2 loc1 loc2 =
let open Loc in
if loc1.bp < loc2.bp then
  if loc1.ep < loc2.ep then false
  else true
else if loc2.ep < loc1.ep then false
else false

[%%if coq = "8.20"]
let feedback_error loc m = Feedback.(feedback (Message(Error,loc,m)))
[%%else]
let feedback_error loc m = Feedback.(feedback (Message(Error,loc,[],m)))
[%%endif]

let patch_loc_source execution_loc error_loc msg =
  match execution_loc, error_loc with
  | _, None -> msg, execution_loc
  | _, Some elpiloc when Loc.finer (Some execution_loc) (Some elpiloc) -> msg, elpiloc
  | { Loc.fname },Some ({ Loc.fname = elpiname } as elpiloc) when fname = elpiname ->
      (* same file, far location, we complementwith a feedback *)
      feedback_error (Some elpiloc) msg;
      Pp.(hv 0 (Loc.pr elpiloc ++ spc () ++ msg)), execution_loc    
  | _, Some elpiloc ->
      (* external file *)
      Pp.(hv 0 (Loc.pr elpiloc ++ spc () ++ msg)), execution_loc

let handle_elpi_compiler_errors ~loc ?error_header f =
  let w_header m =
    match error_header with
    | None -> m
    | Some x -> Pp.(v 0 (str x ++ str":" ++ spc() ++ m)) in
  try f ()
  with
  | Sys_error msg ->
    CErrors.user_err ~loc (w_header (Pp.str msg))
  | Elpi.API.Compile.CompileError(oloc, msg) as e ->
    let _,info = Exninfo.capture e in
    let msg, loc = patch_loc_source loc (Option.map to_coq_loc oloc) (Pp.str msg) in
    CErrors.user_err ~info ~loc (w_header msg)
  | Elpi.API.Parse.ParseError(oloc, msg) as e ->
    let _,info = Exninfo.capture e in
    let msg, loc = patch_loc_source loc (Some (to_coq_loc oloc)) (Pp.str msg) in
    CErrors.user_err ~info ~loc (w_header msg)
  | Gramlib.Grammar.Error _ as e ->
    let _,info = Exninfo.capture e in
    let cloc = Loc.get_loc info in
    let msg = CErrors.print_no_report e in
    let msg, loc = patch_loc_source loc cloc msg in
    CErrors.user_err ~info ~loc (w_header msg)


exception LtacFail of int * Pp.t

let ltac_fail_err ?loc n msg =
  let loc = Option.map to_coq_loc loc in
  Loc.raise ?loc (LtacFail (n, msg))

let feedback_fmt_write, feedback_fmt_flush =
  let b = Buffer.create 2014 in
  ( Buffer.add_substring b,
    fun () ->
      let s = Buffer.to_bytes b in
      let s =
        let len = Bytes.length s in
        if len > 0 && Bytes.get s (len - 1) = '\n' then Bytes.sub_string s 0 (len - 1) else Bytes.to_string s
      in
      Feedback.msg_debug Pp.(str s);
      Buffer.clear b )

let elpi_cat = CWarnings.create_category ~name:"elpi" ()

let elpi_depr_cat =
  CWarnings.create_category ~from:[ elpi_cat; CWarnings.CoreCategories.deprecated ] ~name:"elpi.deprecated" ()
let elpi_tc_cat =
  CWarnings.create_category ~from:[ elpi_cat ] ~name:"elpi.typecheck" ()
  
let () = API.Setup.set_error (fun ?loc s -> err ?loc Pp.(str s))
let () = API.Setup.set_anomaly (fun ?loc s -> err ?loc Pp.(str s))
let () = API.Setup.set_type_error (fun ?loc s -> err ?loc Pp.(str s))
let warn = CWarnings.create ~name:"elpi.runtime" ~category:elpi_cat (fun x -> x)
let warn_impl = CWarnings.create ~name:"elpi.implication-precedence" ~category:elpi_cat (fun x -> x)
let warn_linear = CWarnings.create ~name:"elpi.linear-variable" ~category:elpi_tc_cat (fun x -> x)
let warn_missing_types = CWarnings.create ~name:"elpi.missing-types" ~category:elpi_tc_cat (fun x -> x)
let warn_flex_clause = CWarnings.create ~name:"elpi.flex-clause" ~category:elpi_tc_cat (fun x -> x)

let () = API.Setup.set_warn (fun ?loc ~id x ->
  let loc = Option.map to_coq_loc loc in
  let msg = Pp.(hv 0 (Option.cata (fun loc -> Loc.pr loc ++ spc ()) (mt()) loc ++ str x)) in
  match id with
  | API.Setup.ImplicationPrecedence -> warn_impl ?loc msg
  | LinearVariable -> warn_linear ?loc msg
  | UndeclaredGlobal -> warn_missing_types ?loc msg
  | FlexClause -> warn_flex_clause ?loc msg)
let () = API.Setup.set_std_formatter (Format.make_formatter feedback_fmt_write feedback_fmt_flush)
let () = API.Setup.set_err_formatter (Format.make_formatter feedback_fmt_write feedback_fmt_flush)
let nYI s = err Pp.(str "Not Yet Implemented: " ++ str s)

let pp2string pp x =
  let b = Buffer.create 80 in
  let fmt = Format.formatter_of_buffer b in
  Format.pp_set_margin fmt (Option.default 80 (Topfmt.get_margin ()));
  Format.fprintf fmt "%a%!" pp x;
  Buffer.contents b

module C = Constr
module EC = EConstr

let safe_destApp sigma t = match EC.kind sigma t with C.App (hd, args) -> (EC.kind sigma hd, args) | x -> (x, [||])
let mkGHole = DAst.make Glob_term.(GHole GInternalHole)

let mkApp ~depth t l =
  match l with
  | [] -> t
  | x :: xs -> (
      match API.RawData.look ~depth t with API.RawData.Const c -> API.RawData.mkApp c x xs | _ -> assert false)

let string_split_on_char c s =
  let len = String.length s in
  let rec aux n x =
    if x = len then [ String.sub s n (x - n) ]
    else if s.[x] = c then String.sub s n (x - n) :: aux (x + 1) (x + 1)
    else aux n (x + 1)
  in
  aux 0 0

let rec mk_gforall ty = function
  | (name, r, bk, None, t) :: ps -> DAst.make @@ Glob_term.GProd (name, r, bk, t, mk_gforall ty ps)
  | (name, r, _, Some bo, t) :: ps -> DAst.make @@ Glob_term.GLetIn (name, r, bo, Some t, mk_gforall ty ps)
  | [] -> ty

let rec mk_gfun ty = function
  | (name, r, bk, None, t) :: ps -> DAst.make @@ Glob_term.GLambda (name, r, bk, t, mk_gfun ty ps)
  | (name, r, _, Some bo, t) :: ps -> DAst.make @@ Glob_term.GLetIn (name, r, bo, Some t, mk_gfun ty ps)
  | [] -> ty

let manual_implicit_of_binding_kind name = function
  | Glob_term.NonMaxImplicit -> CAst.make (Some (name, false))
  | Glob_term.MaxImplicit -> CAst.make (Some (name, true))
  | Glob_term.Explicit -> CAst.make None

let binding_kind_of_manual_implicit x =
  match x.CAst.v with
  | Some (_, false) -> Glob_term.NonMaxImplicit
  | Some (_, true) -> Glob_term.MaxImplicit
  | None -> Glob_term.Explicit

let manual_implicit_of_gdecl (name, _, bk, _, _) = manual_implicit_of_binding_kind name bk

let lookup_inductive env i =
  let mind, indbo = Inductive.lookup_mind_specif env i in
  if Array.length mind.Declarations.mind_packets <> 1 then nYI "API(env) mutual inductive";
  (mind, indbo)

let locate_qualid qualid =
  try
    match Nametab.locate_extended qualid with
    | Globnames.TrueGlobal gr -> Some (`Gref gr)
    | Globnames.Abbrev sd -> (
        match Abbreviation.search_abbreviation sd with
        | _, Notation_term.NRef (gr, _) -> Some (`Gref gr)
        | _ -> Some (`Abbrev sd))
  with Not_found -> None

let locate_simple_qualid qualid =
  match locate_qualid qualid with
  | Some (`Gref x) -> x
  | Some (`Abbrev _) -> nYI ("complex call to Locate: " ^ Libnames.string_of_qualid qualid)
  | None -> err Pp.(str "Global reference not found: " ++ Libnames.pr_qualid qualid)

let locate_gref s =
  let s = String.trim s in
  try
    let i = String.index s ':' in
    let id = String.sub s (i + 1) (String.length s - (i + 1)) in
    let ref = Coqlib.lib_ref id in
    let path = Nametab.path_of_global ref in
    let qualid = Libnames.qualid_of_path path in
    locate_simple_qualid qualid
  with Not_found ->
    (* String.index *)
    let qualid = Libnames.qualid_of_string s in
    locate_simple_qualid qualid

let (uint63c, uint63) : Uint63.t Elpi.API.RawOpaqueData.cdata * Uint63.t Elpi.API.Conversion.t =
  let open Elpi.API.RawOpaqueData in
  declare
    {
      name = "uint63";
      doc = "";
      pp = (fun fmt i -> Format.fprintf fmt "%s" (Uint63.to_string i));
      compare = Uint63.compare;
      hash = Uint63.hash;
      hconsed = false;
      constants = [];
    }

let (float64c, float64) : Float64.t Elpi.API.RawOpaqueData.cdata * Float64.t Elpi.API.Conversion.t =
  let open Elpi.API.RawOpaqueData in
  declare
    {
      name = "float64";
      doc = "";
      pp = (fun fmt i -> Format.fprintf fmt "%s" (Float64.to_string i));
      compare = Float64.total_compare;
      hash = Float64.hash;
      hconsed = false;
      constants = [];
    }

let (pstringc, pstring) : Pstring.t Elpi.API.RawOpaqueData.cdata * Pstring.t Elpi.API.Conversion.t =
  let open Elpi.API.RawOpaqueData in
  declare {
    name = "pstring";
    doc = "";
    pp = (fun fmt s -> Format.fprintf fmt "%S" (Pstring.to_string s));
    compare = Pstring.compare;
    hash = Pstring.hash;
    hconsed = false;
    constants = [];
  }
let pstring_of_string = Pstring.of_string
let string_of_pstring = Pstring.to_string

let debug = CDebug.create ~name:"elpi" ()

let elpitime_flag, elpitime = CDebug.create_full ~name:"elpitime" ()

let (projectionc, projection) : Names.Projection.t Elpi.API.RawOpaqueData.cdata * Names.Projection.t Elpi.API.Conversion.t =
  let open Elpi.API.RawOpaqueData in
  declare
    {
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
  | E.App (_, x, xs) -> List.fold_left (f ~depth) (f ~depth acc x) xs
  | E.Cons (x, xs) -> f ~depth (f ~depth acc x) xs
  | E.Builtin (_, xs) -> List.fold_left (f ~depth) acc xs
  | E.Lam x -> f ~depth:(depth + 1) acc x
  | E.UnifVar (_, xs) -> List.fold_left (f ~depth) acc xs

type clause_scope = Local | Regular | Global | SuperGlobal

let pp_scope fmt = function
  | Local -> Format.fprintf fmt "local"
  | Regular -> Format.fprintf fmt "regular"
  | Global -> Format.fprintf fmt "global"
  | SuperGlobal -> Format.fprintf fmt "superglobal"

let rec list_map_acc f acc = function
  | [] -> (acc, [])
  | x :: xs ->
      let acc, x = f acc x in
      let acc, xs = list_map_acc f acc xs in
      (acc, x :: xs)

let rec fix_detype x = match DAst.get x with Glob_term.GEvar _ -> mkGHole | _ -> Glob_ops.map_glob_constr fix_detype x

let detype_qvar sigma q =
  let open Glob_term in
  match UState.id_of_qvar (Evd.evar_universe_context sigma) q with
  | Some id -> GLocalQVar (CAst.make (Names.Name.Name id))
  | None -> GQVar q

let detype_quality sigma q =
  let open Glob_term in
  let open Sorts.Quality in
  match q with QConstant q -> GQConstant q | QVar q -> GQualVar (detype_qvar sigma q)

let detype_level_name sigma l =
  let open Glob_term in
  if Univ.Level.is_set l then GSet
  else
    match UState.id_of_level (Evd.evar_universe_context sigma) l with
    | Some id -> GLocalUniv (CAst.make id)
    | None -> GUniv l

let detype_level sigma l =
  let open Glob_term in
  UNamed (detype_level_name sigma l)

let detype_universe sigma u =
  Glob_term.UNamed (List.map (Util.on_fst (detype_level_name sigma)) (Univ.Universe.repr u))
let detype_sort ku sigma x =
  let open Sorts in
  let open Glob_ops in
  match x with
  | SProp -> glob_SProp_sort
  | Prop -> glob_Prop_sort
  | Set -> glob_Set_sort
  | Type u when ku -> None, detype_universe sigma u
  | QSort (q, u) when ku -> Some (detype_qvar sigma q), detype_universe sigma u
  | _ -> glob_Type_sort

(*
let detype_relevance_info sigma na =
  match Evarutil.nf_relevance sigma na with
  | Relevant -> Some Glob_term.GRelevant
  | Irrelevant -> Some Glob_term.GIrrelevant
  | RelevanceVar q -> Some (Glob_term.GRelevanceVar (detype_qvar sigma q))
*)

let detype_instance ku sigma l =
  if not ku then None
  else
    let open EConstr in
    let l = EInstance.kind sigma l in
    if UVars.Instance.is_empty l then None
    else
      let qs, us = UVars.Instance.to_array l in
      let qs = List.map (detype_quality sigma) (Array.to_list qs) in
      let us = List.map (detype_level sigma) (Array.to_list us) in
      Some (qs, us)

let it_destRLambda_or_LetIn_names l c =
  let open Glob_term in
  let rec aux l nal c =
    match (DAst.get c, l) with
    | _, [] -> (List.rev nal, c)
    | GLambda (na, _,  _, _, c), false :: l -> aux l (na :: nal) c
    | GLetIn (na, _, _, _, c), true :: l -> aux l (na :: nal) c
    | _ -> nYI "detype eta"
  in
  aux l [] c
let rec decompose accu c = match DAst.get c with
| Glob_term.GLambda (na, _, _, _, c) -> decompose (na :: accu) c
| _ -> List.rev accu, c


module RobustExpand :
sig
open Names
open EConstr
val return_clause : Environ.env -> Evd.evar_map -> Ind.t ->
  EInstance.t -> EConstr.t array -> EConstr.case_return -> rel_context * EConstr.t
val branch : Environ.env -> Evd.evar_map -> Construct.t ->
  EInstance.t -> EConstr.t array -> EConstr.case_branch -> rel_context * EConstr.t
end =
struct
open Vars
open Names
open Declarations
open UVars
open Constr
open Context.Rel.Declaration

let instantiate_context u subst nas ctx =
  let rec instantiate i ctx = match ctx with
  | [] -> []
  | LocalAssum (_, ty) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let ty = substnl subst i (subst_instance_constr u ty) in
    LocalAssum (nas.(i), ty) :: ctx
  | LocalDef (_, ty, bdy) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let ty = substnl subst i (subst_instance_constr u ty) in
    let bdy = substnl subst i (subst_instance_constr u bdy) in
    LocalDef (nas.(i), ty, bdy) :: ctx
  in
  let () = if not (Int.equal (Array.length nas) (List.length ctx)) then raise_notrace Exit in
  instantiate (Array.length nas - 1) ctx

let return_clause env sigma ind u params ((nas, p),_) =
  let nas : Name.t EConstr.binder_annot array = nas in
  try
    let u = EConstr.Unsafe.to_instance u in
    let params = EConstr.Unsafe.to_constr_array params in
    let nas : Name.t Constr.binder_annot array =
      match EConstr.Unsafe.relevance_eq with Refl -> nas
    in
    let () = if not @@ Environ.mem_mind (fst ind) env then raise_notrace Exit in
    let mib = Environ.lookup_mind (fst ind) env in
    let mip = mib.mind_packets.(snd ind) in
    let paramdecl = subst_instance_context u mib.mind_params_ctxt in
    let paramsubst = subst_of_rel_context_instance paramdecl params in
    let realdecls, _ = CList.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
    let self =
      let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
      let inst = Instance.(abstract_instance (length u)) in
      mkApp (mkIndU (ind, inst), args)
    in
    let realdecls = LocalAssum (Context.anonR, self) :: realdecls in
    let realdecls = instantiate_context u paramsubst nas realdecls in
    List.map EConstr.of_rel_decl realdecls, p
  with e when CErrors.noncritical e ->
    let dummy na = LocalAssum (na, EConstr.mkProp) in
    List.rev (CArray.map_to_list dummy nas), p

let branch env sigma (ind, i) u params (nas, br) =
  let nas : Name.t EConstr.binder_annot array = nas in
  try
    let u = EConstr.Unsafe.to_instance u in
    let params = EConstr.Unsafe.to_constr_array params in
    let nas : Name.t Constr.binder_annot array =
      match EConstr.Unsafe.relevance_eq with Refl -> nas
    in
    let () = if not @@ Environ.mem_mind (fst ind) env then raise_notrace Exit in
    let mib = Environ.lookup_mind (fst ind) env in
    let mip = mib.mind_packets.(snd ind) in
    let paramdecl = subst_instance_context u mib.mind_params_ctxt in
    let paramsubst = subst_of_rel_context_instance paramdecl params in
    let (ctx, _) = mip.mind_nf_lc.(i - 1) in
    let ctx, _ = CList.chop mip.mind_consnrealdecls.(i - 1) ctx in
    let ctx = instantiate_context u paramsubst nas ctx in
    List.map EConstr.of_rel_decl ctx, br
  with e when CErrors.noncritical e ->
    let dummy na = LocalAssum (na, EConstr.mkProp) in
    List.rev (CArray.map_to_list dummy nas), br

end

let detype_relevance_info sigma na =
  match EConstr.ERelevance.kind sigma na with
    | Relevant -> Some Glob_term.GRelevant
    | Irrelevant -> Some Glob_term.GIrrelevant
    | RelevanceVar q -> Some (GRelevanceVar (detype_qvar sigma q))
let mk_glob_decl_g sigma na x y z = Context.binder_name na, detype_relevance_info sigma @@ Context.binder_relevance na, x, y, z
let mkGProd sigma na x y z = Glob_term.GProd(Context.binder_name na, detype_relevance_info sigma @@ Context.binder_relevance na, x, y, z)
let mkGLambda sigma na x y z = Glob_term.GLambda(Context.binder_name na, detype_relevance_info sigma @@ Context.binder_relevance na, x, y, z)
let mkGLetIn sigma na x y z = Glob_term.GLetIn(Context.binder_name na, detype_relevance_info sigma @@ Context.binder_relevance na, x, y, z)
let get_ind_tags env ci p =
  let ind = ci.Constr.ci_ind in
  if Environ.mem_mind (fst ind) env then
    let (mib, mip) = Inductive.lookup_mind_specif env ind in
    Context.Rel.to_tags (CList.firstn mip.mind_nrealdecls mip.mind_arity_ctxt)
  else
    let (nas, _), _ = p in
    CArray.map_to_list (fun _ -> false) nas

let get_cstr_tags env ci bl =
  let ind = ci.Constr.ci_ind in
  if Environ.mem_mind (fst ind) env then
    let (mib, mip) = Inductive.lookup_mind_specif env ind in
    Array.map2 (fun (d, _) n -> Context.Rel.to_tags (CList.firstn n d))
      mip.mind_nf_lc mip.mind_consnrealdecls
  else
    let map (nas, _) = CArray.map_to_list (fun _ -> false) nas in
    Array.map map bl

let get_GLambda_name_tgt typ =
  match DAst.get typ with
  | Glob_term.GLambda (x, _, _, t, c) -> (x, c)
  | _ -> (Anonymous, typ)

let detype_primitive_string = function
  | Constr.String s -> DAst.make @@ Glob_term.GString s
  | _ -> assert false

[%%if coq = "8.19" || coq = "8.20" ]
let fresh (names, e) sigma name ty =
  let open EConstr in
  let open Names.Name in
  let mk_fresh was =
    let id = Namegen.next_name_away was names in
    (Name id, (Names.Id.Set.add id names, e))
  in
  match name with
  | Anonymous ->
      let noccurs sigma i = function None -> true | Some t -> Vars.noccurn sigma i t in
      let name, names = Namegen.compute_displayed_name_in_gen noccurs e sigma names name ty in
      (name, (names, e))
  | Name id when Names.Id.Set.mem id names -> mk_fresh name
  | Name id as x -> (x, (Names.Id.Set.add id names, e))

let names_of_env env =
  let namesr = Environ.rel_context env |> Context.Rel.to_vars in
  let namesv = Environ.named_context env |> Context.Named.to_vars in
  Names.Id.Set.union namesr namesv
[%%else]
let fresh (names, e) sigma name ty =
  let open EConstr in
  let open Names.Name in
  let mk_fresh was =
    let id, names = Namegen.Generator.next_name_away Namegen.Generator.fresh was names in
    (Name id, (names, e))
  in
  match name with
  | Anonymous ->
      let noccurs sigma i = function None -> true | Some t -> Vars.noccurn sigma i t in
      let name, names = Namegen.compute_displayed_name_in_gen Namegen.Generator.fresh noccurs e sigma names name ty in
      (name, (names, e))
  | Name id when Nameops.Fresh.mem id names -> mk_fresh name
  | Name id as x -> (x, (Nameops.Fresh.add id names, e))

let names_of_env env =
  let namesr = Environ.rel_context env |> Context.Rel.to_vars in
  let namesv = Environ.named_context env |> Context.Named.to_vars in
  Names.Id.Set.fold (fun id accu -> Nameops.Fresh.add id accu) namesr (Nameops.Fresh.of_set namesv)
[%%endif]

let detype ?(keepunivs = false) env sigma t =
  let open Glob_term in
  let open EConstr in
  let open Context.Rel.Declaration in
  debug Pp.(fun () -> str "detype: " ++ Printer.pr_econstr_env env sigma t);

  let fresh (names, e) name ty = fresh (names, e) sigma name ty in
  let push_rel d env c =
    let name = Context.Rel.Declaration.get_name d in
    let r = Context.Rel.Declaration.get_relevance d in
    let name, (names, env) = fresh env name (Some c) in
    let namer = Context.make_annot name r in
    ((names, EConstr.push_rel (Context.Rel.Declaration.set_name name d) env), namer)
  in
  let push_occurring_rel d env =
    let name = Context.Rel.Declaration.get_name d in
    let r = Context.Rel.Declaration.get_relevance d in
    let name, (names, env) = fresh env name None in
    let namer = Context.make_annot name r in
    ((names, EConstr.push_rel (Context.Rel.Declaration.set_name name d) env), namer)
  in

  let lookup_rel i (_, env) = Environ.lookup_rel i env in

  let unknown_inductive = Coqlib.lib_ref "elpi.unknown_inductive" in

  let rec detype_binder env name bo ty t =
    let gty = aux env ty in
    let gbo = Option.map (aux env) bo in
    (*let rinfo = detype_relevance_info sigma binder_relevance in*)
    let env, name = push_rel (LocalAssum (name, ty)) env t in
    let gt = aux env t in
    (name, gbo, gty, gt)
  and aux env t =
    match kind sigma t with
    | Rel i -> (
        match lookup_rel i env |> get_name with
        | Names.Name.Anonymous -> assert false
        | Names.Name.Name x -> DAst.make @@ GVar x
        | exception Not_found -> assert false)
    | Var x ->
        (* Discriminate between section variable and non-section variable *)
        DAst.make
          (try
             let _ = Environ.lookup_named x (snd env) in
             GRef (Names.GlobRef.VarRef x, None)
           with Not_found -> GVar x)
    | Meta _ -> assert false
    | Evar _ -> mkGHole
    | Sort s -> DAst.make @@ GSort (detype_sort keepunivs sigma (ESorts.kind sigma s))
    | Cast (t, k, ty) -> DAst.make @@ GCast (aux env t, Some k, aux env ty)
    | Prod (name, ty, t) ->
        let name, _, gty, gt = detype_binder env name None ty t in
        DAst.make @@ mkGProd sigma name Explicit gty gt
    | Lambda (name, ty, t) ->
        let name, _, gty, gt = detype_binder env name None ty t in
        DAst.make @@ mkGLambda sigma name Explicit gty gt
    | LetIn (name, bo, ty, t) ->
        let name, gbo, gty, gt = detype_binder env name (Some bo) ty t in
        DAst.make @@ mkGLetIn sigma name Option.(get gbo) (Some gty) gt
    | App (hd, args) -> DAst.make @@ GApp (aux env hd, CArray.map_to_list (aux env) args)
    | Int i -> DAst.make @@ GInt i
    | Float i -> DAst.make @@ GFloat i
    | Array (u, a, d, ty) ->
        DAst.make @@ GArray (detype_instance keepunivs sigma u, CArray.map (aux env) a, aux env d, aux env ty)
    | Const (c, u) -> DAst.make @@ GRef (Names.GlobRef.ConstRef c, detype_instance keepunivs sigma u)
    | Ind (c, u) -> DAst.make @@ GRef (Names.GlobRef.IndRef c, detype_instance keepunivs sigma u)
    | Construct (c, u) -> DAst.make @@ GRef (Names.GlobRef.ConstructRef c, detype_instance keepunivs sigma u)
    | Proj (p, r, c) ->
        if Names.Projection.unfolded p then
          let open Names in
          let c = aux env c in
          let id = Label.to_id @@ Projection.label p in
          let nargs, parg =
            try
              let _, mip = Global.lookup_inductive (Projection.inductive p) in
              (mip.mind_consnrealargs.(0), Projection.arg p)
            with e when !Flags.in_debugger ->
              (* kinda weird printing but the name should be enough to
                 indicate which projection it is *)
              (1, 0)
          in
          let pathole = DAst.make @@ PatVar Anonymous in
          let patargs =
            List.init nargs (fun i -> if Int.equal i parg then DAst.make @@ PatVar (Name id) else pathole)
          in
          let pat = DAst.make @@ PatCstr ((Projection.inductive p, 1), patargs, Anonymous) in
          let br = ([ id ], [ pat ], DAst.make @@ GVar id) in
          (* MatchStyle looks relatively heavy *)
          DAst.make @@ GCases (LetPatternStyle, None, [ (c, (Anonymous, None)) ], [ CAst.make br ])
        else
          let pars = Names.Projection.npars p in
          let hole = DAst.make @@ GHole GInternalHole in
          let args = CList.make pars hole in
          DAst.make
          @@ GApp (DAst.make @@ GRef (Names.GlobRef.ConstRef (Names.Projection.constant p), None), args @ [ aux env c ])
    | Fix (((vn, _) as nvn), (names, tys, bodies)) ->
        let env, names =
          list_map_acc
            (fun env (n, ty) -> push_occurring_rel (LocalAssum (n, ty)) env)
            env
            (CList.combine (names|> CArray.to_list) (tys |> CArray.to_list))
        in
        let n = Array.length tys in
        let v = CArray.map3 (fun c t i -> share_names (i + 1) [] env c (Vars.lift n t)) bodies tys vn in
        DAst.make
        @@ GRec
             ( GFix (Array.map (fun i -> Some i) (fst nvn), snd nvn),
               CArray.map_of_list (function Names.Name.Name x -> x | _ -> assert false) (List.map Context.binder_name names),
               Array.map (fun (bl, _, _) -> bl) v,
               Array.map (fun (_, _, ty) -> ty) v,
               Array.map (fun (_, bd, _) -> bd) v )
    | CoFix _ -> nYI "cofix"
    | Case (ci, u, pms, p, iv, c, [| bl |]) when unknown_inductive = Names.GlobRef.IndRef ci.ci_ind ->
        let tomatch = aux env c in
        let map i br =
          let ctx, body = RobustExpand.branch (snd env) sigma (ci.ci_ind, i + 1) u pms br in
          EConstr.it_mkLambda_or_LetIn body ctx
        in
        let bl = map 0 bl in
        let bl' = aux env bl in
        let (nal, d) = decompose [] bl' in
  
        DAst.make @@ GLetTuple (nal, ((*Anonymous,None*) Name (Names.Id.of_string "xxx"), Some mkGHole), tomatch, d)
    | Case (ci, u, pms, p, iv, c, bl) -> detype_case env (ci, u, pms, p, iv, c, bl)
    | s -> detype_primitive_string s
 and share_names n l env bo ty =
    if n = 0 then (List.rev l, aux env bo, aux env ty)
    else
      match (EConstr.kind sigma bo, EConstr.kind sigma ty) with
      | LetIn (_, b, _, x), _ -> share_names n l env (Vars.subst1 b x) ty
      | _, LetIn (_, b, _, x) -> share_names n l env bo (Vars.subst1 b x)
      | Lambda (na, lty, bo), Prod (na', _, ty) ->
          let na = Nameops.Name.pick_annot na na' in
          let decl = LocalAssum (na, lty) in
          let lty = aux env lty in
          let env, na = push_rel decl env bo in
          share_names (n - 1) (mk_glob_decl_g sigma na Explicit None lty :: l) env bo ty
      | _, Prod (na, lty, ty) ->
          let decl = LocalAssum (na, lty) in
          let lty = aux env lty in
          let env, na = push_occurring_rel decl env in
          let bo = mkApp (Vars.lift 1 bo, [| mkRel 1 |]) in
          share_names (n - 1) (mk_glob_decl_g sigma na Explicit None lty :: l) env bo ty
      | _ -> assert false
  and detype_case env (ci, univs, params, p, iv, c, bl) =
    let open Constr in
    let tomatch = aux env c in
    let tomatch =
      let _, mip = Global.lookup_inductive ci.ci_ind in
      let hole = DAst.make @@ GHole GInternalHole in
      let indices = CList.make mip.mind_nrealargs hole in
      let t = EConstr.mkApp (EConstr.mkIndU (ci.ci_ind, univs), params) in
      DAst.make @@ GCast (tomatch, None, Glob_ops.mkGApp (aux env t) indices)
    in

    let alias, aliastyp, pred =
      let tags = get_ind_tags (snd env) ci p in
      let ctx, p = RobustExpand.return_clause (snd env) sigma ci.ci_ind univs params p in
      let p = EConstr.it_mkLambda_or_LetIn p ctx in
      let p = aux env p in
      let nl, typ = it_destRLambda_or_LetIn_names tags p in
      let n, typ = get_GLambda_name_tgt typ in
      let aliastyp = if List.for_all (Names.Name.equal Anonymous) nl then None else Some (CAst.make (ci.ci_ind, nl)) in
      (n, aliastyp, Some typ)
    in
    let constructs = Array.init (Array.length bl) (fun i -> (ci.ci_ind, i + 1)) in
      let constagsl = get_cstr_tags (snd env) ci bl in
      let eqnl = detype_eqns env constructs constagsl (ci, univs, params, bl) in
      DAst.make @@ GCases (RegularStyle, pred, [ (tomatch, (alias, aliastyp)) ], eqnl)
  and detype_eqns env constructs consnargsl bl =
    let ci, u, pms, bl = bl in
    CArray.to_list (CArray.map3 (detype_eqn env u pms) constructs consnargsl bl)
  and detype_eqn env u pms constr construct_nargs br =
    let ctx, body = RobustExpand.branch (snd env) sigma constr u pms br in
    let branch = EConstr.it_mkLambda_or_LetIn body ctx in
    let make_pat decl env b ids =
      let env, na = push_rel decl env b in
      let ids = match Context.binder_name na with Names.Name.Name x -> Names.Id.Set.add x ids | _ -> ids in
      (DAst.make (PatVar (Context.binder_name na)), env, ids)
    in
    let rec buildrec ids patlist env n b =
      if Int.equal n 0 then
        CAst.make
        @@ (Names.Id.Set.elements ids, [ DAst.make @@ PatCstr (constr, List.rev patlist, Anonymous) ], aux env b)
      else
        match EConstr.kind sigma b with
        | Lambda (x, t, b) ->
            let pat, env, new_ids = make_pat (LocalAssum (x, t)) env b ids in
            buildrec new_ids (pat :: patlist) env (pred n) b
        | LetIn (x, b, t, b') ->
            let pat, env, new_ids = make_pat (LocalDef (x, b, t)) env b' ids in
            buildrec new_ids (pat :: patlist) env (pred n) b'
        | _ -> assert false
    in
    buildrec Names.Id.Set.empty [] env (List.length ctx) branch
  in

  let x = aux (names_of_env env, env) t in
  x

[%%if coq = "8.19" || coq = "8.20" ]
let detype_closed_glob env sigma closure =
  let gbody = Detyping.detype_closed_glob Names.Id.Set.empty env sigma closure in
  fix_detype gbody
[%%else]
let detype_closed_glob env sigma closure =
  let gbody = Detyping.detype_closed_glob env sigma closure in
  fix_detype gbody
[%%endif]

type qualified_name = string list

let compare_qualified_name = Stdlib.compare
let pr_qualified_name = Pp.prlist_with_sep (fun () -> Pp.str ".") Pp.str
let show_qualified_name = String.concat "."
let pp_qualified_name fmt l = Format.fprintf fmt "%s" (String.concat "." l)

let option_map_acc f s = function
  | None -> (s, None)
  | Some x ->
      let s, x = f s x in
      (s, Some x)

let option_map_acc2 f s = function
  | None -> (s, None, [])
  | Some x ->
      let s, x, gl = f s x in
      (s, Some x, gl)

let option_default f = function Some x -> x | None -> f ()

let coq_version_parser version =
  Elpi.API.Utils.version_parser ~what:"coq" version

let mp2path x =
  let open Names in
  let rec mp2sl = function
    | MPfile dp -> CList.rev_map Id.to_string (DirPath.repr dp)
    | MPbound id ->
        let _, id, dp = MBId.repr id in
        mp2sl (MPfile dp) @ [ Id.to_string id ]
    | MPdot (mp, lbl) -> mp2sl mp @ [ Label.to_string lbl ]
  in
  mp2sl x

let gr2path gr =
  let open Names in
  match gr with
  | Names.GlobRef.VarRef v -> mp2path (Lib.current_mp ())
  | Names.GlobRef.ConstRef c -> mp2path @@ Constant.modpath c
  | Names.GlobRef.IndRef (i, _) -> mp2path @@ MutInd.modpath i
  | Names.GlobRef.ConstructRef ((i, _), j) -> mp2path @@ MutInd.modpath i

let eta_contract env sigma t =
  let unzip l t = EConstr.it_mkLambda t l in
  let not_occurs n t =
    let fr = Termops.free_rels sigma t in
    let rec aux i =
      if n < i then true
      else not (Int.Set.mem i fr) && aux (i+1) in
    aux 1 in
  (*let not_occurs n t =
    let rc = not_occurs n t in
    Printf.eprintf "not_occurs %d %s %b\n" n Pp.(string_of_ppcmds @@ Printer.pr_econstr_env env sigma t) rc;
    rc in*)
  let eta_condition vl nargs i t =
    if i < nargs - vl then not_occurs vl t
    else EConstr.eq_constr_nounivs sigma t (EConstr.mkRel (vl - (i - (nargs - vl)))) in
  let rec contract env vl t =
    match EConstr.kind sigma t with
    | App(hdo,argso) ->
        let hd = map env hdo in
        let args = CArray.Smart.map (map env) argso in
        let nargs = Array.length args in
        if nargs >= vl &&
            not_occurs vl hd &&
            CArray.for_all_i (eta_condition vl nargs) 0 args
        then
          let args = Array.sub args 0 (nargs - vl) in
          (* apperantly negative lift is a thing *)
          EConstr.Vars.lift (-vl) (EConstr.mkApp(hd,args)), true
        else
          if hd == hdo && args == argso then t, false
          else EConstr.mkApp(hd,args), false
    | _ -> map env t, false
  and cross env (o,vl,zip) t =
    match EConstr.kind sigma t with
    | Lambda(name,ty,bo) -> cross env (o,vl+1,(name,ty)::zip) bo
    | _ ->
        let t', b = contract env vl t in
        if b then t'
        else if t == t' then o
        else unzip zip t'
  and map env t =
    match EConstr.kind sigma t with
    | Lambda _ -> cross env (t,0,[]) t
    | _ -> Termops.map_constr_with_full_binders env sigma EConstr.push_rel map env t
  in
    (*Printf.eprintf "------------- %s\n" Pp.(string_of_ppcmds @@ Printer.pr_econstr_env env sigma t);*)
    map env t
