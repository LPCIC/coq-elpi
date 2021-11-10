(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module E  = API.RawData
module CD = API.RawOpaqueData
module U  = API.Utils
module P  = API.RawPp
module S  = API.State
module F = API.FlexibleData

module C = Constr
module EC = EConstr
open Names
module G = GlobRef
open Coq_elpi_utils

(* ************************************************************************ *)
(* ****************** HOAS of Coq terms and goals ************************* *)
(* See also coq-HOAS.elpi (terms)                                           *)
(* ************************************************************************ *)

(* {{{ CData ************************************************************** *)

(* names *)
let namein, isname, nameout, name =
  let { CD.cin; isc; cout }, name  = CD.declare {
    CD.name = "name";
    doc = "Name.Name.t: Name hints (in binders), can be input writing a name between backticks, e.g. `x` or `_` for anonymous. Important: these are just printing hints with no meaning, hence in elpi two name are always related: `x` = `y`";
    pp = (fun fmt x ->
      Format.fprintf fmt "`%a`" Pp.pp_with (Name.print x));
    compare = (fun _ _ -> 0);
    hash = (fun _ -> 0);
    hconsed = false;
    constants = [];
  } in
  cin, isc, cout, name
;;
let in_elpi_name x = namein x

let is_coq_name ~depth t =
  match E.look ~depth t with
  | E.CData n -> isname n || (CD.is_string n && Id.is_valid (CD.to_string n))
  | _ -> false

let in_coq_name ~depth t =
  match E.look ~depth t with
  | E.CData n when isname n -> nameout n
  | E.CData n when CD.is_string n ->
     let s = CD.to_string n in
     if s = "_" then Name.Anonymous
     else Name.Name (Id.of_string s)
  | E.UnifVar _ -> Name.Anonymous
  | _ -> err Pp.(str"Not a name: " ++ str (API.RawPp.Debug.show_term t))

(* All in one data structure to represent the Coq context and its link with
   the elpi one:
   - section is not part of the elpi context, but Coq's evars are applied
     also to that part
   - proof is the named_context with proof variables only (no section part)
   - local is the rel_context
   - db2rel stores how many locally bound (rel) variables were there when
     the binder for the given dbl is crossed: see lp2term
   - env is a Coq environment corresponding to section + proof + local *)
type empty = [ `Options ]
type full = [ `Options | `Context ]

(* Readback of UVars into ... *)
type ppoption = All | Most | Normal
type hole_mapping =
  | Verbatim   (* 1:1 correspondence between UVar and Evar *)
  | Heuristic  (* new UVar outside Llam is pruned before being linked to Evar *)
  | Implicit   (* No link, UVar is intepreted as a "hole" constant *)
type options = {
  hoas_holes : hole_mapping option;
  local : bool option;
  deprecation : Deprecation.t option;
  primitive : bool option;
  failsafe : bool; (* don't fail, e.g. we are trying to print a term *)
  ppwidth : int;
  pp : ppoption;
  pplevel : Constrexpr.entry_relative_level;
  using : string option;
}

let default_options = {
  hoas_holes = Some Verbatim;
  local = None;
  deprecation = None;
  primitive = None;
  failsafe = false;
  ppwidth = 80;
  pp = Normal;
  pplevel = Constrexpr.LevelSome;
  using = None;
}

type 'a coq_context = {
  section : Names.Id.t list;
  section_len : int;
  proof : EConstr.named_context;
  proof_len : int;
  local : (int * EConstr.rel_declaration) list;
  local_len : int;
  env : Environ.env;
  db2name : Names.Id.t Int.Map.t;
  name2db : int Names.Id.Map.t;
  db2rel : int Int.Map.t;
  names : Id.Set.t;
  options : options;
}
let upcast (x : [> `Options ] coq_context) : full coq_context = (x :> full coq_context)

let pr_coq_ctx { env; db2name; db2rel } sigma =
  let open Pp in
  v 0 (
    str "Mapping from DBL:"++ cut () ++ str "  " ++
    v 0 (prlist_with_sep cut (fun (i,n) -> str(E.Constants.show i) ++ str " |-> " ++ Id.print n)
        (Int.Map.bindings db2name)) ++ cut () ++
    v 0 (prlist_with_sep cut (fun (i,n) -> str(E.Constants.show i) ++ str " |-> " ++ int n)
      (Int.Map.bindings db2rel)) ++ cut () ++
    str "Named:" ++ cut () ++ str "  " ++
    v 0 (Printer.pr_named_context_of env sigma) ++ cut () ++
    str "Rel:" ++ cut () ++ str "  " ++
    v 0 (Printer.pr_rel_context_of env sigma) ++ cut ()
  )

let in_coq_fresh ~id_only =
  let mk_fresh dbl =
    Id.of_string_soft
      (Printf.sprintf "elpi_ctx_entry_%d_" dbl) in
fun ~depth dbl name ~coq_ctx:{names}->
  match in_coq_name ~depth name with
  | Name.Anonymous when id_only -> Name.Name (mk_fresh dbl)
  | Name.Anonymous as x -> x
  | Name.Name id when Id.Set.mem id names -> Name.Name (mk_fresh dbl)
  | Name.Name id as x -> x

let in_coq_annot ~depth t = Context.make_annot (in_coq_name ~depth t) Sorts.Relevant

let in_coq_fresh_annot_name ~depth ~coq_ctx dbl t =
  Context.make_annot (in_coq_fresh ~id_only:false ~depth ~coq_ctx dbl t) Sorts.Relevant

let in_coq_fresh_annot_id ~depth ~coq_ctx dbl t =
  let get_name = function Name.Name x -> x | Name.Anonymous -> assert false in
  Context.make_annot (in_coq_fresh ~id_only:true ~depth ~coq_ctx dbl t |> get_name) Sorts.Relevant

(* universes *)
let univin, isuniv, univout, univ_to_be_patched =
  let { CD.cin; isc; cout }, univ = CD.declare {
    CD.name = "univ";
    doc = "Univ.Universe.t";
    pp = (fun fmt x ->
      let s = Pp.string_of_ppcmds (Univ.Universe.pr x) in
      let l = string_split_on_char '.' s in
      let s = match List.rev l with
        | x :: y :: _ -> y ^ "." ^ x
        | _ -> s in
      Format.fprintf fmt "«%s»" s);
    compare = Univ.Universe.compare;
    hash = Univ.Universe.hash;
    hconsed = false;
    constants = [];
  } in
  cin, isc, cout, univ
;;

let unspec2opt = function Elpi.Builtin.Given x -> Some x | Elpi.Builtin.Unspec -> None
let opt2unspec = function Some x -> Elpi.Builtin.Given x | None -> Elpi.Builtin.Unspec

(* constants *)

type global_constant = Variable of Names.Id.t  | Constant of Names.Constant.t
let hash_global_constant = function
  | Variable id -> Names.Id.hash id
  | Constant c -> Names.Constant.CanOrd.hash c
let compare_global_constant x y = match x,y with
  | Variable v1, Variable v2 -> Names.Id.compare v1 v2
  | Constant c1, Constant c2 -> Names.Constant.CanOrd.compare c1 c2
  | Variable _, _ -> -1
  | _ -> 1

let global_constant_of_globref = function
  | GlobRef.VarRef x -> Variable x
  | GlobRef.ConstRef x -> Constant x
  | x -> CErrors.anomaly Pp.(str"not a global constant: " ++ (Printer.pr_global x))

let ({ CD.isc = isconstant; cout = constantout },constant), (_,inductive), (_,constructor) =
  let open API.RawOpaqueData in
  declare {
    name = "constant";
    doc = "Global constant name";
    pp = (fun fmt x ->
      let x = match x with
        | Variable x -> GlobRef.VarRef x
        | Constant c -> GlobRef.ConstRef c in
      Format.fprintf fmt "«%a»" Pp.pp_with (Printer.pr_global x));
    compare = compare_global_constant;
    hash = hash_global_constant;
    hconsed = false;
    constants = [];
  },
  declare {
    name = "inductive";
    doc = "Inductive type name";
    pp = (fun fmt x -> Format.fprintf fmt "«%a»" Pp.pp_with (Printer.pr_global (GlobRef.IndRef x)));
    compare = Names.Ind.CanOrd.compare;
    hash = Names.Ind.CanOrd.hash;
    hconsed = false;
    constants = [];
  },
  declare {
    name = "constructor";
    doc = "Inductive constructor name";
    pp = (fun fmt x -> Format.fprintf fmt "«%a»" Pp.pp_with (Printer.pr_global (GlobRef.ConstructRef x)));
    compare = Names.Construct.CanOrd.compare;
    hash = Names.Construct.CanOrd.hash;
    hconsed = false;
    constants = [];
  }
;;

let collect_term_variables ~depth t =
  let rec aux ~depth acc t =
    match E.look ~depth t with
    | E.CData c when isconstant c ->
        begin match constantout c with
        | Variable id -> id :: acc
        | _ -> acc
        end
    | x -> fold_elpi_term aux acc ~depth x
  in
  aux ~depth [] t


let gref =
  let open GlobRef in
  let open API.AlgebraicData in declare {
    ty = API.Conversion.TyName "gref";
    doc = "Global objects: inductive types, inductive constructors, definitions";
    pp = (fun fmt x ->
            Format.fprintf fmt "«%a»" Pp.pp_with (Printer.pr_global x));
    constructors = [
      K ("const", "Nat.add, List.append, ...",
          A (constant,N),
          B (function Variable v -> VarRef v | Constant c -> ConstRef c),
          M (fun ~ok ~ko -> function VarRef v -> ok (Variable v) | ConstRef c -> ok (Constant c) | _ -> ko ()));
      K ("indt",  "nat, list, ...",
          A (inductive,N),
          B (fun i -> IndRef i),
          M (fun ~ok ~ko -> function IndRef i -> ok i | _ -> ko ()));
      K ("indc",  "O, S, nil, cons, ...",
          A (constructor,N),
          B (fun c -> ConstructRef c),
          M (fun ~ok ~ko -> function ConstructRef c -> ok c | _ -> ko ()));
    ]
} |> API.ContextualConversion.(!<)

let abbreviation =
  let open API.OpaqueData in
  declare {
    name = "abbreviation";
    doc = "Name of an abbreviation";
    pp = (fun fmt x -> Format.fprintf fmt "«%s»" (KerName.to_string x));
    compare = KerName.compare;
    hash = KerName.hash;
    hconsed = false;
    constants = [];
  }

module GROrd = struct
  include Names.GlobRef.CanOrd
  let show x = Pp.string_of_ppcmds (Printer.pr_global x)
  let pp fmt x = Format.fprintf fmt "%a" Pp.pp_with (Printer.pr_global x)
end
module GRMap = U.Map.Make(GROrd)
module GRSet = U.Set.Make(GROrd)

let globalc  = E.Constants.declare_global_symbol "global"

let in_elpi_gr ~depth s r =
  let s, t, gl = gref.API.Conversion.embed ~depth s r in
  assert (gl = []);
  E.mkApp globalc t []

let in_coq_gref ~depth ~origin ~failsafe s t =
  try
    let s, t, gls = gref.API.Conversion.readback ~depth s t in
    assert(gls = []);
    s, t
  with API.Conversion.TypeErr _ ->
    if failsafe then
      s, Coqlib.lib_ref "elpi.unknown_gref"
    else
      err Pp.(str "The term " ++ str(pp2string (P.term depth) origin) ++
        str " cannot be represented in Coq since its gref part is illformed")

let mpin, ismp, mpout, modpath =
  let { CD.cin; isc; cout }, x = CD.declare {
    CD.name = "modpath";
    doc = "Name of a module /*E*/";
    pp = (fun fmt x ->
            Format.fprintf fmt "«%s»" (Names.ModPath.to_string x));
    compare = Names.ModPath.compare;
    hash = Names.ModPath.hash;
    hconsed = false;
    constants = [];
  } in
  cin, isc, cout, x
;;
let mptyin, istymp, mptyout, modtypath =
  let { CD.cin; isc; cout }, x = CD.declare {
    CD.name = "modtypath";
    doc = "Name of a module type /*E*/";
    pp = (fun fmt x ->
            Format.fprintf fmt "«%s»" (Names.ModPath.to_string x));
    compare = Names.ModPath.compare;
    hash = Names.ModPath.hash;
    hconsed = false;
    constants =[];
  } in
  cin, isc, cout, x
;;

let in_elpi_modpath ~ty mp = if ty then mptyin mp else mpin mp
let is_modpath ~depth t =
  match E.look ~depth t with E.CData x -> ismp x | _ -> false
let is_modtypath ~depth t =
  match E.look ~depth t with E.CData x -> istymp x | _ -> false
let in_coq_modpath ~depth t =
  match E.look ~depth t with
  | E.CData x when ismp x -> mpout x
  | E.CData x when istymp x -> mptyout x
  | _ -> assert false

(* ********************************* }}} ********************************** *)

(* {{{ constants (app, fun, ...) ****************************************** *)
(* binders *)
let lamc   = E.Constants.declare_global_symbol "fun"
let in_elpi_lam n s t = E.mkApp lamc (in_elpi_name n) [s;E.mkLam t]

let prodc  = E.Constants.declare_global_symbol "prod"
let in_elpi_prod n s t = E.mkApp prodc (in_elpi_name n) [s;E.mkLam t]

let letc   = E.Constants.declare_global_symbol "let"
let in_elpi_let n b s t = E.mkApp letc (in_elpi_name n) [s;b;E.mkLam t]

(* other *)
let appc   = E.Constants.declare_global_symbol "app"

let in_elpi_app_Arg ~depth hd args =
    match E.look ~depth hd, args with
    | E.Const c, [] -> assert false
    | E.Const c, x :: xs -> E.mkApp c x xs
    | E.App(c,x,xs), _ -> E.mkApp c x (xs@args)
    | _ -> assert false

let flatten_appc ~depth hd (args : E.term list) =
  match E.look ~depth hd with
  | E.App(c,x,[]) when c == appc ->
      E.mkApp appc (U.list_to_lp_list (U.lp_list_to_list ~depth x @ args)) []
  | _ -> E.mkApp appc (U.list_to_lp_list (hd :: args)) []

let in_elpi_appl ~depth hd (args : E.term list) =
  if args = [] then hd
  else flatten_appc ~depth hd args

let in_elpi_app ~depth hd (args : E.term array) =
  in_elpi_appl ~depth hd (Array.to_list args)

let matchc = E.Constants.declare_global_symbol "match"

let in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs =
  E.mkApp matchc t [rt; U.list_to_lp_list bs]

let fixc   = E.Constants.declare_global_symbol "fix"

let in_elpi_fix name rno ty bo =
  E.mkApp fixc (in_elpi_name name) [CD.of_int rno; ty; E.mkLam bo]

let primitivec   = E.Constants.declare_global_symbol "primitive"

type primitive_value =
  | Uint63 of Uint63.t
  | Float64 of Float64.t
  | Projection of Projection.t

let primitive_value : primitive_value API.Conversion.t =
  let module B = Coq_elpi_utils in
  let open API.AlgebraicData in  declare {
  ty = API.Conversion.TyName "primitive-value";
  doc = "Primitive values";
  pp = (fun fmt -> function
    | Uint63 i -> Format.fprintf fmt "Type"
    | Float64 f -> Format.fprintf fmt "Set"
    | Projection p -> Format.fprintf fmt "");
  constructors = [
    K("uint63","unsigned integers over 63 bits",A(B.uint63,N),
      B (fun x -> Uint63 x),
      M (fun ~ok ~ko -> function Uint63 x -> ok x | _ -> ko ()));
    K("float64","double precision foalting points",A(B.float64,N),
      B (fun x -> Float64 x),
      M (fun ~ok ~ko -> function Float64 x -> ok x | _ -> ko ()));
    K("proj","primitive projection",A(B.projection,A(API.BuiltInData.int,N)),
      B (fun p n -> Projection p),
      M (fun ~ok ~ko -> function Projection p -> ok p Names.Projection.(arg p + npars p) | _ -> ko ()));
  ]
} |> API.ContextualConversion.(!<)
  
let in_elpi_primitive ~depth state i =
  let state, i, _ = primitive_value.API.Conversion.embed ~depth state i in
  state, E.mkApp primitivec i []
 

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : Evd.evar_map -> elpi *************************************** *)

let command_mode =
  S.declare ~name:"coq-elpi:command-mode"
    ~init:(fun () -> true)
    ~start:(fun x -> x)
    ~pp:(fun fmt b -> Format.fprintf fmt "%b" b)

module CoqEngine_HOAS : sig 

  type coq_engine  = {
   global_env : Environ.env;
   sigma : Evd.evar_map; (* includes universe constraints *)

  }

  val show_coq_engine : coq_engine -> string

  val engine : coq_engine S.component

  val from_env_keep_univ_of_sigma : Environ.env -> Evd.evar_map -> coq_engine
  val from_env_sigma : Environ.env -> Evd.evar_map -> coq_engine

end = struct

 type coq_engine = {
   global_env : Environ.env [@printer (fun _ _ -> ())];
   sigma : Evd.evar_map [@printer (fun fmt m ->
     Format.fprintf fmt "%a" Pp.pp_with (Termops.pr_evar_map None (Global.env()) m))];
 }
 let pp_coq_engine fmt { sigma } =
   Format.fprintf fmt "%a" Pp.pp_with (Termops.pr_evar_map None (Global.env()) sigma)

let show_coq_engine = Format.asprintf "%a" pp_coq_engine

 let from_env_sigma global_env sigma =
   {
     global_env;
     sigma;
   }

 let from_env env = from_env_sigma env (Evd.from_env env)

 let from_env_keep_univ_of_sigma env sigma0 =
   let uctx = UState.update_sigma_univs (Evd.evar_universe_context sigma0) (Environ.universes env) in
   let sigma = Evd.from_ctx (UState.demote_global_univs env uctx) in
   from_env_sigma env sigma
 let init () = from_env (Global.env ())

 let engine : coq_engine S.component =
   S.declare ~name:"coq-elpi:evmap-constraint-type"
     ~pp:pp_coq_engine ~init ~start:(fun _ -> init())

end

open CoqEngine_HOAS

(* Bidirectional mapping between Elpi's UVars and Coq's Evars.

   Coq evar E is represented by a constraint
   
      evar X1 ty X2

   and eventually a goal

      goal ctx X1 ty attrs

   and the bidirectional mapping

      E <-> X2 \in UVElabMap
      E <-> X1 \in UVRawMap
*)
module CoqEvarKey = struct
  type t = Evar.t
  let compare = Evar.compare
  let pp fmt t = Format.fprintf fmt "%a" Pp.pp_with (Evar.print t)
  let show t = Format.asprintf "%a" pp t
end
module UVElabMap = F.Map(CoqEvarKey)
module UVRawMap = F.Map(CoqEvarKey)

module UVMap = struct
  let elpi k s =
    UVRawMap.elpi k (S.get UVRawMap.uvmap s),
    UVElabMap.elpi k (S.get UVElabMap.uvmap s)

  let add k raw elab s =
    let s = S.update UVRawMap.uvmap s (UVRawMap.add raw k) in
    let s = S.update UVElabMap.uvmap s (UVElabMap.add elab k) in
    s

  let host elab s =
    try
      UVElabMap.host elab (S.get UVElabMap.uvmap s)
    with Not_found ->
      UVRawMap.host elab (S.get UVRawMap.uvmap s)
      
  let show s =
    "RAW:\n" ^ UVRawMap.show (S.get UVRawMap.uvmap s) ^
    "ELAB:\n" ^ UVElabMap.show (S.get UVElabMap.uvmap s)

  let empty s =
    let s = S.set UVRawMap.uvmap s UVRawMap.empty in
    let s = S.set UVElabMap.uvmap s UVElabMap.empty in
    s
  
  let fold f s acc =
    UVElabMap.fold (fun ev uv sol acc ->
      let ruv = UVRawMap.elpi ev (S.get UVRawMap.uvmap s) in
      f ev ruv uv sol acc)
    (S.get UVElabMap.uvmap s) acc

  let remove_host evar s =
    let s = S.update UVRawMap.uvmap s (UVRawMap.remove_host evar) in
    let s = S.update UVElabMap.uvmap s (UVElabMap.remove_host evar) in
    s

  let filter_host f s =
    let s = S.update UVRawMap.uvmap s (UVRawMap.filter (fun evar _ -> f evar)) in
    let s = S.update UVElabMap.uvmap s (UVElabMap.filter (fun evar _ -> f evar)) in
    s

end

let section_ids env =
    let named_ctx = Environ.named_context env in
    Context.Named.fold_inside
      (fun acc x -> Context.Named.Declaration.get_id x :: acc)
      ~init:[] named_ctx

(* map from Elpi evars and Coq's universe levels *)
module UM = F.Map(struct
  type t = Univ.Universe.t
  let compare = Univ.Universe.compare
  let show x = Pp.string_of_ppcmds @@ Univ.Universe.pr x
  let pp fmt x = Format.fprintf fmt "%a" Pp.pp_with (Univ.Universe.pr x)
end)

let um = S.declare ~name:"coq-elpi:evar-univ-map"
  ~pp:UM.pp ~init:(fun () -> UM.empty) ~start:(fun x -> x)

let new_univ state =
  S.update_return engine state (fun ({ sigma } as x) ->
    let sigma, v = Evd.new_univ_level_variable UState.UnivRigid sigma in
    let u = Univ.Universe.make v in
    let sigma = Evd.add_universe_constraints sigma
        (UnivProblem.Set.singleton (UnivProblem.ULe (Univ.type1_univ,u))) in
    { x with sigma }, u)

(* We patch data_of_cdata by forcing all output universes that
 * are unification variables to be a Coq universe variable, so that
 * we can always call Coq's API *)
let univ =
  (* turn UVars into fresh universes *)
  { univ_to_be_patched with
  API.Conversion.readback = begin fun ~depth state t ->
    match E.look ~depth t with
    | E.UnifVar (b,args) ->
       let m = S.get um state in
       begin try
         let u = UM.host b m in
         state, u, []
       with Not_found ->
         let state, u = new_univ state in
         let state = S.update um state (UM.add b u) in
         state, u, [ E.mkApp E.Constants.eqc (E.mkUnifVar b ~args state) [univin u]]
       end
    | _ -> univ_to_be_patched.API.Conversion.readback ~depth state t
  end
}

let universe =
  let open API.AlgebraicData in  declare {
  ty = API.Conversion.TyName "universe";
  doc = "Universes (for the sort term former)";
  pp = (fun fmt -> function
    | Sorts.Type _ -> Format.fprintf fmt "Type"
    | Sorts.Set -> Format.fprintf fmt "Set"
    | Sorts.Prop -> Format.fprintf fmt "Prop"
    | Sorts.SProp -> Format.fprintf fmt "SProp");
  constructors = [
    K("prop","impredicative sort of propositions",N,
      B Sorts.prop,
      M (fun ~ok ~ko -> function Sorts.Prop -> ok | _ -> ko ()));
    K("sprop","impredicative sort of propositions with definitional proof irrelevance",N,
      B Sorts.sprop,
      M (fun ~ok ~ko -> function Sorts.SProp -> ok | _ -> ko ()));
    K("typ","predicative sort of data (carries a level)",A(univ,N),
      B Sorts.sort_of_univ,
      M (fun ~ok ~ko -> function
        | Sorts.Type x -> ok x
        | Sorts.Set -> ok Univ.type0_univ
        | _ -> ko ()));
  ]
} |> API.ContextualConversion.(!<)

let sortc  = E.Constants.declare_global_symbol "sort"
let propc  = E.Constants.declare_global_symbol "prop"
let spropc = E.Constants.declare_global_symbol "sprop"
let typc   = E.Constants.declare_global_symbol "typ"

let in_elpi_sort s =
  E.mkApp
    sortc
    (match s with
    | Sorts.SProp -> E.mkGlobal spropc
    | Sorts.Prop -> E.mkGlobal propc
    | Sorts.Set -> E.mkApp typc (univin Univ.type0_univ) []
    | Sorts.Type u -> E.mkApp typc (univin u) [])
    []

let in_elpi_flex_sort t = E.mkApp sortc (E.mkApp typc t []) []

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : EConstr.t -> elpi ******************************************* *)

let check_univ_inst univ_inst =
  if not (Univ.Instance.is_empty univ_inst) then
    nYI "HOAS universe polymorphism"
    
let get_sigma s = (S.get engine s).sigma
let get_global_env s = (S.get engine s).global_env

let declare_evc = E.Constants.declare_global_symbol "declare-evar"

let pp_coq_ctx { env } state =
  try
    Printer.pr_named_context_of env (get_sigma state)
  with e when CErrors.noncritical e ->
    Pp.(str "error in printing: " ++ str (Printexc.to_string e))

let get_optionc   = E.Constants.declare_global_symbol "get-option"

let get_options ~depth hyps state =
  let is_string ~depth t =
    match E.look ~depth t with
    | E.CData d -> CD.is_string d
    | _ -> false in
  let get_string ~depth t =
    match E.look ~depth t with
    | E.CData d -> CD.to_string d
    | _ -> assert false in
  let options =
    E.of_hyps hyps |> CList.map_filter (fun { E.hdepth = depth; E.hsrc = t } ->
    match E.look ~depth t with
    | E.App(c,name,[p]) when c == get_optionc && is_string ~depth name ->
        Some (get_string ~depth name, (p,depth))
    | _ -> None) in
  let map = List.fold_right (fun (k,v) m -> API.Data.StrMap.add k v m) options API.Data.StrMap.empty in
  let get_bool_option name =
    try
      let t, depth = API.Data.StrMap.find name map in
      let _, b, _ = Elpi.Builtin.bool.API.Conversion.readback ~depth state t in
      Some b
    with Not_found -> None in
  let get_string_option name =
    try
      let t, depth = API.Data.StrMap.find name map in
      let _, b, _ = API.BuiltInData.string.API.Conversion.readback ~depth state t in
      Some b
    with Not_found -> None in
  let get_int_option name =
    try
      let t, depth = API.Data.StrMap.find name map in
      let _, b, _ = API.BuiltInData.int.API.Conversion.readback ~depth state t in
      Some b
    with Not_found -> None in
  let locality s =
    if s = Some "default" then None
    else if s = Some "local" then Some true
    else if s = Some "global" then Some false
    else if s = None then None
    else err Pp.(str"Unknown locality attribute: " ++ str (Option.get s)) in
  let pp s =
    if s = Some "all" then All
    else if s = Some "most" then Most
    else Normal in
  let ppwidth = function Some i -> i | None -> 80 in
  let pplevel = function None -> Constrexpr.LevelSome | Some i -> Constrexpr.LevelLe i in
  let get_pair_option fst snd name =
    try
      let t, depth = API.Data.StrMap.find name map in
      let _, b, _ = Elpi.Builtin.(pair (unspec fst) (unspec snd)).API.Conversion.readback ~depth state t in
      Some b
    with Not_found -> None in
  let empty2none = function Some "" -> None | x -> x in
  let deprecation = function
    | None -> None
    | Some(since,note) ->
        let since = unspec2opt since |> empty2none in
        let note = unspec2opt note |> empty2none in
        Some { Deprecation.since; note } in
  {
    hoas_holes =
      begin match get_bool_option "HOAS:holes" with
      | None -> None
      | Some true -> Some Heuristic
      | Some false -> Some Verbatim end;
    local = locality @@ get_string_option "coq:locality";
    deprecation = deprecation @@ get_pair_option API.BuiltInData.string API.BuiltInData.string "coq:deprecation";
    primitive = get_bool_option "coq:primitive";
    failsafe = false;
    ppwidth = ppwidth @@ get_int_option "coq:ppwidth";
    pp = pp @@ get_string_option "coq:pp";
    pplevel = pplevel @@ get_int_option "coq:pplevel";
    using = get_string_option "coq:using";
  }

let mk_coq_context ~options state =
  let env = get_global_env state in
  let section = section_ids env in
  {
    section;
    section_len = List.length section;
    proof = [];
    proof_len = 0;
    local = [];
    local_len = 0;
    db2name = Int.Map.empty;
    name2db = Names.Id.Map.empty;
    db2rel = Int.Map.empty;
    names = Id.Set.empty;
    env;
    options;
  }

let push_coq_ctx_proof i e coq_ctx =
  assert(coq_ctx.local = []);
  let id = Context.Named.Declaration.get_id e in
 {
  coq_ctx with
  proof = e :: coq_ctx.proof;
  proof_len = 1 + coq_ctx.proof_len;
  env = EConstr.push_named e coq_ctx.env;
  db2name = Int.Map.add i id coq_ctx.db2name;
  name2db = Names.Id.Map.add id i coq_ctx.name2db;
  names = Id.Set.add id coq_ctx.names;
}

let push_coq_ctx_local i e coq_ctx =
 let rel = 1 + coq_ctx.local_len in
 {
  coq_ctx with
  local = (i,e) :: coq_ctx.local;
  local_len = rel;
  db2rel = Int.Map.add i rel coq_ctx.db2rel;
  env = EConstr.push_rel e coq_ctx.env;
}

(* Not sure this is sufficient, eg we don't restrict evars, but elpi shuld... *)
let restrict_coq_context live_db state { proof; proof_len; local; name2db; env; options;  } =
  let named_ctx =
    mk_coq_context ~options state |> List.fold_right (fun e ctx ->
      let id = Context.Named.Declaration.get_id e in
      let db = Names.Id.Map.find id name2db in
      if List.mem db live_db
      then push_coq_ctx_proof db e ctx
      else ctx) proof in

  debug Pp.(fun () ->
      str "restrict_coq_context: named: " ++
      Printer.pr_named_context_of named_ctx.env (get_sigma state));

  let subst_rel_decl env k s = function
    | Context.Rel.Declaration.LocalAssum(n,t) ->

      debug Pp.(fun () ->
          Printer.pr_econstr_env env (get_sigma state) t
          ++str "--"++ int k ++ str"->" ++
          Printer.pr_econstr_env env (get_sigma state) (EConstr.Vars.substnl s k t));

       Context.Rel.Declaration.LocalAssum(n,EConstr.Vars.substnl s k t)
    | Context.Rel.Declaration.LocalDef(n,t,b) ->
       Context.Rel.Declaration.LocalDef(n,EConstr.Vars.substnl s k t,EConstr.Vars.substnl s k b) in

  (named_ctx,[]) |> List.fold_right (fun (db,e) (ctx,s) ->

      debug Pp.(fun () ->
          str"restrict_coq_context: cur rel ctx: " ++
          Printer.pr_rel_context_of ctx.env (get_sigma state) ++ fnl() ++
          str"restrict_coq_context: cur subst: " ++
          prlist_with_sep spc (Printer.pr_econstr_env ctx.env (get_sigma state)) s ++ fnl() ++
          str"restrict_coq_context: looking at " ++
          Names.Name.print (Context.Rel.Declaration.get_name e)
          ++ str"(dbl " ++ int db ++ str")");

    if List.mem db live_db
    then push_coq_ctx_local db (subst_rel_decl ctx.env 0 s e) ctx, (EConstr.mkRel 1) :: List.map (EConstr.Vars.lift 1) s
    else ctx, EConstr.mkProp :: s) local |>
  fun (x,_) -> x

let info_of_evar ~env ~sigma ~section k =
  let open Context.Named in
  let { Evd.evar_concl } as info =
    Evarutil.nf_evar_info sigma (Evd.find sigma k) in
  let filtered_hyps = Evd.evar_filtered_hyps info in
  let ctx = EC.named_context_of_val filtered_hyps in
  let ctx = ctx |> List.filter (fun x ->
    not(CList.mem_f Id.equal (Declaration.get_id x) section)) in
  evar_concl, ctx, Environ.reset_with_named_context filtered_hyps env

(* ******************************************* *)
(*  <---- depth ---->                          *)
(*  proof_ctx |- pis \ t                       *)
(* ******************************************* *)
type hyp = { ctx_entry : E.term; depth : int }

let declc = E.Constants.declare_global_symbol "decl"
let defc = E.Constants.declare_global_symbol "def"
let evarc = E.Constants.declare_global_symbol "evar"

let mk_pi_arrow hyp rest =
  E.mkApp E.Constants.pic (E.mkLam (E.mkApp E.Constants.implc hyp [rest])) []

let mk_decl ~depth name ~ty =
  E.mkApp declc E.(mkConst depth) [in_elpi_name name; ty]

let mk_def ~depth name ~bo ~ty =
  E.mkApp defc E.(mkConst depth) [in_elpi_name name; ty; bo]

let rec constr2lp coq_ctx ~calldepth ~depth state t =
  assert(depth >= coq_ctx.proof_len);
  let { sigma } = S.get engine state in
  let gls = ref [] in
  let rec aux ~depth env state t = match EC.kind sigma t with
    | C.Rel n -> state, E.mkConst (depth - n)
    | C.Var n ->
         begin
          try state, E.mkConst @@ Names.Id.Map.find n coq_ctx.name2db
          with Not_found ->
            assert(List.mem n coq_ctx.section);
            state, in_elpi_gr ~depth state (G.VarRef n)
         end
    | C.Meta _ -> nYI "constr2lp: Meta"
    | C.Evar (k,args) ->
        (* the evar is created at the depth the conversion is called, not at
          the depth at which it is found *)
         let state, elpi_uvk, _, gsl_t = in_elpi_evar ~calldepth k state in
         gls := gsl_t @ !gls;
         let args = CList.firstn (List.length args - coq_ctx.section_len) args in
         let state, args = CList.fold_left_map (aux ~depth env) state args in
         state, E.mkUnifVar elpi_uvk ~args:(List.rev args) state
    | C.Sort s -> state, in_elpi_sort (EC.ESorts.kind sigma s)
    | C.Cast (t,_,ty0) ->
         let state, t = aux ~depth env state t in
         let state, ty = aux ~depth env state ty0 in
         let env = EConstr.push_rel Context.Rel.Declaration.(LocalAssum(Context.make_annot Anonymous Sorts.Relevant,ty0)) env in
         let state, self = aux ~depth:(depth+1) env state (EC.mkRel 1) in
         state, in_elpi_let Names.Name.Anonymous t ty self
    | C.Prod(n,s0,t) ->
         let state, s = aux ~depth env state s0 in
         let env = EConstr.push_rel Context.Rel.Declaration.(LocalAssum(n,s0)) env in
         let state, t = aux ~depth:(depth+1) env state t in
         state, in_elpi_prod n.Context.binder_name s t
    | C.Lambda(n,s0,t) ->
         let state, s = aux ~depth env state s0 in
         let env = EConstr.push_rel Context.Rel.Declaration.(LocalAssum(n,s0)) env in
         let state, t = aux ~depth:(depth+1) env state t in
         state, in_elpi_lam n.Context.binder_name s t
    | C.LetIn(n,b0,s0,t) ->
         let state, b = aux ~depth env state b0 in
         let state, s = aux ~depth env state s0 in
         let env = EConstr.push_rel Context.Rel.Declaration.(LocalDef(n,b0,s0)) env in
         let state, t = aux ~depth:(depth+1) env state t in
         state, in_elpi_let n.Context.binder_name b s t
    | C.App(hd,args) ->
         let state, hd = aux ~depth env state hd in
         let state, args = CArray.fold_left_map (aux ~depth env) state args in
         state, in_elpi_app ~depth hd args
    | C.Const(c,i) ->
         check_univ_inst (EC.EInstance.kind sigma i);
         let ref = G.ConstRef c in
         state, in_elpi_gr ~depth state ref
    | C.Ind(ind,i) ->
         check_univ_inst (EC.EInstance.kind sigma i);
         state, in_elpi_gr ~depth state (G.IndRef ind)
    | C.Construct(construct,i) ->
         check_univ_inst (EC.EInstance.kind sigma i);
         state, in_elpi_gr ~depth state (G.ConstructRef construct)
    | C.Case(ci, u, pms, rt, iv, t, bs) ->
         let (_, rt, _, t, bs) = EConstr.expand_case env sigma (ci, u, pms, rt, iv, t, bs) in
         let state, t = aux ~depth env state t in
         let state, rt = aux ~depth env state rt in
         let state, bs = CArray.fold_left_map (aux ~depth env) state bs in
         state,
         in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt
           (Array.to_list bs)
    | C.Fix(([| rarg |],_),([| name |],[| typ0 |], [| bo |])) ->
         let state, typ = aux ~depth env state typ0 in
         let env = EConstr.push_rel Context.Rel.Declaration.(LocalAssum(name,typ0)) env in
         let state, bo = aux ~depth:(depth+1) env state bo in
         state, in_elpi_fix name.Context.binder_name rarg typ bo
    | C.Proj(p,t) ->
         let state, t = aux ~depth env state t in
         let state, p = in_elpi_primitive ~depth state (Projection p) in
         state, in_elpi_app ~depth p [|t|]
    | C.Fix _ -> nYI "HOAS for mutual fix"
    | C.CoFix _ -> nYI "HOAS for cofix"
    | C.Int i -> in_elpi_primitive ~depth state (Uint63 i)
    | C.Float f -> in_elpi_primitive ~depth state (Float64 f)
    | C.Array _ -> nYI "HOAS for persistent arrays"
  in
  debug Pp.(fun () ->
      str"term2lp: depth=" ++ int depth ++
      str " ctx=" ++ pp_coq_ctx coq_ctx state ++
      str " term=" ++Printer.pr_econstr_env (get_global_env state) (get_sigma state) t);
  let state, t = aux ~depth coq_ctx.env state t in
  debug Pp.(fun () -> str"term2lp (out): " ++ str (pp2string (P.term depth) t));
  state, t, !gls

and under_coq2elpi_ctx ~calldepth state ctx ?(mk_ctx_item=fun _ decl _ _ _ -> mk_pi_arrow decl) kont =
  let open Context.Named.Declaration in
  let gls = ref [] in
  let rec aux i ~depth coq_ctx hyps state = function
    | [] ->
        let state, t, gls_t = kont coq_ctx hyps ~depth state in
        gls := gls_t @ !gls;
        state, t
    | LocalAssum (Context.{binder_name=coq_name}, ty) as e :: rest ->
        let name = Name coq_name in
        let state, ty, gls_ty = constr2lp coq_ctx ~calldepth ~depth:(depth+1) state ty in
        gls := gls_ty @ !gls;
        let hyp = mk_decl ~depth name ~ty in
        let hyps = { ctx_entry = hyp ; depth = depth + 1 } :: hyps in
        let coq_ctx = push_coq_ctx_proof depth e coq_ctx in
        let state, rest = aux (succ i) ~depth:(depth+1) coq_ctx hyps state rest in
        state, mk_ctx_item i hyp name ty None rest
      | LocalDef (Context.{binder_name=coq_name},bo,ty) as e :: rest ->
        let name = Name coq_name in
        let state, ty, gls_ty = constr2lp coq_ctx ~calldepth ~depth:(depth+1) state ty in
        let state, bo, gls_bo = constr2lp coq_ctx ~calldepth ~depth:(depth+1) state bo in
        gls := gls_ty @ gls_bo @ !gls;
        let hyp = mk_def ~depth name ~bo ~ty in
        let hyps = { ctx_entry = hyp ; depth = depth + 1 } :: hyps in
        let coq_ctx = push_coq_ctx_proof depth e coq_ctx in
        let state, rest = aux (succ i) ~depth:(depth+1) coq_ctx hyps state rest in
        state, mk_ctx_item i hyp name ty (Some bo) rest
  in
    let state, t = aux 0 ~depth:calldepth (mk_coq_context ~options:default_options state) [] state (List.rev ctx) in
    state, t, !gls

and in_elpi_evar_concl evar_concl ~raw_uvar elpi_evk coq_ctx hyps ~calldepth ~depth state =
  let state, evar_concl, gls_evar_concl = constr2lp coq_ctx ~calldepth ~depth state evar_concl in
  let args = CList.init coq_ctx.proof_len (fun i -> E.mkConst @@ i + calldepth) in
  let hyps = List.map (fun { ctx_entry; depth = from } ->
    U.move ~from ~to_:depth ctx_entry) hyps in
  state, U.list_to_lp_list hyps,
  (E.mkUnifVar raw_uvar ~args state),
  (E.mkUnifVar elpi_evk ~args state),
  evar_concl, gls_evar_concl

and in_elpi_evar_info ~calldepth ~env ~sigma ctx ~raw_ev:elpi_revk elpi_evk evar_concl state =
  under_coq2elpi_ctx ~calldepth state ctx (fun coq_ctx hyps ~depth state ->
    let state, hyps, raw_ev, ev, ty, gls =
      in_elpi_evar_concl evar_concl ~raw_uvar:elpi_revk elpi_evk coq_ctx hyps
        ~calldepth ~depth state in
    state, E.mkApp declare_evc hyps [raw_ev; ty; ev], gls)

and in_elpi_evar ~calldepth k state =
  debug Pp.(fun () -> str"in_elpi_evar:" ++ Evar.print k);
  try
    let elpi_raw_evk, elpi_evk = UVMap.elpi k state in
    debug Pp.(fun () ->
        str"in_elpi_evar: known " ++
        Evar.print k ++ str" as " ++ str(F.Elpi.show elpi_evk));
    state, elpi_evk, elpi_raw_evk, []
  with Not_found ->
    let state, elpi_evk = F.Elpi.make state in
    let state, elpi_raw_evk = F.Elpi.make state in
    let state, gls = in_elpi_fresh_evar ~calldepth k ~raw_ev:elpi_raw_evk elpi_evk state in
    state, elpi_evk, elpi_raw_evk, gls

and in_elpi_fresh_evar ~calldepth k ~raw_ev elpi_evk state =
    let { sigma; global_env } as e = S.get engine state in
    let state = UVMap.add k raw_ev elpi_evk state in
    debug Pp.(fun () -> str"in_elpi_fresh_evar: unknown " ++ Evar.print k);
    let evar_concl, ctx, _ = info_of_evar ~env:global_env ~sigma ~section:(section_ids global_env) k in
    let state, evar_decl, gls = in_elpi_evar_info ~calldepth ~env:global_env ~sigma ctx ~raw_ev elpi_evk evar_concl state in
    debug Pp.(fun () -> str"in_elpi_fresh_evar: new decl" ++ cut () ++
      str(pp2string (P.term calldepth) evar_decl));
    state, gls @ [evar_decl]
;;

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : elpi -> Constr.t * Evd.evar_map ***************************** *)

let add_constraints state c = S.update engine state (fun ({ sigma } as x) ->
  { x with sigma = Evd.add_universe_constraints sigma c })


let type_of_global state r = S.update_return engine state (fun x ->
  let ty, ctx = Typeops.type_of_global_in_context x.global_env r in
  let inst, ctx = UnivGen.fresh_instance_from ctx None in
  let ty = Vars.subst_instance_constr inst ty in
  let sigma = Evd.merge_context_set Evd.univ_rigid x.sigma ctx in
  { x with sigma }, EConstr.of_constr ty)

let body_of_constant state c = S.update_return engine state (fun x ->
  match Global.body_of_constant_body Library.indirect_accessor (Environ.lookup_constant c x.global_env) with
  | Some (bo, priv, ctx) ->
     let inst, ctx = UnivGen.fresh_instance_from ctx None in
     let bo = Vars.subst_instance_constr inst bo in
     let sigma = Evd.merge_context_set Evd.univ_rigid x.sigma ctx in
     let sigma = match priv with
     | Opaqueproof.PrivateMonomorphic () -> sigma
     | Opaqueproof.PrivatePolymorphic (_, ctx) ->
      let ctx = Util.on_snd (Univ.subst_univs_level_constraints (Univ.make_instance_subst inst)) ctx in
      Evd.merge_context_set Evd.univ_rigid sigma ctx
     in
     { x with sigma }, Some (EConstr.of_constr bo)
  | None -> x, None)

let evar_arity k state =
  let info = Evd.find (S.get engine state).sigma k in
  let filtered_hyps = Evd.evar_filtered_hyps info in
  List.length (Environ.named_context_of_val filtered_hyps)

let minimize_universes state =
  S.update engine state (fun ({ sigma } as x) ->
    { x with sigma = Evd.minimize_universes sigma })

let is_sort ~depth x =
  match E.look ~depth x with
  | E.App(s,_,[]) -> sortc == s
  | _ -> false

let is_prod ~depth x =
  match E.look ~depth x with
  | E.App(s,_,[_;_]) -> prodc == s
  | _ -> false

let is_lam ~depth x =
  match E.look ~depth x with
  | E.App(s,_,[ty;bo]) when lamc == s ->
    begin match E.look ~depth bo with
    | E.Lam bo -> Some(ty,bo)
    | _ -> None end
  | _ -> None

let pp_cst fmt { E.goal = (depth,concl); context } =
  Format.fprintf fmt "%d |> %a |- %a" depth
    (P.list (fun fmt { E.hdepth; E.hsrc } ->
        Format.fprintf fmt "%d:%a" hdepth (P.term hdepth) hsrc) ", ")
      context
     (P.term depth) concl

let find_evar var csts =
  csts |> CList.find_map (fun ({ E.goal = (depth,concl); context } as cst) ->
    match E.look ~depth concl with
    | E.App(c,x,[ty;rx]) when c == evarc ->
        begin match E.look ~depth x, E.look ~depth rx with
        | E.UnifVar(raw,args), E.UnifVar(r,_) when F.Elpi.(equal raw var || equal r var) ->
          debug Pp.(fun () ->
              str"lp2term: evar: found relevant constraint: " ++
              str(pp2string pp_cst cst)); 
          Some r
        | _ -> None end
    | _ -> None) 

let preprocess_context visible context =
  let select_ctx_entries visible { E.hdepth = depth; E.hsrc = t } =
    let isVisibleConst t = match E.look ~depth t with E.Const i -> visible i | _ -> false in
    let destConst t = match E.look ~depth t with E.Const x -> x | _ -> assert false in
    match E.look ~depth t with
    | E.App(c,v,[name;ty]) when c == declc && isVisibleConst v ->
       Some (destConst v, depth, `Decl(name,ty))
    | E.App(c,v,[name;ty;bo]) when c == defc && isVisibleConst v ->
       Some (destConst v, depth, `Def (name,ty,bo))
    | _ ->
      debug Pp.(fun () ->
          str "skip entry" ++
          str(pp2string (P.term depth) t));
      None
  in
  let ctx_hyps = CList.map_filter (select_ctx_entries visible) context in
  let dbl2ctx =
    List.fold_right (fun (i,d,e) m ->
      if Int.Map.mem i m
      then err Pp.(str "Duplicate context entry for " ++
                  str(pp2string (P.term d) (E.mkConst i)))
      else Int.Map.add i (d,e) m)
    ctx_hyps Int.Map.empty in
  dbl2ctx

let rec dblset_of_canonical_ctx ~depth acc = function
  | [] -> acc
  | x :: xs ->
      match E.look ~depth x with
      | E.Const i -> dblset_of_canonical_ctx ~depth (Int.Set.add i acc) xs
      | _ -> err Pp.(str"HOAS: non canonical constraint, the evar is applied to:" ++
                      str(pp2string (P.term depth) x))

let find_evar_decl var csts =
  csts |> CList.find_map (fun ({ E.goal = (depth,concl); context } as cst) ->
    match E.look ~depth concl with
    | E.App(c,x,[ty;rx]) when c == evarc ->
        begin match E.look ~depth x, E.look ~depth rx with
        | E.UnifVar(raw,args_raw), E.UnifVar(r,args) when F.Elpi.(equal raw var || equal r var) ->
          debug Pp.(fun () ->
              str"lp2term: evar: found relevant constraint: " ++
              str(pp2string pp_cst cst));
          let args = if F.Elpi.(equal raw var) then args_raw else args in
          let visible_set = dblset_of_canonical_ctx ~depth Int.Set.empty args in
          let dbl2ctx = preprocess_context (fun x -> Int.Set.mem x visible_set) context in
          Some (dbl2ctx, raw, r, (depth,ty), cst)
        | _ -> None end
    | _ -> None)

let analyze_scope ~depth coq_ctx args =
  let is_in_coq i =
    Int.Map.mem i coq_ctx.db2name || Int.Map.mem i coq_ctx.db2rel in
  let rec aux seen mask args needs_restriction deterministic = function
    | [] ->
        if needs_restriction then `NeedsRestriction (deterministic, List.rev mask)
        else `GoodToGo (List.rev args)
    | x :: xs ->
        match E.look ~depth x with
        | E.Const i ->
             let is_duplicate = E.Constants.Set.mem i seen in
             let keep = not is_duplicate && is_in_coq i in
             aux (E.Constants.Set.add i seen) (keep :: mask) (i::args)
               (needs_restriction || not keep) (deterministic && not is_duplicate) xs
        | _ -> aux seen (false :: mask) args true false xs
   in
      aux E.Constants.Set.empty [] [] false true args

let rec of_elpi_ctx ~calldepth syntactic_constraints depth dbl2ctx state initial_coq_ctx =

  let aux coq_ctx depth state t =
    lp2constr ~calldepth syntactic_constraints coq_ctx ~depth state t in

  let of_elpi_ctx_entry dbl coq_ctx ~depth e state =
    match e with
    | `Decl(name,ty) ->
        let id = in_coq_fresh_annot_id ~depth ~coq_ctx dbl name in
        let state, ty, gls = aux coq_ctx depth state ty in
        state, Context.Named.Declaration.LocalAssum(id,ty), gls
    | `Def(name,ty,bo) ->
        let id = in_coq_fresh_annot_id ~depth ~coq_ctx dbl name in
        let state, ty, gl1 = aux coq_ctx depth state ty in
        let state, bo, gl2 = aux coq_ctx depth state bo in
        state, Context.Named.Declaration.LocalDef(id,bo,ty), gl1 @ gl2
  in
  
  let rec ctx_entries coq_ctx state gls i =
    if i = depth then state, coq_ctx, List.(concat (rev gls))
    else (* context entry for the i-th variable *)
      if not (Int.Map.mem i dbl2ctx)
      then ctx_entries coq_ctx state gls (i+1)
      else
        let d, e = Int.Map.find i dbl2ctx in
        debug Pp.(fun () -> str "<<< context entry for DBL "++ int i ++ str" at depth" ++ int d);
        let state, e, gl1 = of_elpi_ctx_entry i coq_ctx ~depth:d e state in
        debug Pp.(fun () -> str "context entry >>>");
        let coq_ctx = push_coq_ctx_proof i e coq_ctx in
        ctx_entries coq_ctx state (gl1 :: gls) (i+1)
  in
    ctx_entries initial_coq_ctx state [] 0

(* ***************************************************************** *)
(* <-- depth -->                                                     *)
(* names |- pis |- t                                                 *)
(*   |        \- lp fresh constans                                   *)
(*   \- proof_ctx                                                    *)
(* ***************************************************************** *)

and lp2constr ~calldepth syntactic_constraints coq_ctx ~depth state ?(on_ty=false) t =
  let aux = lp2constr ~calldepth syntactic_constraints coq_ctx in
  let aux_lam coq_ctx ~depth s t = match E.look ~depth t with
  | E.Lam t -> lp2constr ~calldepth syntactic_constraints coq_ctx ~depth:(depth+1) s t
  | E.UnifVar(r,args) ->
       lp2constr ~calldepth syntactic_constraints coq_ctx ~depth:(depth+1) s
         (E.mkUnifVar r ~args:(List.map (U.move ~from:depth ~to_:(depth+1)) args @ [E.mkConst depth]) state)
  | _ -> err Pp.(str"HOAS: expecting a lambda, got: " ++ str(pp2string (P.term depth) t))
  in
  debug Pp.(fun () -> str"lp2term@" ++ int depth ++ str":" ++ str(pp2string (P.term depth) t));
  match E.look ~depth t with
  | E.App(s,p,[]) when sortc == s ->
      let state, u, gsl = universe.API.Conversion.readback ~depth state p in
      state, EC.mkSort u, gsl
 (* constants *)
  | E.App(c,d,[]) when globalc == c ->
     let state, gr = in_coq_gref ~depth ~origin:t ~failsafe:coq_ctx.options.failsafe state d in
     begin match gr with
     | G.VarRef x -> state, EC.mkVar x, []
     | G.ConstRef x -> state, EC.mkConst x, []
     | G.ConstructRef x -> state, EC.mkConstruct x, []
     | G.IndRef x -> state, EC.mkInd x, []
     end
 (* binders *)
  | E.App(c,name,[s;t]) when lamc == c || prodc == c ->
      let name = in_coq_fresh_annot_name ~depth ~coq_ctx depth name in
      let state, s, gl1 = aux ~depth state ~on_ty:true s in
      let coq_ctx = push_coq_ctx_local depth (Context.Rel.Declaration.LocalAssum(name,s)) coq_ctx in
      let state, t, gl2 = aux_lam coq_ctx ~depth state t in
      if lamc == c then state, EC.mkLambda (name,s,t), gl1 @ gl2
      else state, EC.mkProd (name,s,t), gl1 @ gl2
  | E.App(c,name,[s;b;t]) when letc == c ->
      let name = in_coq_fresh_annot_name ~depth ~coq_ctx depth name in
      let state, s, gl1 = aux ~depth state ~on_ty:true s in
      let state, b, gl2 = aux ~depth state b in
      let coq_ctx = push_coq_ctx_local depth (Context.Rel.Declaration.LocalDef(name,b,s)) coq_ctx in
      let state, t, gl3 = aux_lam coq_ctx ~depth state t in
      if EC.eq_constr (get_sigma state) t (EC.mkRel 1) then
        state, EC.mkCast (b,Constr.DEFAULTcast,s), gl1 @ gl2 @ gl3
      else
        state, EC.mkLetIn (name,b,s,t), gl1 @ gl2 @ gl3
      
  | E.Const n ->
                  
     if n >= 0 then
       try state, EC.mkVar(Int.Map.find n coq_ctx.db2name), []
       with Not_found ->
         try state, EC.mkRel(coq_ctx.local_len - Int.Map.find n coq_ctx.db2rel + 1), []
         with Not_found -> 
          if coq_ctx.options.failsafe then
            let hole = EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref "elpi.unknown_gref")) in
            state, hole, []
          else      
           err Pp.(hov 0 (str"Bound variable " ++ str (E.Constants.show n) ++
             str" not found in the Coq context:" ++ cut () ++
             pr_coq_ctx coq_ctx (get_sigma state) ++ cut () ++
             str"Did you forget to load some hypotheses with => ?"))
     else
        err Pp.(str"wrong constant:" ++ str (E.Constants.show n))

 (* app *)
  | E.App(c,x,[]) when appc == c -> begin
       match U.lp_list_to_list ~depth x with
       | x :: xs -> begin
          match E.look ~depth x, xs with
          | E.App(c,p,[]), i :: xs when primitivec == c ->
              let state, p, gls = primitive_value.API.Conversion.readback ~depth state p in
              begin match p with
              | Projection p ->
                  let state, i, gl1 = aux ~depth state i in
                  let state, xs, gl2 = API.Utils.map_acc (aux ~depth ~on_ty:false) state xs in
                  state, EC.mkApp (EC.mkProj (p,i),Array.of_list xs), gls @ gl1 @ gl2
              | _ ->  err Pp.(str"not a primitive projection:" ++ str (E.Constants.show c))
              end
          | x, _ ->
              let state, x, gl1 = aux ~depth state (E.kool x) in
              let state, xs, gl2 = API.Utils.map_acc (aux ~depth ~on_ty:false) state xs in
              state, EC.mkApp (x, Array.of_list xs), gl1 @ gl2
          end
       | _ -> assert false (* TODO *)
       end
  
  (* match *)
  | E.App(c,t,[rt;bs]) when matchc == c ->
      let state, t, gl1 = aux ~depth state t in
      let state, rt, gl2 = aux ~depth state rt in
      let state, bt, gl3 =
        API.Utils.map_acc (aux ~depth ~on_ty:false) state (U.lp_list_to_list ~depth bs) in
      let ind =
        (* XXX fixme reduction *)
        let { sigma } = S.get engine state in
        let rec aux t o = match EC.kind sigma t with
          | C.Lambda(n,s,t) -> aux t (`SomeTerm (n,s))
          | _ -> match o with
            | `None ->
                if List.length bt = 1 then `None
                else CErrors.anomaly Pp.(str "match on unknown, non singleton, inductive")
            | `SomeTerm (n,t) as x ->
               match safe_destApp sigma t with
               | C.Ind i, _ -> `SomeInd (fst i)
               | _ ->
                if List.length bt = 1 then x
                else CErrors.anomaly Pp.(str "match on unknown, non singleton, inductive")
        in
          aux rt `None in
      let default_case_info () =
        let unknown_ind_cinfo = Inductiveops.make_case_info (get_global_env state)
            begin match Coqlib.lib_ref "elpi.unknown_inductive" with
            | GlobRef.IndRef i -> i
            | _ -> assert false end
            Sorts.Relevant C.LetStyle in
        let b = List.hd bt in
        let l, _ = EC.decompose_lam (get_sigma state) b in
        let ci_pp_info = { unknown_ind_cinfo.Constr.ci_pp_info with Constr.cstr_tags =
          [| List.map (fun _ -> false) l |] } in
        { unknown_ind_cinfo with Constr.ci_pp_info} in
      let { sigma } = S.get engine state in
      begin match ind with
      | `SomeInd ind ->
          let ci = Inductiveops.make_case_info (get_global_env state) ind Sorts.Relevant C.RegularStyle in
          state, EC.mkCase (EConstr.contract_case (get_global_env state) sigma (ci,rt,C.NoInvert,t,Array.of_list bt)), gl1 @ gl2 @ gl3
      | `None -> CErrors.anomaly Pp.(str "non dependent match on unknown, non singleton, inductive")
      | `SomeTerm (n,rt) ->
          let ci = default_case_info () in
          let b =
            match bt with
            | [t] -> [||], t
            | _ -> assert false in
          state, EConstr.mkCase (ci,EConstr.EInstance.empty,[||],([|n|],rt),Constr.NoInvert,t,[|b|]), gl1 @ gl2 @ gl3
      end

 (* fix *)
  | E.App(c,name,[rno;ty;bo]) when fixc == c ->
      let name = in_coq_fresh_annot_name ~depth ~coq_ctx depth name in
      let state, ty, gl1 = aux ~depth state ~on_ty:true ty in
      let coq_ctx = push_coq_ctx_local depth (Context.Rel.Declaration.LocalAssum(name,ty)) coq_ctx in
      let state, bo, gl2 = aux_lam coq_ctx ~depth state bo in
      let rno =
        match E.look ~depth rno with
        | E.CData n when CD.is_int n -> CD.to_int n
        | _ -> err Pp.(str"Not an int: " ++ str (P.Debug.show_term rno)) in
      state, EC.mkFix (([|rno|],0),([|name|],[|ty|],[|bo|])), gl1 @ gl2

  | E.App(c,v,[]) when primitivec == c ->
      let state, v, gls = primitive_value.API.Conversion.readback ~depth state v in
      begin match v with
      | Uint63 i -> state, EC.mkInt i, gls
      | Float64 f -> state, EC.mkFloat f, gls
      | Projection p -> state, EC.mkConst (Names.Projection.constant p), gls
      end

  (* evar *)
  | E.UnifVar (elpi_evk,args) as x ->
      debug Pp.(fun () ->
        str"lp2term: evar: " ++
        str (pp2string (P.term depth) (E.kool x)) ++ spc () ++ str (UVMap.show state));
      if coq_ctx.options.hoas_holes = Some Implicit then
        (* If we don't apply the hole to the whole context Detyping will prune
           (in the binder name) variables that don't occur, and then Pretyping
           does not put the variables back in scope *)
        let hole = EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref "elpi.hole")) in
        let all_ctx = CArray.init coq_ctx.local_len (fun x -> EConstr.mkRel (x+1)) in
        (* We put another hole at the end to know how many arguments we added here *)
        let all_ctx = Array.append all_ctx [|hole|] in
        state, EConstr.mkApp(hole, all_ctx), []
      else
      begin try
        let ext_key = UVMap.host elpi_evk state in

        debug Pp.(fun () -> str"lp2term: evar: already in Coq: " ++ Evar.print ext_key);

        let state, args, gl1 = API.Utils.map_acc (aux ~depth ~on_ty:false) state args in
        let args = List.rev args in
        let section_args =
          CList.rev_map EC.mkVar (section_ids (get_global_env state)) in
        let arity = evar_arity ext_key state in
        let ev =
          let all_args = args @ section_args in
          let nargs = List.length all_args in
          if nargs > arity then
            let args1, args2 = CList.chop (nargs - arity) all_args in
            EC.mkApp(EC.mkEvar (ext_key, args2),
                       CArray.rev_of_list args1)
          else
            EC.mkEvar (ext_key, all_args) in

        state, ev, gl1
      with Not_found -> try
        let canonical_context, elpi_revkc, elpi_evkc, ty, relevant_constraint =
          find_evar_decl elpi_evk (E.constraints syntactic_constraints) in
        let state, k, gl1 =
          declare_evar_of_constraint ~calldepth elpi_revkc elpi_evkc syntactic_constraints canonical_context ty state coq_ctx.options in

        debug Pp.(fun () -> str"lp2term: evar: declared new: " ++
          Evar.print k ++ str" = " ++ str(F.Elpi.show elpi_evk));

        if List.length args <> Int.Map.cardinal canonical_context then
          CErrors.anomaly Pp.(str"Mismatch between canonical context and instance." ++ fnl () ++
            str"Instance:" ++ fnl () ++
            str (pp2string (P.term depth) t) ++ fnl () ++
            str"Canonical context:" ++ fnl () ++
            str(pp2string pp_cst relevant_constraint));
        let state, x, gls = aux ~depth state t in
        state, x, gl1 @ gls
      with Not_found ->

        debug Pp.(fun () -> str"lp2term: evar: unknown");

        match analyze_scope ~depth coq_ctx args with
        | `GoodToGo args_in_coq_ctx ->
           create_evar_unknown ~calldepth syntactic_constraints
             coq_ctx ~args_in_coq_ctx ~depth state elpi_evk ~on_ty (E.kool x)
        | `NeedsRestriction (is_deterministic, keep_mask)
          when is_deterministic || coq_ctx.options.hoas_holes = Some Heuristic ->

          debug Pp.(fun () -> str"evar: unknown: needs restriction ");

          let state, new_uv = F.Elpi.make state in
          let ass =
            let rec mk_restriction d acc = function
              | [] -> E.mkUnifVar new_uv ~args:(List.rev acc) state
              | true :: mask -> E.mkLam (mk_restriction (d+1) (E.mkBound d :: acc) mask)
              | false :: mask -> E.mkLam (mk_restriction (d+1) acc mask) in
            mk_restriction calldepth [] keep_mask in
          let restriction_assignment =
            E.mkApp E.Constants.eqc (E.mkUnifVar elpi_evk ~args:[] state) [ass] in

          debug Pp.(fun () ->
              str"evar: unknown: restriction assignment: "
              ++ str (pp2string (P.term calldepth) restriction_assignment));

          let args =
            CList.map_filter (fun (b,a) -> if b then Some a else None) (List.combine keep_mask args) in
          let state, t, gls = aux ~depth state (E.mkUnifVar new_uv ~args state) in
          state, t, restriction_assignment :: gls

        | `NeedsRestriction _ ->
           err Pp.(str "Flexible term outside pattern fragment:"++cut ()++str (pp2string (P.term depth) @@ E.kool x))
    end

  (* errors *)
  | E.Lam _ ->
       err Pp.(str "out of place lambda: "++
               str (pp2string P.(term depth) t))
  | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Debug.show_term t))

(* Evar info out of thin air: the user wrote an X that was never encountered by
   type checking (of) hence we craft a tower ?1 : ?2 : Type and link X with ?1 *)
and create_evar_unknown ~calldepth syntactic_constraints (coq_ctx : 'a coq_context) ~args_in_coq_ctx ~depth ~on_ty state elpi_evk orig =
  debug Pp.(fun () ->
      str"lp2term: evar: create_unknown: whole ctx:" ++
      Printer.pr_named_context_of coq_ctx.env (get_sigma state) ++ str" ; "++
      Printer.pr_rel_context_of coq_ctx.env (get_sigma state) );
  debug Pp.(fun () ->
      str"lp2term: evar: create_unknown: visible ctx:" ++
      str (pp2string (P.list (P.term depth) " ") (List.map E.mkBound args_in_coq_ctx)));

  let env = (restrict_coq_context args_in_coq_ctx state coq_ctx).env in

  debug Pp.(fun () ->
      str"lp2term: evar: create_unknown: restricted ctx:" ++
      Printer.pr_named_context_of coq_ctx.env (get_sigma state) ++
      Printer.pr_rel_context_of env (get_sigma state));

  let state, (k, kty) = S.update_return engine state (fun ({ sigma } as e) ->
    let sigma, (ty, _) = Evarutil.new_type_evar ~naming:(Namegen.IntroFresh (Names.Id.of_string "e")) env sigma Evd.univ_rigid in
    if on_ty then
      { e with sigma }, (fst (EConstr.destEvar sigma ty), None)
    else
      let sigma, t = Evarutil.new_evar~typeclass_candidate:false ~naming:(Namegen.IntroFresh (Names.Id.of_string "e")) env sigma ty in
      { e with sigma }, (fst (EConstr.destEvar sigma t), Some (fst (EConstr.destEvar sigma ty)))) in
  (*let state = S.update UVMap.uvmap state (UVMap.add elpi_evk k) in*)
  let state, gls_kty =
    match kty with
    | None -> state, []
    | Some k ->
        let state, _,_, gls = in_elpi_evar ~calldepth k state in
        state, gls in
  let state, gls_k = in_elpi_fresh_evar ~calldepth k ~raw_ev:elpi_evk elpi_evk state in
  debug Pp.(fun () ->
    str"lp2term: evar: create_unknown: new link: ? |> " ++
      Printer.pr_named_context_of env (get_sigma state) ++ str" |- ? = " ++ Evar.print k ++ cut() ++
      str(show_coq_engine @@ S.get engine state));
  let state, x, gls_orig = lp2constr ~calldepth syntactic_constraints coq_ctx ~depth state ~on_ty orig in
  state, x, gls_kty @ gls_k @ gls_orig

(* Evar info read back from a constraint (contains the context and the type) *)
and declare_evar_of_constraint ~calldepth elpi_revkc elpi_evkc syntactic_constraints ctx (depth_concl,concl) state options =
  let state, coq_ctx, gl1 =
    of_elpi_ctx ~calldepth syntactic_constraints depth_concl ctx state (mk_coq_context ~options state) in
  let state, ty, gl2 = lp2constr ~calldepth syntactic_constraints coq_ctx ~depth:depth_concl state concl in
  let state, k = S.update_return engine state (fun ({ sigma } as e) ->
    let sigma, t = Evarutil.new_evar~typeclass_candidate:false ~naming:(Namegen.IntroFresh (Names.Id.of_string "elpi_evar")) coq_ctx.env sigma ty in
    { e with sigma }, fst (EConstr.destEvar sigma t)) in
  let state = UVMap.add k elpi_revkc elpi_evkc state in
  debug Pp.(fun () ->
    str"lp2term: evar: new from constraint: " ++ int depth_concl ++ str" |> " ++
      pp_coq_ctx coq_ctx state ++ str" |- " ++
      str(pp2string (P.term depth_concl) concl) ++
      str " = " ++ Evar.print k ++ spc () ++ str (UVMap.show state));
  state, k, gl1 @ gl2
;;

let lp2constr syntactic_constraints coq_ctx ~depth state t =
  debug Pp.(fun () ->
      str"lp2term: depth=" ++ int depth ++
      str " ctx=[" ++ pp_coq_ctx coq_ctx state ++ str"]" ++
      str " term=" ++ str (pp2string (P.term depth) t));
  let state, t, gls = lp2constr ~calldepth:depth syntactic_constraints coq_ctx ~depth state t in
  debug Pp.(fun () ->
      str"lp2term: out=" ++
      (Printer.pr_econstr_env (get_global_env state) (get_sigma state) t) ++
      spc () ++ str "elpi2coq:" ++ cut () ++ str(UVMap.show state) ++ Termops.pr_evar_map None (Global.env()) (get_sigma state));
  state, t, gls

(* ********************************* }}} ********************************** *)

let push_env state name =
  let open Context.Rel.Declaration in
  S.update engine state (fun ({ global_env } as x) ->
     { x with global_env = Environ.push_rel (LocalAssum(Context.make_annot name Sorts.Relevant,C.mkProp)) global_env })
let pop_env state =
  S.update engine state (fun ({ global_env } as x) ->
     { x with global_env = Environ.pop_rel_context 1 global_env })

let set_sigma state sigma = S.update engine state (fun x -> { x with sigma })

(* We reset the evar map since it depends on the env in which it was created *)
let grab_global_env state =
  let env = Global.env () in
  if env == get_global_env state then state
  else
    let state = S.set engine state (CoqEngine_HOAS.from_env_keep_univ_of_sigma env (get_sigma state)) in
    let state = UVMap.empty state in
    state
let grab_global_env_drop_univs state =
  let env = Global.env () in
  if env == get_global_env state then state
  else
    let state = S.set engine state (CoqEngine_HOAS.from_env_sigma env (Evd.from_env env)) in
    let state = UVMap.empty state in
    state



let solvec = E.Constants.declare_global_symbol "solve"
let msolvec = E.Constants.declare_global_symbol "msolve"
let goalc = E.Constants.declare_global_symbol "goal"
let nablac = E.Constants.declare_global_symbol "nabla"
let sealc = E.Constants.declare_global_symbol "seal"
let openc = E.Constants.declare_global_symbol "coq.ltac.open"
let allc = E.Constants.declare_global_symbol "coq.ltac.all"

let mk_goal hyps rev ty ev args =
  E.mkApp goalc hyps [rev ;ty; ev; U.list_to_lp_list args]

let in_elpi_goal state ~args ~hyps ~raw_ev ~ty ~ev =
  mk_goal hyps raw_ev ty ev args

let sealed_goal2lp ~depth ~args ~in_elpi_arg state k =
  let calldepth = depth in
  let env = get_global_env state in
  let sigma = get_sigma state in
  let state, elpi_goal_evar, elpi_raw_goal_evar, evar_decls = in_elpi_evar ~calldepth k state in
  let evar_concl, goal_ctx, goal_env =
    info_of_evar ~env ~sigma ~section:(section_ids env) k in
  let state, g, gls =
    under_coq2elpi_ctx ~calldepth state goal_ctx
      ~mk_ctx_item:(fun _ _ _ _ _ t -> E.mkApp nablac (E.mkLam t) [])
      (fun coq_ctx hyps ~depth state ->
            let state, args, gls_args = API.Utils.map_acc (in_elpi_arg ~depth ?calldepth:(Some calldepth) coq_ctx [] sigma) state args in
            let args = List.flatten args in
            let state, hyps, raw_ev, ev, goal_ty, gls =
              in_elpi_evar_concl evar_concl ~raw_uvar:elpi_raw_goal_evar elpi_goal_evar
                coq_ctx hyps ~calldepth ~depth state in
          state, E.mkApp sealc (in_elpi_goal state ~args ~hyps ~raw_ev ~ty:goal_ty ~ev) [], gls_args @ gls) in
  state, g, evar_decls @ gls

let solvegoal2query sigma goals loc args ~in_elpi_arg ~depth:calldepth state =

  let state = S.set command_mode state false in (* tactic mode *)

  let state = S.set engine state (from_env_sigma (get_global_env state) sigma) in

  let state, gl, gls =
    API.Utils.map_acc (fun state goal ->
      if not (Evd.is_undefined sigma goal) then
        err Pp.(str (Printf.sprintf "Evar %d is not a goal" (Evar.repr goal)));

      sealed_goal2lp ~depth:calldepth ~in_elpi_arg ~args state goal) state goals in

  let state, ek = F.Elpi.make ~name:"NewGoals" state in
  let newgls = E.mkUnifVar ek ~args:[] state in

  let query =
    E.mkApp API.RawData.Constants.orc
      (E.mkApp msolvec (U.list_to_lp_list gl) [newgls])
      [E.mkApp allc (E.mkApp openc (E.mkConst solvec) []) [U.list_to_lp_list gl;newgls]] in

  let evarmap_query =
    match gls @ [query] with
    | [] -> assert false
    | [g] -> g
    | x :: xs -> E.mkApp E.Constants.andc x xs in

  state, (loc, evarmap_query)
;;

let sealed_goal2lp ~depth state goal =
  sealed_goal2lp ~depth ~args:[] ~in_elpi_arg:(fun ~depth ?calldepth _ _ _ _ _ -> assert false) state goal

let customtac2query sigma goals loc text ~depth:calldepth state =
  match goals with
  | [] | _ :: _ :: _ ->
     CErrors.user_err Pp.(str "elpi query can only be used on one goal")
  | [goal] ->
    let info = Evd.find sigma goal in
    let env = get_global_env state in
    let env = Environ.reset_with_named_context (Evd.evar_filtered_hyps info) env in
    if not (Evd.is_undefined sigma goal) then
      err Pp.(str (Printf.sprintf "Evar %d is not a goal" (Evar.repr goal)));
    let state = S.set command_mode state false in (* tactic mode *)
    let state = S.set engine state (from_env_sigma env sigma) in
    let state, elpi_goal_evar, elpi_raw_goal_evar, evar_decls = in_elpi_evar ~calldepth goal  state in
    let evar_concl, goal_ctx, goal_env =
      info_of_evar ~env ~sigma ~section:(section_ids env) goal in
    let state, query, gls =
      under_coq2elpi_ctx ~calldepth state goal_ctx
      (fun coq_ctx hyps ~depth state ->
          let state, q = API.Quotation.lp ~depth state loc text in
          state, q, []) in
    let evarmap_query =
      match evar_decls @ gls @ [query] with
      | [] -> assert false
      | [g] -> g
      | x :: xs -> E.mkApp E.Constants.andc x xs in
    debug Pp.(fun () -> str"engine: " ++ str (show_coq_engine (S.get engine state)));
    state, (loc, evarmap_query)
;;

type 'arg tactic_main = Solve of 'arg list | Custom of string

let goals2query sigma goals loc ~main ~in_elpi_arg ~depth state =
  match main with
  | Solve args -> solvegoal2query sigma goals loc args ~in_elpi_arg ~depth state
  | Custom text -> customtac2query sigma goals loc text ~depth state 

let eat_n_lambdas ~depth t upto state =
  let open E in
  let rec aux n t =
    if n = upto then t
    else match look ~depth:n t with
      | Lam t -> aux (n+1) t
      | UnifVar(r,a) -> aux (n+1) (mkUnifVar r ~args:(a@[mkConst n]) state)
      | _ -> assert false
  in
    aux depth t

let get_goal_ref ~depth syntactic_constraints state t =
  match E.look ~depth t with
  | E.App(c,ctx,[_;_;g;i]) when c == goalc ->
     begin match E.look ~depth g with
     | E.UnifVar(ev,scope) ->
       begin try
         let uv = find_evar ev syntactic_constraints in
         Some (ctx,UVMap.host uv state,scope,U.lp_list_to_list ~depth i)
       with Not_found -> None
       end
     | _ -> err Pp.(str"Not a variable after goal: " ++ str(pp2string (P.term depth) g))
     end
  | _ -> None

let rec get_sealed_goal_ref ~depth syntactic_constraints state t =
  match E.look ~depth t with
  | E.App(c,g,[]) when c == nablac ->
     begin match E.look ~depth g with
     | E.Lam g -> get_sealed_goal_ref ~depth:(depth+1) syntactic_constraints state g
     | _ -> err Pp.(str"Not a lambda after nabla: " ++ str(pp2string (P.term depth) g))
     end
  | E.App(c,g,[]) when c == sealc ->
     get_goal_ref ~depth syntactic_constraints state g
  | _ -> None

let no_list_given = function
  | E.UnifVar _ -> true
  | _ -> false

let rec skip_lams ~depth d t = match E.look ~depth t with
  | E.Lam t -> skip_lams ~depth:(depth+1) (d+1) t
  | x -> x, d

let show_engine state =
  show_coq_engine (S.get engine state) ^ "\nCoq-Elpi mapping:\n" ^
  UVMap.show state

let elpi_solution_to_coq_solution syntactic_constraints state =
  let { sigma; global_env } as e = S.get engine state in
  
  debug Pp.(fun () -> str"elpi sigma -> coq sigma: before:\n" ++ str (show_engine state));

  let state, assigned, changed, extra_gls =
    UVMap.fold (fun k _ _ elpi_solution (state, assigned, changed, extra) ->
      match elpi_solution with
      | None -> (state, assigned, changed, extra)
      | Some t ->

       (* The canonical context in which have to port the solution found by elpi *)
       let _, ctx, _ = info_of_evar ~env:global_env ~sigma ~section:(section_ids global_env) k in

       (* under_coq_ctx is tied to elpi terms, while here I need the coq_ctx to
          convert the term back, hence this spill hack *)
       let spilled_solution = ref (EConstr.mkProp) in
       let state, _, gls = under_coq2elpi_ctx ~calldepth:0 state ctx ~mk_ctx_item:(fun _ _ _ _ _ x -> x) 
         (fun coq_ctx hyps ~depth state ->
           debug Pp.(fun () ->
               str"solution for "++ Evar.print k ++ str" in ctx=" ++
               Printer.pr_named_context_of coq_ctx.env (get_sigma state) ++ str" at depth=" ++
               int depth ++ str" id term=" ++ str(pp2string (P.term 0) t));

           (* These meta-level-lambdas are elpi specific, they don't exist in Coq *)
           let t = eat_n_lambdas ~depth:0 t coq_ctx.proof_len state in
               
           let state, solution, gls = lp2constr
               syntactic_constraints coq_ctx ~depth state t in

           spilled_solution := solution;
           state, E.mkNil (* dummy *), gls)
       in
       let coq_solution = !spilled_solution in

       let state = S.update engine state (fun ({ sigma } as e) ->
         let sigma = Evd.define k coq_solution sigma in
         { e with sigma }) in

       (* since the order in which we add is not topological*)
       let assigned = Evar.Set.add k assigned in

       state, assigned, true, gls :: extra) state
     (state, Evar.Set.empty, false, [])
  in
    
  (* Drop from the mapping the evars that were assigned *)
  let state = UVMap.filter_host (fun k -> not (Evar.Set.mem k assigned)) state in

  debug Pp.(fun () -> str"elpi sigma -> coq sigma: after:\n" ++ str (show_engine state));

  state, assigned, changed, List.(concat (rev extra_gls))
  

let get_declared_goals all_goals constraints state assignments pp_ctx =
   let syntactic_constraints = E.constraints constraints in
   match API.Data.StrMap.find "NewGoals" assignments with
   | exception Not_found -> Evar.Set.elements all_goals , []
   | r ->
       let l, depth = skip_lams ~depth:0 0 (r) in
       if no_list_given l then Evar.Set.elements all_goals, []
       else
         let l = U.lp_list_to_list ~depth (E.kool l) in
         let declared = List.map (fun x ->
           match get_sealed_goal_ref ~depth syntactic_constraints state x with
           | Some (_,g,_,_) -> g
           | None -> err Pp.(str"Not a goal " ++ str(pp2string (P.term depth) x) ++ str " in " ++ cut () ++ str(pp2string (API.Pp.constraints pp_ctx) constraints))) l in
         let declared_set =
           List.fold_right Evar.Set.add declared Evar.Set.empty in
         declared,
         Evar.Set.elements @@ Evar.Set.diff all_goals declared_set
   (*i
   let sigma = (cs_get_engine state).sigma in
   (* Purge *)
   let state = cs_set_engine state (from_env_sigma env sigma) in
   declared_goals, shelved_goals
*)

let rec reachable1 sigma root acc =
  let info = Evd.find sigma root in
  let res = if Evd.evar_body info == Evd.Evar_empty then Evar.Set.add root acc else acc in
  let res = Evar.Set.union res @@ Evarutil.undefined_evars_of_evar_info sigma (Evd.find sigma root) in
  if Evar.Set.equal res acc then acc else reachable sigma res res
and reachable sigma roots acc =
  Evar.Set.fold (reachable1 sigma) roots acc

let reachable sigma roots acc =
  let res = reachable sigma roots acc in
  debug Pp.(fun () ->
      str"reachable from:" ++
      prlist_with_sep spc Evar.print (Evar.Set.elements roots) ++
      str" = " ++
      prlist_with_sep spc Evar.print (Evar.Set.elements res));
  res

let tclSOLUTION2EVD sigma0 { API.Data.constraints; assignments; state; pp_ctx } =
  let open Proofview.Unsafe in
  let open Tacticals in
  let open Proofview.Notations in
    tclGETGOALS >>= fun gls ->
    let gls = gls |> List.map Proofview.drop_state in
    let roots = List.fold_right Evar.Set.add gls Evar.Set.empty in
    let state, solved_goals, _, _gls = elpi_solution_to_coq_solution constraints state in
    let sigma = get_sigma state in
    let all_goals = reachable sigma roots Evar.Set.empty in
    let declared_goals, shelved_goals =
      get_declared_goals (Evar.Set.diff all_goals solved_goals) constraints state assignments pp_ctx in
    debug Pp.(fun () -> str "Goals: " ++ prlist_with_sep spc Evar.print declared_goals);
    debug Pp.(fun () -> str "Shelved Goals: " ++ prlist_with_sep spc Evar.print shelved_goals);
    let sigma = Evd.fold_undefined (fun k _ sigma ->
      if Evar.Set.mem k all_goals || Evd.mem sigma0 k then sigma
      else Evd.remove sigma k
      ) sigma sigma in
  tclTHENLIST [
    tclEVARS sigma;
    tclSETGOALS @@ List.map Proofview.with_empty_state declared_goals;
    Proofview.shelve_goals shelved_goals
  ]

let rm_evarc = E.Constants.declare_global_symbol "rm-evar"

let set_current_sigma ~depth state sigma =

  debug Pp.(fun () -> str"bringing updated sigma back to lp");

  let state = set_sigma state sigma in
  let state, assignments, decls, to_remove_coq, to_remove_elpi =
    UVMap.fold (fun k elpi_raw_evk elpi_evk solution (state, assignments, decls, to_remove_coq, to_remove_elpi as acc) ->
      let info = Evd.find sigma k in
      match Evd.evar_body info with
      | Evd.Evar_empty -> acc
      | Evd.Evar_defined c ->
          let ctx = Evd.evar_filtered_context info in
          let env = get_global_env state in
          let section_ids = section_ids env in
          let ctx = ctx |> List.filter (fun e -> let id = Context.Named.Declaration.get_id e in not(List.mem id section_ids)) in
          let assigned = E.mkUnifVar elpi_evk ~args:[] state in
          debug Pp.(fun () ->
              str"set_current_sigma: preparing assignment for " ++ str (pp2string (P.term depth) assigned) ++
              str" under context " ++ Printer.pr_named_context env sigma (EConstr.Unsafe.to_named_context ctx));
          let state, t, dec = under_coq2elpi_ctx ~mk_ctx_item:(fun _ _ _ _ _ -> E.mkLam) ~calldepth:depth state ctx (fun coq_ctx hyps ~depth:new_ctx_depth state ->
            constr2lp coq_ctx ~calldepth:depth ~depth:new_ctx_depth state c) in
          let assignment = E.mkAppL E.Constants.eqc [assigned; t] in
          debug Pp.(fun () ->
            str"set_current_sigma: assignment at depth" ++ int depth ++
            str" is: " ++ str (pp2string (P.term depth) assignment));
          state, assignment :: assignments, dec :: decls, k :: to_remove_coq, (elpi_raw_evk, elpi_evk, List.length ctx) :: to_remove_elpi
      ) state (state,[],[],[],[]) in
  let state = List.fold_right UVMap.remove_host to_remove_coq state in
  let removals = to_remove_elpi |> List.map (fun (rk,k,ano) ->
    let args = CList.init ano (fun x -> E.mkConst (x+depth)) in
    E.mkAppL rm_evarc [E.mkUnifVar rk ~args state; E.mkUnifVar k ~args state]) in
  state, removals @ List.concat decls @ assignments

(* elpi -> Entries.mutual_inductive_entry **************************** *)

(* documentation of the Coq API

  Coq < Inductive foo (A : Type) (a : A) : A -> Prop := K : foo A a a.

  {Entries.mind_entry_record = None; mind_entry_finite = Finite;
   mind_entry_params =
    [(a, Entries.LocalAssumEntry _UNBOUND_REL_1);
     (A, Entries.LocalAssumEntry Type@{Top.1})];
   mind_entry_inds =
    [{Entries.mind_entry_typename = foo;
      mind_entry_arity = _UNBOUND_REL_2 -> Prop; mind_entry_template = false;
      mind_entry_consnames = [K];
      mind_entry_lc =
       [_UNBOUND_REL_3 _UNBOUND_REL_2 _UNBOUND_REL_1 _UNBOUND_REL_1]}];
   mind_entry_universes = Entries.Monomorphic_ind_entry Top.1 |= ;
   mind_entry_private = None}

  Coq < Inductive bar (n m : nat) : Prop := K (_ : bar n (S m)).

  {Entries.mind_entry_record = None; mind_entry_finite = Finite;
   mind_entry_params =
    [(m, Entries.LocalAssumEntry nat); (n, Entries.LocalAssumEntry nat)];
   mind_entry_inds =
    [{Entries.mind_entry_typename = bar; mind_entry_arity = Prop;
      mind_entry_template = false; mind_entry_consnames = [K];
      mind_entry_lc =
       [_UNBOUND_REL_3 _UNBOUND_REL_2 (S _UNBOUND_REL_1) ->
        _UNBOUND_REL_4 _UNBOUND_REL_3 _UNBOUND_REL_2]}];
   mind_entry_universes = Entries.Monomorphic_ind_entry ;
   mind_entry_private = None}
*)


type record_field_att =
  | Coercion of bool
  | Canonical of bool

let record_field_att = let open API.Conversion in let open API.AlgebraicData in let open Elpi.Builtin in declare {
  ty = TyName "field-attribute";
  doc = "Attributes for a record field. Can be left unspecified, see defaults below.";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("coercion","default false",A(bool,N),
        B (fun x -> Coercion(x)),
        M (fun ~ok ~ko -> function Coercion x -> ok (x) | _ -> ko ()));
    K("canonical","default true, if field is named",A(bool,N),
        B (fun x -> Canonical(x)),
        M (fun ~ok ~ko -> function Canonical x -> ok (x) | _ -> ko ()));
  ]
} |> API.ContextualConversion.(!<)

let record_field_attributes = Elpi.Builtin.unspec (API.BuiltInData.list record_field_att)

let is_coercion_att = function
  | Elpi.Builtin.Unspec -> false
  | Elpi.Builtin.Given l ->
      let rec aux = function
      | [] -> false
      | Coercion x :: _ -> x
      | _ :: l -> aux l
      in
        aux l
let is_canonical_att = function
  | Elpi.Builtin.Unspec -> true
  | Elpi.Builtin.Given l ->
      let rec aux = function
      | [] -> true
      | Canonical x :: _ -> x
      | _ :: l -> aux l
      in
        aux l

let implicit_kind : Glob_term.binding_kind API.Conversion.t = let open API.Conversion in let open API.AlgebraicData in let open Glob_term in declare {
  ty = TyName "implicit_kind";
  doc = "Implicit status of an argument";
  pp = (fun fmt -> function
    | NonMaxImplicit -> Format.fprintf fmt "implicit"
    | Explicit -> Format.fprintf fmt "explicit"
    | MaxImplicit -> Format.fprintf fmt "maximal");
  constructors = [
    K("implicit","regular implicit argument, eg Arguments foo [x]",N,
      B NonMaxImplicit,
      M (fun ~ok ~ko -> function NonMaxImplicit -> ok | _ -> ko ()));
    K("maximal","maximally inserted implicit argument, eg Arguments foo {x}",N,
      B MaxImplicit,
      M (fun ~ok ~ko -> function MaxImplicit -> ok | _ -> ko ()));
    K("explicit","explicit argument, eg Arguments foo x",N,
      B Explicit,
      M (fun ~ok ~ko -> function Explicit -> ok | _ -> ko ()));
  ]
} |> API.ContextualConversion.(!<)

let in_coq_imp ~depth st x =
  let open Elpi.Builtin in
  match (unspec implicit_kind).API.Conversion.readback ~depth st x with
  | st, Unspec, gl  -> assert(gl = []); st, Glob_term.Explicit
  | st, Given x, gl -> assert(gl = []); st, x

let in_elpi_imp ~depth st x =
  let st, x, gl = implicit_kind.API.Conversion.embed ~depth st x in
  assert (gl = []);
  st, x

let in_elpi_explicit ~depth state =
  let _, x = in_elpi_imp ~depth state Glob_term.Explicit in
  x

let parameterc = E.Constants.declare_global_symbol "parameter"
let arityc = E.Constants.declare_global_symbol "arity"
let constructorc = E.Constants.declare_global_symbol "constructor"
let inductivec = E.Constants.declare_global_symbol "inductive"
let recordc = E.Constants.declare_global_symbol "record"
let fieldc = E.Constants.declare_global_symbol "field"
let end_recordc = E.Constants.declare_global_symbol "end-record"

let in_elpi_id = function
  | Names.Name.Name id -> CD.of_string (Names.Id.to_string id)
  | Names.Name.Anonymous -> CD.of_string "_"

let in_elpi_bool state b =
  let _, b, _ = Elpi.Builtin.bool.API.Conversion.embed ~depth:0 state b in
  b
let in_coq_bool ~depth state ~default b =
  let _, b, _ = Elpi.Builtin.(unspec bool).API.Conversion.readback ~depth state b in
  match b with
  | Elpi.Builtin.Given b -> b
  | Elpi.Builtin.Unspec -> default

let in_elpi_parameter id ~imp ty rest =
  E.mkApp parameterc (in_elpi_id id) [imp;ty;E.mkLam rest]
let in_elpi_arity t =
  E.mkApp arityc t []

let in_elpi_indtdecl_record rid arity kid rest =
  E.mkApp recordc (in_elpi_id rid) [arity;in_elpi_id kid;rest]
let in_elpi_indtdecl_endrecord () =
  E.mkConst end_recordc

let in_elpi_field atts n ty fields =
  E.mkApp fieldc atts [in_elpi_id n; ty; E.mkLam fields]

let in_elpi_indtdecl_inductive state find id arity constructors =
  match find with
  | Vernacexpr.Inductive_kw | Vernacexpr.Variant ->
      E.mkApp inductivec (in_elpi_id id) [in_elpi_bool state true; arity;E.mkLam @@ U.list_to_lp_list constructors]
  | Vernacexpr.CoInductive ->
      E.mkApp inductivec (in_elpi_id id) [in_elpi_bool state false; arity;E.mkLam @@ U.list_to_lp_list constructors]
  | Vernacexpr.Record | Vernacexpr.Structure | Vernacexpr.Class _ -> assert false
let in_elpi_indtdecl_constructor id ty =
  E.mkApp constructorc (in_elpi_id id) [ty]

type record_field_spec = { name : Name.t; is_coercion : bool; is_canonical : bool }
let in_elpi_indtdecl_field ~depth s { name; is_coercion; is_canonical } ty rest =
  let open API.Conversion in
  let s, att, gl = record_field_attributes.embed ~depth s (Elpi.Builtin.Given [Coercion is_coercion; Canonical is_canonical]) in
  assert(gl = []);
  s, E.mkApp fieldc att [in_elpi_id name;ty;E.mkLam rest]

let force_name =
  let n = ref 0 in
  function
  | Name.Name x -> x
  | _ ->
     incr n; Id.of_string (Printf.sprintf "_missing_parameter_name_%d_" !n)

let force_name_ctx =
  let open Context in
  let open Rel.Declaration in
  List.map (function
    | LocalAssum(n,t) -> LocalAssum (map_annot (fun n -> Name (force_name n)) n, t)
    | LocalDef(n,b,ty) -> LocalDef(map_annot (fun n -> Name (force_name n)) n, b, ty))
;;


let readback_arity ~depth coq_ctx constraints state t =
  let lp2constr coq_ctx ~depth state t =
    lp2constr constraints coq_ctx ~depth state t in
  let rec aux_arity coq_ctx ~depth params impls state extra t =
    match E.look ~depth t with
    | E.App(c,name,[imp;ty;decl]) when is_coq_name ~depth name && c == parameterc ->
        let name = in_coq_annot ~depth name in
        let state, imp = in_coq_imp ~depth state imp in
        let state, ty, gls = lp2constr coq_ctx ~depth state ty in
        let e = Context.Rel.Declaration.LocalAssum(name,ty) in
        aux_lam e coq_ctx ~depth (e :: params) (manual_implicit_of_binding_kind (Context.binder_name name) imp :: impls) state (gls :: extra) decl
    | E.App(c,ty,[]) when c == arityc ->
        let state, ty, gls = lp2constr coq_ctx ~depth state ty in
        state, params, impls, ty,  List.flatten @@ gls :: extra
    | _ -> err Pp.(str"arity expected, got: "++ str (pp2string P.(term depth) t))
  and aux_lam e coq_ctx ~depth params impls state extra t =
    match E.look ~depth t with
    | E.Lam t -> aux_arity (push_coq_ctx_local depth e coq_ctx) ~depth:(depth+1) params impls state extra t
    | _ -> err Pp.(str"lambda expected: "  ++
                  str (pp2string P.(term depth) t))
  in
    aux_arity coq_ctx ~depth [] [] state [] t
;;

let mk_ctx_item_parameter ~depth state impls = fun i _ name ty bo rest ->
  let impls = List.rev impls in
  if bo <> None then err Pp.(str"arities with let-in are not supported");
  let imp =
    try List.nth impls i
    with Failure _ -> in_elpi_explicit ~depth state in
  in_elpi_parameter ~imp name ty rest

let mk_ctx_item_record_field ~depth state atts = fun i _ name ty bo rest ->
  if bo <> None then err Pp.(str"record fields with let-in are not supported");
  let state, atts, gls = record_field_attributes.API.Conversion.embed ~depth state (Elpi.Builtin.Given atts.(i)) in
  in_elpi_field atts name ty rest

(* TODO: clarify the x\ is after the decl !! *)
let under_coq2elpi_relctx ~calldepth state ctx
  ?(coq_ctx = mk_coq_context ~options:default_options state)
  ?(mk_ctx_item=fun _ decl _ _ _ -> mk_pi_arrow decl)
  kont
=
  let open Context.Rel.Declaration in
  let gls = ref [] in
  let rec aux i ~depth coq_ctx hyps state = function
    | [] ->
        let state, t, gls_t = kont coq_ctx hyps ~depth state in
        gls := gls_t @ !gls;
        state, t
    | LocalAssum (Context.{binder_name=coq_name}, ty) as e :: rest ->
        let name = coq_name in
        let state, ty, gls_ty = constr2lp coq_ctx ~calldepth ~depth:(depth) state ty in
        gls := gls_ty @ !gls;
        let hyp = mk_decl ~depth name ~ty in
        let hyps = { ctx_entry = hyp ; depth = depth } :: hyps in
        let coq_ctx = push_coq_ctx_local depth e coq_ctx in
        let state, rest = aux (succ i) ~depth:(depth+1) coq_ctx hyps state rest in
        state, mk_ctx_item i hyp name ty None rest
      | LocalDef (Context.{binder_name=coq_name},bo,ty) as e :: rest ->
        let name = coq_name in
        let state, ty, gls_ty = constr2lp coq_ctx ~calldepth ~depth:(depth) state ty in
        let state, bo, gls_bo = constr2lp coq_ctx ~calldepth ~depth:(depth) state bo in
        gls := gls_ty @ gls_bo @ !gls;
        let hyp = mk_def ~depth name ~bo ~ty in
        let hyps = { ctx_entry = hyp ; depth = depth } :: hyps in
        let coq_ctx = push_coq_ctx_local depth e coq_ctx in
        let state, rest = aux (succ i) ~depth:(depth+1) coq_ctx hyps state rest in
        state, mk_ctx_item i hyp name ty (Some bo) rest
  in
    let state, t = aux 0 ~depth:calldepth coq_ctx [] state (List.rev ctx) in
    state, t, !gls

let in_elpi_imp_list ~depth state impls =
  let in_elpi_imp state x =
    let state, i = in_elpi_imp ~depth state x in
    state, i, [] in
  let state, impls, _ = API.Utils.map_acc in_elpi_imp state impls in
  state, impls

let embed_arity ~depth coq_ctx constraints state (relctx,impls,ty) =
  let calldepth = depth in
  let state, impls = in_elpi_imp_list ~depth state impls in
  under_coq2elpi_relctx ~calldepth state relctx
    ~mk_ctx_item:(mk_ctx_item_parameter ~depth state impls)
    (fun coq_ctx hyps ~depth state ->
        let state, ty, gl = constr2lp coq_ctx ~calldepth ~depth state ty in
        state, in_elpi_arity ty, gl)
;;

let lp2inductive_entry ~depth coq_ctx constraints state t =

  let lp2constr coq_ctx ~depth state t =
    lp2constr constraints coq_ctx ~depth state t in

  let open Entries in

  let check_consistency_and_drop_nuparams sigma nuparams name params arity =
    let eq_param x y =
      Name.equal
        (Context.Rel.Declaration.get_name x)
        (Context.Rel.Declaration.get_name y) &&
      EConstr.eq_constr_nounivs sigma
       (EConstr.Vars.lift 1 (Context.Rel.Declaration.get_type x))
       (Context.Rel.Declaration.get_type y) in
    let rec aux n nuparams params =
      match nuparams, params with
      | [], params -> EC.it_mkProd_or_LetIn arity (List.rev params)
      | x :: nuparams, y :: params when eq_param x y ->
          aux (succ n) nuparams params
      | x :: _, p ->  err Pp.(pr_nth n ++ str" non uniform parameter, named " ++
                              Name.print (Context.Rel.Declaration.get_name x) ++
                              str ", not found in constructor "++Id.print name)
    in aux 1 (List.rev nuparams) (List.rev params) in

  let aux_construtors coq_ctx ~depth (params,impls) (nuparams,nuimpls) arity itname finiteness state ks =

    let params = force_name_ctx params in
    let paramno = List.length params in

    (* decode constructors' types *)
    let (state, gls_rev), names_ktypes =
      CList.fold_left_map (fun (state, extra) t ->

        match E.look ~depth t with
        | E.App(c,name,[ty]) when c == constructorc ->
            begin match E.look ~depth name with
            | E.CData name when CD.is_string name ->
              let name = Id.of_string (CD.to_string name) in
              let state, params, impls, ty, gls = readback_arity ~depth coq_ctx constraints state ty in
              (state, gls :: extra), (name, ty, params, impls)
            | _ -> err Pp.(str"@gref expected: "  ++
                 str (pp2string P.(term depth) name))
            end
        | _ -> err Pp.(str"constructor expected: "  ++
                 str (pp2string P.(term depth) t)))
      (state,[]) ks in
    let knames, ktypes, kparams, kimpls = CList.split4 names_ktypes in

    let sigma = get_sigma state in

    (* Handling of non-uniform parameters *)
    let nupno = List.length nuparams in
    let ktypes = CList.map3 (check_consistency_and_drop_nuparams sigma nuparams) knames kparams ktypes in
    let kimpls = List.map (fun x -> impls @ x) kimpls in

    (* Relocation to match Coq's API.
     * From
     *  Params, Ind, NuParams |- ktys
     * To
     *  Ind, Params, NuParams |- ktys
     *)
    let ktypes = ktypes |> List.map (fun t ->
      let subst = CList.init (nupno + paramno + 1) (fun i ->
        if i < nupno then EC.mkRel (i+1)
        else if i = nupno then
          let ind = EC.mkRel (nupno + paramno + 1) in
          if paramno = 0 then ind
          else
            let ps =
              CArray.init paramno (fun i -> EC.mkRel (nupno + paramno - i)) in
            EC.mkApp (ind,ps)
        else EC.mkRel i) in
      EC.Vars.substl subst t
    ) in

    let params = nuparams @ params in
    let i_impls = impls @ nuimpls in

    debug Pp.(fun () ->
        str"Inductive declaration with sigma:" ++ cut() ++
        Termops.pr_evar_map None (Global.env()) sigma);
    let state = minimize_universes state in
    let sigma = get_sigma state in
    let ktypes = List.map (EC.to_constr sigma) ktypes in
    let open Context.Rel.Declaration in
    let params = List.map (function
      | LocalAssum (x, t) -> LocalAssum(x, EC.to_constr sigma t)
      | LocalDef (x, t, b) -> LocalDef(x, EC.to_constr sigma t, EC.to_constr sigma b))
      params in
    let arity = EC.to_constr sigma arity in
    let used =
      List.fold_left (fun acc t ->
          Univ.LSet.union acc
            (EConstr.universes_of_constr sigma (EConstr.of_constr t)))
        (EConstr.universes_of_constr sigma (EConstr.of_constr arity)) ktypes in
    let used =
      List.fold_left (fun acc -> function
        | (LocalDef(_,t,b)) ->
          Univ.LSet.union acc
           (Univ.LSet.union
            (EConstr.universes_of_constr sigma (EConstr.of_constr t))
            (EConstr.universes_of_constr sigma (EConstr.of_constr b)))
        | (LocalAssum(_,t)) ->
          Univ.LSet.union acc
            (EConstr.universes_of_constr sigma (EConstr.of_constr t)))
        used params in
    let sigma = Evd.restrict_universe_context sigma used in
    debug Pp.(fun () ->
        str"Inductive declaration with restricted sigma:" ++ cut() ++
        Termops.pr_evar_map None (Global.env()) sigma);
    let oe = {
      mind_entry_typename = itname;
      mind_entry_arity = arity;
      mind_entry_consnames = knames;
      mind_entry_lc = ktypes;
    } in
    state, {
      mind_entry_record =
        if finiteness = Declarations.BiFinite then
          if coq_ctx.options.primitive = Some true then Some (Some [|Names.Id.of_string "record"|]) (* primitive record *)
          else Some None (* regular record *)
        else None; (* not a record *)
      mind_entry_finite = finiteness;
      mind_entry_params = params;
      mind_entry_inds = [oe];
      mind_entry_universes = Monomorphic_ind_entry;
      mind_entry_variance = None;
      mind_entry_private = None; }, Evd.universe_context_set sigma, i_impls, kimpls, List.(concat (rev gls_rev))
  in

  let rec aux_fields depth state ind fields =
    match E.look ~depth fields with
    | E.App(c,atts,[n; ty; fields]) when c == fieldc ->
      begin match E.look ~depth fields with
      | E.Lam fields ->
        let state, fs, tf = aux_fields (depth+1) state ind fields in
        let name = in_coq_name ~depth n in
        let state, atts, gls = record_field_attributes.API.Conversion.readback ~depth state atts in
        assert(gls = []);
        state, { name; is_coercion = is_coercion_att atts; is_canonical = is_canonical_att atts } :: fs,
          in_elpi_prod name ty tf
      | _ -> err Pp.(str"field/end-record expected: "++
                   str (pp2string P.(term depth) fields))
      end
    | E.Const c when c == end_recordc -> state, [], ind
    | _ ->  err Pp.(str"field/end-record expected: "++ 
                 str (pp2string P.(term depth) fields))
  in


  let rec aux_decl coq_ctx ~depth params impls state extra t =

    match E.look ~depth t with
    | E.App(c,name,[imp;ty;decl]) when is_coq_name ~depth name && c == parameterc ->
        let name = in_coq_annot ~depth name in
        let state, imp = in_coq_imp ~depth state imp in
        let state, ty, gls = lp2constr coq_ctx ~depth state ty in
        let e = Context.Rel.Declaration.LocalAssum(name,ty) in
        aux_lam e coq_ctx ~depth (e :: params) (manual_implicit_of_binding_kind (Context.binder_name name) imp :: impls) state (gls :: extra) decl
    | E.App(c,id,[fin;arity;ks])
      when c == inductivec ->
        let name = in_coq_annot ~depth id in
        if Name.is_anonymous (Context.binder_name name) then
          err Pp.(str"id expected, got: "++ str (pp2string P.(term depth) id));
        let fin = if in_coq_bool ~depth state ~default:true fin then Declarations.Finite else Declarations.CoFinite in
        let state, nuparams, nuimpls, arity, gl1 = readback_arity ~depth coq_ctx constraints state arity in
        let e = Context.Rel.Declaration.LocalAssum(name,arity) in
        let iname =
          match Context.binder_name name with Name x -> x | _ -> assert false in
        begin match E.look ~depth ks with
        | E.Lam t ->
            let ks = U.lp_list_to_list ~depth:(depth+1) t in
            let state, idecl, ctx, i_impls, ks_impls, gl2 =
              aux_construtors (push_coq_ctx_local depth e coq_ctx) ~depth:(depth+1) (params,List.rev impls) (nuparams, List.rev nuimpls) arity iname fin
                state ks in
            state, (idecl, ctx, None, [i_impls, ks_impls]), List.(concat (rev (gl2 :: gl1 :: extra)))
        | _ -> err Pp.(str"lambda expected: "  ++
                 str (pp2string P.(term depth) ks))
        end
    | E.App(c,id,[arity;kn;fields]) when c == recordc ->
      begin match E.look ~depth kn with
      | E.CData kname when CD.is_string kname ->

        let state, arity, gl1 = lp2constr coq_ctx ~depth state arity in

        let name = in_coq_annot ~depth id in
        if Name.is_anonymous (Context.binder_name name) then
          err Pp.(str"id expected, got: "++ str (pp2string P.(term depth) id));
        let e = Context.Rel.Declaration.LocalAssum(name,arity) in
        let iname =
          match Context.binder_name name with Name x -> x | _ -> assert false in
        let fields = U.move ~from:depth ~to_:(depth+1) fields in
        (* We simulate the missing binders for the inductive *)
        let ind = E.mkConst depth in
        let state, fields_names_coercions, kty = aux_fields (depth+1) state ind fields in
        let k = [E.mkApp constructorc kn [in_elpi_arity kty]] in
        let state, idecl, ctx, i_impls, ks_impls, gl2 =
          aux_construtors (push_coq_ctx_local depth e coq_ctx) ~depth:(depth+1) (params,impls) ([],[]) arity iname Declarations.BiFinite
            state k in
        let primitive = coq_ctx.options.primitive = Some true in
        state, (idecl, ctx, Some (primitive,fields_names_coercions), [i_impls, ks_impls]), List.(concat (rev (gl2 :: gl1 :: extra)))
      | _ -> err Pp.(str"id expected, got: "++
                 str (pp2string P.(term depth) kn))
      end
    | _ -> err Pp.(str"(co)inductive/record expected: "++
                 str (pp2string P.(term depth) t))
  and aux_lam e coq_ctx ~depth params impls state extra t =
    match E.look ~depth t with
    | E.Lam t -> aux_decl (push_coq_ctx_local depth e coq_ctx) ~depth:(depth+1) params impls state extra t
    | _ -> err Pp.(str"lambda expected: "  ++
                 str (pp2string P.(term depth) t))
  in
  aux_decl coq_ctx ~depth [] [] state [] t

let inductive_kind_of_recursivity_kind = function
  | Declarations.Finite -> Vernacexpr.Inductive_kw
  | Declarations.CoFinite -> Vernacexpr.CoInductive
  | Declarations.BiFinite -> Vernacexpr.Inductive_kw

let safe_chop n l =
  let rec aux n acc l =
    if n = 0 then List.rev acc, l
    else
      match l with
      | [] -> List.rev acc, []
      | x :: xs -> aux (n-1) (x :: acc) xs
  in
    aux n [] l

let inductive_decl2lp ~depth coq_ctx constraints state (mutind,(mind,ind),(i_impls,k_impls)) =
  let calldepth = depth in
  let allparams = List.map EConstr.of_rel_decl mind.Declarations.mind_params_ctxt in
  let kind = inductive_kind_of_recursivity_kind mind.Declarations.mind_finite in
  let name = Name ind.Declarations.mind_typename in
  let paramsno = mind.Declarations.mind_nparams_rec in
  let allparamsno = mind.Declarations.mind_nparams in

  let i_impls_params, i_impls_nuparams = safe_chop paramsno i_impls in
  let state, i_impls_params = in_elpi_imp_list ~depth state i_impls_params in
  let nuparams, params = CList.chop (mind.Declarations.mind_nparams - paramsno) allparams in
  let nuparamsno = List.length nuparams in
  let sigma = get_sigma state in
  let drop_nparams_from_ctx n ctx =
    let ctx, _ = CList.chop (List.length ctx - n) ctx in
    ctx in
  let drop_upto_nparams_from_ctx n ctx =
    let ctx, _ = safe_chop (List.length ctx - n) ctx in
    ctx in
  let drop_nparams_from_term n x =
    let x = EConstr.of_constr x in
    let ctx, sort = EConstr.decompose_prod_assum sigma x in
    let ctx = drop_nparams_from_ctx n ctx in
    EConstr.it_mkProd_or_LetIn sort ctx in
  let move_allbutnparams_from_ctx_to n ctx t =
    let inline, keep = CList.chop (List.length ctx - n) ctx in
    keep, EConstr.it_mkProd_or_LetIn t inline in
  let k_impls = List.map (drop_upto_nparams_from_ctx paramsno) k_impls in
  let arity =
     drop_nparams_from_term allparamsno
       (Inductive.type_of_inductive ((mind,ind),Univ.Instance.empty)) in
  let knames = CArray.map_to_list (fun x -> Name x) ind.Declarations.mind_consnames in
  let ntyps = mind.Declarations.mind_ntypes in
  let ktys = CArray.map_to_list (fun (ctx,x) ->
    let (ctx,x) =
      Term.it_mkProd_or_LetIn x ctx |>
      Inductive.abstract_constructor_type_relatively_to_inductive_types_context ntyps mutind |>
      Term.decompose_prod_assum in
    let ctx = drop_nparams_from_ctx paramsno @@ List.map EConstr.of_rel_decl ctx in
    move_allbutnparams_from_ctx_to nuparamsno ctx @@ EConstr.of_constr x) ind.Declarations.mind_nf_lc in
  (* Relocation to match Coq's API.
    * From
    *  Ind, Params, NuParams |- ktys
    * To
    *  Params, Ind, NuParams |- ktys
    *)
  let rec iter n acc f =
    if n = 0 then acc
    else iter (n-1) (f acc) f in
  let subst = CList.init (allparamsno + 1) (fun i ->
    let i = i + 1 in (* init is 0 based, rels are 1 base *)
    if i = allparamsno + 1 then
      let ind = EC.mkRel (nuparamsno + 1) in
      iter paramsno ind (fun x -> EConstr.mkLambda (Context.anonR,EConstr.mkProp,EConstr.Vars.lift 1 x))
    else if i > nuparamsno then EC.mkRel(i+1)
    else EC.mkRel i) in
  let reloc t = Reductionops.nf_beta (Global.env()) sigma @@ EC.Vars.substl subst t in
under_coq2elpi_relctx ~calldepth state params
    ~mk_ctx_item:(mk_ctx_item_parameter ~depth state i_impls_params)
   (fun coq_ctx hyps ~depth state ->
      if mind.Declarations.mind_record = Declarations.NotRecord then
        let state, arity, gls1 =
          embed_arity ~depth coq_ctx constraints state (nuparams,i_impls_nuparams,arity) in
        let coq_ctx = push_coq_ctx_local depth (Context.Rel.Declaration.LocalAssum(Context.anonR,EConstr.mkProp)) coq_ctx in
        let depth = depth+1 in
        let embed_constructor state (kname,(kctx,kty),kimpl) =
          let state, karity, gl =
            embed_arity ~depth coq_ctx constraints state (kctx,kimpl,reloc kty) in
          state, in_elpi_indtdecl_constructor kname karity, gl in
        let state, ks, gls2 =
          API.Utils.map_acc embed_constructor state (CList.combine3 knames ktys k_impls) in
        state, in_elpi_indtdecl_inductive state kind name arity ks, List.flatten [gls1 ; gls2]
      else
        let kid, kty, kimpl =
          match knames, ktys, k_impls  with
          | [id], [ty], [impl] -> id, ty, impl
          | _ -> assert false in
        let embed_record_constructor state (ctx,kty) kimpl =
          let more_ctx, _ = EConstr.decompose_prod_assum sigma kty in
          let ty_as_ctx = more_ctx @ ctx in
          let atts = Array.make (List.length ty_as_ctx) [] in
          under_coq2elpi_relctx ~calldepth:depth state ty_as_ctx
            ~coq_ctx
            ~mk_ctx_item:(mk_ctx_item_record_field ~depth state atts)
              (fun coq_ctx hyps ~depth state -> state, in_elpi_indtdecl_endrecord (), [])
        in
        let state, sort, gls1 = constr2lp coq_ctx ~calldepth ~depth state arity in
        let state, rd, gls2 = embed_record_constructor state kty kimpl in
        state, in_elpi_indtdecl_record name sort kid rd, gls1 @ gls2
      )
;;
(* ********************************* }}} ********************************** *)
(* ****************************** API ********************************** *)

let get_current_env_sigma ~depth hyps constraints state =
(* TODO: cahe longer env in coq_engine for later reuse, use == on hyps+depth? *)
  let state, _, changed, gl1 = elpi_solution_to_coq_solution constraints state in
  let state, coq_ctx, gl2 =
    of_elpi_ctx ~calldepth:depth constraints depth (preprocess_context (fun _ -> true) (E.of_hyps hyps)) state (mk_coq_context ~options:(get_options ~depth hyps state) state) in
  state, coq_ctx, get_sigma state, gl1 @ gl2
;;
let get_global_env_current_sigma ~depth hyps constraints state =
  let state, _, changed, gls = elpi_solution_to_coq_solution constraints state in
  let coq_ctx = mk_coq_context ~options:(get_options ~depth hyps state) state in
  let coq_ctx = { coq_ctx with env = Environ.push_context_set (Evd.universe_context_set (get_sigma state)) coq_ctx.env } in
  state, coq_ctx, get_sigma state, gls
;;

let lp2goal ~depth hyps syntactic_constraints state t =
  match get_goal_ref ~depth (E.constraints syntactic_constraints) state t with
  | None -> assert false
  | Some (ctx,k,scope,args) ->
    let state, _, changed, gl1 =
      elpi_solution_to_coq_solution syntactic_constraints state in
    let visible_set = dblset_of_canonical_ctx ~depth Int.Set.empty scope in
    let state, coq_ctx, gl2 =
      of_elpi_ctx ~calldepth:depth syntactic_constraints depth
        (preprocess_context (fun x -> Int.Set.mem x visible_set)
          (U.lp_list_to_list ~depth ctx |> List.map (fun hsrc -> { E.hdepth = depth; E.hsrc })))
        state
        (mk_coq_context ~options:(get_options ~depth hyps state) state) in
    state, coq_ctx, k, args, gl1@gl2

let constr2lp ~depth ?(calldepth=depth) coq_ctx _constraints state t =
  constr2lp coq_ctx ~calldepth ~depth state t

let lp2constr ~depth coq_ctx constraints state t =
  lp2constr constraints coq_ctx ~depth state t

let lp2constr_closed = lp2constr

let constr2lp_closed = constr2lp

let lp2constr_closed_ground ~depth ctx csts state t =
  let state, t1, _ as res = lp2constr ~depth ctx csts state t in
  if not (Evarutil.is_ground_term (get_sigma state) t1) then
    raise API.Conversion.(TypeErr(TyName"closed_term",depth,t));
  res

let constr2lp_closed_ground ~depth ?calldepth ctx csts state t =
  assert (Evarutil.is_ground_term (get_sigma state) t);
  constr2lp ~depth ?calldepth ctx csts state t

let lp2skeleton ~depth coq_ctx constraints state t =
  let coq_ctx = { coq_ctx with options = { coq_ctx.options with hoas_holes = Some Implicit }} in
  let state, t, gls = lp2constr coq_ctx constraints ~depth state t in
  let sigma = get_sigma state in
  let gt = Detyping.detype Detyping.Now false Id.Set.empty coq_ctx.env sigma t in
  let gt =
    let is_GRef_hole x =
      match DAst.get x with
      | Glob_term.GRef(r,None) -> Names.GlobRef.equal r (Coqlib.lib_ref "elpi.hole")
      | _ -> false in
    let rec map x = match DAst.get x with
      | Glob_term.GEvar _ -> mkGHole
      | Glob_term.GApp(hd,args) when is_GRef_hole hd ->
          let _, marker_real_args = CList.split_when is_GRef_hole args in
          let real_args = List.tl marker_real_args in
          if real_args = [] then mkGHole
          else DAst.make @@ Glob_term.GApp(mkGHole,List.map (Glob_ops.map_glob_constr map) real_args)
      | _ when is_GRef_hole x -> mkGHole
      | _ -> Glob_ops.map_glob_constr map x in
    map gt in
  state, gt, gls

(* {{{  Declarations.module_body -> elpi ********************************** *)

let rec in_elpi_module_item ~depth path state (name, item) = match item with
  | Declarations.SFBconst _ ->
      [GlobRef.ConstRef (Constant.make2 path name)]
  | Declarations.SFBmind { Declarations.mind_packets = [| _ |] } ->
      [GlobRef.IndRef (MutInd.make2 path name, 0)]
  | Declarations.SFBmind _ -> nYI "HOAS SFBmind"
  | Declarations.SFBmodule mb -> in_elpi_module ~depth state mb
  | Declarations.SFBmodtype _ -> []

and in_elpi_module : 'a. depth:int -> API.Data.state -> 'a Declarations.generic_module_body -> GlobRef.t list =
  fun ~depth state { Declarations.
  mod_mp;             (* Names.module_path *)
  mod_expr;           (* Declarations.module_implementation *)
  mod_type;           (* Declarations.module_signature *)
  mod_type_alg;       (* Declarations.module_expression option *)
  mod_delta;          (* Mod_subst.delta_resolver *)
  mod_retroknowledge; (* Retroknowledge.action list *)
} ->
  match mod_type with
  | Declarations.MoreFunctor _ -> nYI "functors"
  | Declarations.NoFunctor contents ->
      let l =
        CList.map (in_elpi_module_item ~depth mod_mp state) contents in
      CList.flatten l

let rec in_elpi_modty_item (name, item) = match item with
  | Declarations.SFBconst _ ->
      [ Label.to_string name ]
  | Declarations.SFBmind { Declarations.mind_packets = [| _ |] } ->
      [ Label.to_string name ]
  | Declarations.SFBmind _ -> nYI "HOAS SFBmind"
  | Declarations.SFBmodule mb -> in_elpi_modty mb
  | Declarations.SFBmodtype _ -> []

and in_elpi_modty : 'a.'a Declarations.generic_module_body -> string list =
  fun { Declarations.mod_type; (* Declarations.modty_signature *) } ->
  match mod_type with
  | Declarations.MoreFunctor _ -> nYI "functors"
  | Declarations.NoFunctor contents ->
      CList.flatten (CList.map in_elpi_modty_item contents)

let in_elpi_module ~depth s (x : Declarations.module_body) = in_elpi_module ~depth s x

let in_elpi_module_type (x : Declarations.module_type_body) = in_elpi_modty x

(* ********************************* }}} ********************************** *)

let command_mode = S.get command_mode


(* vim:set foldmethod=marker: *)
