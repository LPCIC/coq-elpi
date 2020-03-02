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

let debug () = !Flags.debug

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
      Format.fprintf fmt "`%s`" (Pp.string_of_ppcmds (Name.print x)));
    compare = (fun _ _ -> 0);
    hash = (fun _ -> 0);
    hconsed = false;
    constants = [];
  } in
  cin, isc, cout, name
;;
let in_elpi_name x = E.mkCData (namein x)

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
type coq_context = {
  section : Names.Id.t list;
  section_len : int;
  proof : EConstr.named_context;
  proof_len : int;
  local : EConstr.rel_context;
  local_len : int;
  env : Environ.env;
  db2name : Names.Id.t Int.Map.t;
  name2db : int Names.Id.Map.t;
  db2rel : int Int.Map.t;
  names : Id.Set.t;
}

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

let in_coq_fresh_name =
  let mk_fresh dbl =
    Id.of_string_soft
      (Printf.sprintf "_elpi_ctx_entry_%d_" dbl) in
fun ~depth dbl name ~coq_ctx:{names}->
  match in_coq_name ~depth name with
  | Name.Anonymous -> mk_fresh dbl
  | Name.Name id when Id.Set.mem id names -> mk_fresh dbl
  | Name.Name id -> id

let in_coq_annot ~depth t = Context.make_annot (in_coq_name ~depth t) Sorts.Relevant

let in_coq_fresh_annot ~depth ~coq_ctx dbl t =
  Context.make_annot (in_coq_fresh_name ~depth ~coq_ctx dbl t) Sorts.Relevant

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

(* constants *)

type global_constant = Variable of Names.Id.t  | Constant of Names.Constant.t
let hash_global_constant = function
  | Variable id -> Names.Id.hash id
  | Constant c -> Names.Constant.hash c
let compare_global_constant x y = match x,y with
  | Variable v1, Variable v2 -> Names.Id.compare v1 v2
  | Constant c1, Constant c2 -> Names.Constant.CanOrd.compare c1 c2
  | Variable _, _ -> -1
  | _ -> 1

let global_constant_of_globref = function
  | GlobRef.VarRef x -> Variable x
  | GlobRef.ConstRef x -> Constant x
  | x -> CErrors.anomaly Pp.(str"not a global constant: " ++ (Printer.pr_global x))

let constant, inductive, constructor = 
  let open API.OpaqueData in
  declare {
    name = "constant";
    doc = "Global constant name";
    pp = (fun fmt x ->
      let x = match x with
        | Variable x -> GlobRef.VarRef x
        | Constant c -> GlobRef.ConstRef c in
      Format.fprintf fmt "«%s»" (Pp.string_of_ppcmds (Printer.pr_global x)));
    compare = compare_global_constant;
    hash = hash_global_constant;
    hconsed = false;
    constants = [];
  },
  declare {
    name = "inductive";
    doc = "Inductive type name";
    pp = (fun fmt x -> Format.fprintf fmt "«%s»" (Pp.string_of_ppcmds (Printer.pr_global (GlobRef.IndRef x))));
    compare = Names.ind_ord;
    hash = Names.ind_hash;
    hconsed = false;
    constants = [];
  },
  declare {
    name = "constructor";
    doc = "Inductive constructor name";
    pp = (fun fmt x -> Format.fprintf fmt "«%s»" (Pp.string_of_ppcmds (Printer.pr_global (GlobRef.ConstructRef x))));
    compare = Names.constructor_ord;
    hash = Names.constructor_hash;
    hconsed = false;
    constants = [];
  }
;;

let gref =
  let open GlobRef in
  let open API.AlgebraicData in declare {
    ty = API.Conversion.TyName "gref";
    doc = "Global objects: inductive types, inductive constructors, definitions";
    pp = (fun fmt x ->
            Format.fprintf fmt "«%s»" (Pp.string_of_ppcmds (Printer.pr_global x)));
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
  include Names.GlobRef.Ordered
  let show x = Pp.string_of_ppcmds (Printer.pr_global x)
  let pp fmt x = Format.fprintf fmt "%s" (show x)
end
module GRMap = U.Map.Make(GROrd)
module GRSet = U.Set.Make(GROrd)

let globalc  = E.Constants.declare_global_symbol "global"

let in_elpi_gr ~depth s r =
  let s, t, gl = gref.API.Conversion.embed ~depth s r in
  assert (gl = []);
  E.mkApp globalc t []

let in_coq_gref ~depth s t =
  let s, t, gls = gref.API.Conversion.readback ~depth s t in
  assert(gls = []);
  s, t

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

let in_elpi_modpath ~ty mp = E.mkCData (if ty then mptyin mp else mpin mp)
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
    
let in_elpi_appl hd (args : E.term list) =
  if args = [] then hd
  else E.mkApp appc (U.list_to_lp_list (hd :: args)) []

let in_elpi_app hd (args : E.term array) =
  in_elpi_appl hd (Array.to_list args)

let matchc = E.Constants.declare_global_symbol "match"

let in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs =
  E.mkApp matchc t [rt; U.list_to_lp_list bs]

let fixc   = E.Constants.declare_global_symbol "fix"

let in_elpi_fix name rno ty bo =
  E.mkApp fixc (in_elpi_name name) [CD.of_int rno; ty; E.mkLam bo]

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : Evd.evar_map -> elpi *************************************** *)

let command_mode =
  S.declare ~name:"coq-elpi:command-mode"
    ~init:(fun () -> true)
    ~pp:(fun fmt b -> Format.fprintf fmt "%b" b)

module CoqEngine_HOAS : sig 

  type coq_engine  = {
   global_env : Environ.env;
   sigma : Evd.evar_map; (* includes universe constraints *)

  }

  val show_coq_engine : coq_engine -> string

  val engine : coq_engine S.component

  val empty_from_env : Environ.env -> coq_engine
  val empty_from_env_sigma : Environ.env -> Evd.evar_map -> coq_engine

end = struct

 type coq_engine = { 
   global_env : Environ.env [@printer (fun _ _ -> ())];
   sigma : Evd.evar_map [@printer (fun fmt m ->
     Format.fprintf fmt "%s" Pp.(string_of_ppcmds (Termops.pr_evar_map None (Global.env()) m)))];
 }
 [@@deriving show]

 let empty_from_env_sigma global_env sigma =
   {
     global_env;
     sigma;
   }

 let empty_from_env env = empty_from_env_sigma env (Evd.from_env env)

 let init () = empty_from_env (Global.env ())

 let engine : coq_engine S.component =
   S.declare ~name:"coq-elpi:evmap-constraint-type"
     ~pp:pp_coq_engine ~init

end

open CoqEngine_HOAS

(* bidir mapping between Elpi's UVars and Coq's Evars *)
module CoqEvarKey = struct
  type t = Evar.t
  let compare = Evar.compare
  let pp fmt t = Format.fprintf fmt "%s" (Pp.string_of_ppcmds (Evar.print t))
  let show t = Format.asprintf "%a" pp t
end
module UVMap = F.Map(CoqEvarKey)

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
  let pp fmt x = Format.fprintf fmt "%s" (show x)
end)

let um = S.declare ~name:"coq-elpi:evar-univ-map"
  ~pp:UM.pp ~init:(fun () -> UM.empty)

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
         state, u, [ E.mkApp E.Constants.eqc (E.mkUnifVar b ~args state) [E.mkCData (univin u)]]
       end
    | _ ->
       univ_to_be_patched.API.Conversion.readback ~depth state t
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
      M (fun ~ok ~ko -> function Sorts.Prop -> ok | _ -> ko ()));
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
    | Sorts.Set -> E.mkApp typc (E.mkCData (univin Univ.type0_univ)) []
    | Sorts.Type u -> E.mkApp typc (E.mkCData (univin u)) [])
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
  Printer.pr_named_context_of env (get_sigma state)

let mk_coq_context state =
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
  local = e :: coq_ctx.local;
  local_len = rel;
  db2rel = Int.Map.add i rel coq_ctx.db2rel;
  env = EConstr.push_rel e coq_ctx.env;
}

(* Not sure this is sufficient, eg we don't restrict evars, but elpi shuld... *)
let restrict_coq_context live_db state { proof; proof_len; local; name2db } =
  mk_coq_context state |>
  List.fold_right (fun e ctx ->
    let id = Context.Named.Declaration.get_id e in
    let db = Names.Id.Map.find id name2db in
    if List.mem db live_db then push_coq_ctx_proof db e ctx else ctx) proof |>
  fun x -> (x,0) |>
  List.fold_right (fun e (ctx,rel) ->
    let db = rel + proof_len in
    if List.mem db live_db then push_coq_ctx_local db e ctx,rel+1 else ctx,rel+1) local |>
  fst

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

let mk_def ~depth name ~bo ~ty ~ctx_len =
  E.mkApp defc E.(mkConst depth) [in_elpi_name name; ty; bo]

let rec constr2lp coq_ctx ~calldepth ~depth state t =
  assert(depth >= coq_ctx.proof_len);
  let { sigma } = S.get engine state in
  let gls = ref [] in
  let rec aux ~depth state t = match EC.kind sigma t with
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
         let args = Array.sub args 0 (Array.length args - coq_ctx.section_len) in
         let state, args = CArray.fold_left_map (aux ~depth) state args in
         state, E.mkUnifVar elpi_uvk ~args:(CArray.rev_to_list args) state
    | C.Sort s -> state, in_elpi_sort (EC.ESorts.kind sigma s)
    | C.Cast (t,_,ty) ->
         let state, t = aux ~depth state t in
         let state, ty = aux ~depth state ty in
         let state, self = aux ~depth:(depth+1) state (EC.mkRel 1) in
         state, in_elpi_let Names.Name.Anonymous t ty self
    | C.Prod(n,s,t) ->
         let state, s = aux ~depth state s in
         let state, t = aux ~depth:(depth+1) state t in
         state, in_elpi_prod n.Context.binder_name s t
    | C.Lambda(n,s,t) ->
         let state, s = aux ~depth state s in
         let state, t = aux ~depth:(depth+1) state t in
         state, in_elpi_lam n.Context.binder_name s t
    | C.LetIn(n,b,s,t) ->
         let state, b = aux ~depth state b in
         let state, s = aux ~depth state s in
         let state, t = aux ~depth:(depth+1) state t in
         state, in_elpi_let n.Context.binder_name b s t
    | C.App(hd,args) ->
         let state, hd = aux ~depth state hd in
         let state, args = CArray.fold_left_map (aux ~depth) state args in
         state, in_elpi_app hd args
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
    | C.Case((*{ C.ci_ind; C.ci_npar; C.ci_cstr_ndecls; C.ci_cstr_nargs }*)_,
             rt,t,bs) ->
         let state, t = aux ~depth state t in
         let state, rt = aux ~depth state rt in
         let state, bs = CArray.fold_left_map (aux ~depth) state bs in
         state,
         in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt 
           (Array.to_list bs)
    | C.Fix(([| rarg |],_),([| name |],[| typ |], [| bo |])) ->
         let state, typ = aux ~depth state typ in
         let state, bo = aux ~depth:(depth+1) state bo in
         state, in_elpi_fix name.Context.binder_name rarg typ bo
    | C.Fix _ -> nYI "HOAS for mutual fix"
    | C.CoFix _ -> nYI "HOAS for cofix"
    | C.Proj _ -> nYI "HOAS for primitive projections"
    | C.Int _ -> nYI "HOAS for primitive machine integers"
    | C.Float _ -> nYI "HOAS for primitive machine floats"
  in
  if debug () then
    Feedback.msg_debug Pp.(str"term2lp: depth=" ++ int depth ++
      str " ctx=" ++ pp_coq_ctx coq_ctx state ++
      str " term=" ++Printer.pr_econstr_env (get_global_env state) (get_sigma state) t);
  let state, t = aux ~depth state t in
  if debug () then
    Feedback.msg_debug Pp.(str"term2lp (out): " ++
      str (pp2string (P.term depth) t));
  state, t, !gls

and under_coq2elpi_ctx ~calldepth state ctx ?(mk_ctx_item=mk_pi_arrow) kont =
  let open Context.Named.Declaration in
  let gls = ref [] in
  let rec aux ~depth coq_ctx hyps state = function
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
        let state, rest = aux ~depth:(depth+1) coq_ctx hyps state rest in
        state, mk_ctx_item hyp rest
      | LocalDef (Context.{binder_name=coq_name},bo,ty) as e :: rest ->
        let name = Name coq_name in
        let state, ty, gls_ty = constr2lp coq_ctx ~calldepth ~depth:(depth+1) state ty in
        let state, bo, gls_bo = constr2lp coq_ctx ~calldepth ~depth:(depth+1) state bo in
        gls := gls_ty @ gls_bo @ !gls;
        let hyp = mk_def ~depth name ~bo ~ty ~ctx_len:coq_ctx.proof_len in
        let hyps = { ctx_entry = hyp ; depth = depth + 1 } :: hyps in
        let coq_ctx = push_coq_ctx_proof depth e coq_ctx in
        let state, rest = aux ~depth:(depth+1) coq_ctx hyps state rest in
        state, mk_ctx_item hyp rest
  in
    let state, t = aux ~depth:calldepth (mk_coq_context state) [] state (List.rev ctx) in
    state, t, !gls

and in_elpi_evar_concl evar_concl elpi_revk elpi_evk coq_ctx hyps ~calldepth ~depth state =
  let state, evar_concl, gls_evar_concl = constr2lp coq_ctx ~calldepth ~depth state evar_concl in
  let args = CList.init coq_ctx.proof_len (fun i -> E.mkConst @@ i + calldepth) in
  let hyps = List.map (fun { ctx_entry; depth = from } ->
    U.move ~from ~to_:depth ctx_entry) hyps in
  state, U.list_to_lp_list (List.rev hyps),
  (E.mkUnifVar elpi_revk ~args state),
  (E.mkUnifVar elpi_evk ~args state),
  evar_concl, gls_evar_concl

and in_elpi_evar_info ~calldepth ~env ~sigma ctx elpi_revk elpi_evk evar_concl state =
  under_coq2elpi_ctx ~calldepth state ctx (fun coq_ctx hyps ~depth state ->
    let state, hyps, raw_ev, ev, ty, gls =
      in_elpi_evar_concl evar_concl elpi_revk elpi_evk coq_ctx hyps
        ~calldepth ~depth state in
    state, E.mkApp declare_evc hyps [raw_ev; ty; ev], gls)

and in_elpi_evar ~calldepth k state =
  if debug () then Feedback.msg_debug Pp.(str"in_elpi_evar:" ++ Evar.print k);
  try
    let elpi_evk = UVMap.elpi k (S.get UVMap.uvmap state) in
    if debug () then Feedback.msg_debug Pp.(str"in_elpi_evar: known " ++
      Evar.print k ++ str" as " ++ str(F.Elpi.show elpi_evk));
    state, elpi_evk, elpi_evk, []
  with Not_found ->
    let state, elpi_evk = F.Elpi.make state in
    let state, elpi_raw_evk = F.Elpi.make state in
    let state, gls = in_elpi_fresh_evar ~calldepth k elpi_raw_evk elpi_evk state in
    state, elpi_evk, elpi_raw_evk, gls

and in_elpi_fresh_evar ~calldepth k elpi_raw_evk elpi_evk state =
    let { sigma; global_env } as e = S.get engine state in
    let state = S.update UVMap.uvmap state (UVMap.add elpi_evk k) in
    if debug () then Feedback.msg_debug Pp.(str"in_elpi_fresh_evar: unknown " ++ Evar.print k);
    let evar_concl, ctx, _ = info_of_evar ~env:global_env ~sigma ~section:(section_ids global_env) k in
    let state, evar_decl, gls = in_elpi_evar_info ~calldepth ~env:global_env ~sigma ctx elpi_raw_evk elpi_evk evar_concl state in
    if debug () then Feedback.msg_debug Pp.(str"in_elpi_fresh_evar: new decl" ++ cut () ++
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
          if debug () then
            Feedback.msg_debug Pp.(str"lp2term: evar: found relevant constraint: " ++
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
        if debug () then            
          Feedback.msg_debug Pp.(str "skip entry" ++
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

let find_evar_decl var csts =
  let rec dblset_of_canonical_ctx ~depth acc = function
    | [] -> acc
    | x :: xs ->
        match E.look ~depth x with
        | E.Const i -> dblset_of_canonical_ctx ~depth (Int.Set.add i acc) xs
        | _ -> err Pp.(str"HOAS: non canonical constraint")
  in
  csts |> CList.find_map (fun ({ E.goal = (depth,concl); context } as cst) ->
    match E.look ~depth concl with
    | E.App(c,x,[ty;rx]) when c == evarc ->
        begin match E.look ~depth x, E.look ~depth rx with
        | E.UnifVar(raw,args), E.UnifVar(r,_) when F.Elpi.(equal raw var || equal r var) ->
          if debug () then
            Feedback.msg_debug Pp.(str"lp2term: evar: found relevant constraint: " ++
              str(pp2string pp_cst cst));
          let visible_set = dblset_of_canonical_ctx ~depth Int.Set.empty args in
          let dbl2ctx = preprocess_context (fun x -> Int.Set.mem x visible_set) context in
          Some (dbl2ctx, raw, r, (depth,ty), cst)
        | _ -> None end
    | _ -> None) 

let rec of_elpi_ctx ~calldepth syntactic_constraints depth dbl2ctx state =

  let aux coq_ctx depth state t =
    lp2constr ~calldepth syntactic_constraints coq_ctx ~depth state t in

  let of_elpi_ctx_entry dbl coq_ctx ~depth e state =
    match e with
    | `Decl(name,ty) ->
        let name = in_coq_fresh_annot ~depth ~coq_ctx dbl name in
        let state, ty, gls = aux coq_ctx depth state ty in
        state, Context.Named.Declaration.LocalAssum(name,ty), gls
    | `Def(name,ty,bo) ->
        let name = in_coq_fresh_annot ~depth ~coq_ctx dbl name in
        let state, ty, gl1 = aux coq_ctx depth state ty in
        let state, bo, gl2 = aux coq_ctx depth state bo in
        state, Context.Named.Declaration.LocalDef(name,bo,ty), gl1 @ gl2
  in
  
  let rec ctx_entries coq_ctx state gls i =
    if i = depth then state, coq_ctx, List.(concat (rev gls))
    else (* context entry for the i-th variable *)
      if not (Int.Map.mem i dbl2ctx)
      then ctx_entries coq_ctx state gls (i+1)
      else
        let d, e = Int.Map.find i dbl2ctx in
        let state, e, gl1 = of_elpi_ctx_entry i coq_ctx ~depth:d e state in
        let coq_ctx = push_coq_ctx_proof i e coq_ctx in
        ctx_entries coq_ctx state (gl1 :: gls) (i+1)
  in
    ctx_entries (mk_coq_context state) state [] 0

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
  | _ -> err Pp.(str"HOAS: expecting a lambda, got: " ++
           str(pp2string (P.term depth) t)) in
  if debug () then
    Feedback.msg_debug 
      Pp.(str"lp2term@" ++ int depth ++ str":" ++
           str(pp2string (P.term depth) t));
  match E.look ~depth t with
  | E.App(s,p,[]) when sortc == s ->
      let state, u, gsl = universe.API.Conversion.readback ~depth state p in
      if debug () then Feedback.msg_debug Pp.(str "xxxxx:" ++ Termops.pr_evar_map None (Global.env()) (get_sigma state));
      state, EC.mkSort u, gsl
 (* constants *)
  | E.App(c,d,[]) when globalc == c ->
     let state, gr = in_coq_gref ~depth state d in
     begin match gr with
     | G.VarRef x -> state, EC.mkVar x, []
     | G.ConstRef x -> state, EC.mkConst x, []
     | G.ConstructRef x -> state, EC.mkConstruct x, []
     | G.IndRef x -> state, EC.mkInd x, []
     end
 (* binders *)
  | E.App(c,name,[s;t]) when lamc == c || prodc == c ->
      let id = in_coq_fresh_annot ~depth ~coq_ctx depth name in
      let name = Context.map_annot Name.mk_name id in
      let state, s, gl1 = aux ~depth state ~on_ty:true s in
      let coq_ctx = push_coq_ctx_local depth (Context.Rel.Declaration.LocalAssum(name,s)) coq_ctx in
      let state, t, gl2 = aux_lam coq_ctx ~depth state t in
      if lamc == c then state, EC.mkLambda (name,s,t), gl1 @ gl2
      else state, EC.mkProd (name,s,t), gl1 @ gl2
  | E.App(c,name,[s;b;t]) when letc == c ->
      let id = in_coq_fresh_annot ~depth ~coq_ctx depth name in
      let name = Context.map_annot Name.mk_name id in
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
           err Pp.(hov 0 (str"Bound variable " ++ str (E.Constants.show n) ++
             str" not found in the Coq context:" ++ cut () ++
             pr_coq_ctx coq_ctx (get_sigma state) ++ cut () ++
             str"Did you forget to load some hypotheses with => ?"))
     else
        err Pp.(str"wrong constant:" ++ str (E.Constants.show n))

 (* app *)
  | E.App(c,x,[]) when appc == c ->
       (match U.lp_list_to_list ~depth x with
       | x :: xs -> 
          let state, x, gl1 = aux ~depth state x in
          let state, xs, gl2 = API.Utils.map_acc (aux ~depth ~on_ty:false) state xs in
          state, EC.mkApp (x, Array.of_list xs), gl1 @ gl2
       | _ -> assert false) (* TODO *)
  
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
          | C.Lambda(_,s,t) -> aux t (Some s)
          | _ -> match o with
            | None -> assert false (* wrong shape of rt XXX *)
            | Some t ->
               match safe_destApp sigma t with
               | C.Ind i, _ -> fst i
               | _ -> assert false (* wrong shape of rt XXX *)
        in
          aux rt None in
      let ci =
        Inductiveops.make_case_info (get_global_env state) ind Sorts.Relevant C.RegularStyle in
      state, EC.mkCase (ci,rt,t,Array.of_list bt), gl1 @ gl2 @ gl3

 (* fix *)
  | E.App(c,name,[rno;ty;bo]) when fixc == c ->
      let id = in_coq_fresh_annot ~depth ~coq_ctx depth name in
      let name = Context.map_annot Name.mk_name id in
      let state, ty, gl1 = aux ~depth state ~on_ty:true ty in
      let coq_ctx = push_coq_ctx_local depth (Context.Rel.Declaration.LocalAssum(name,ty)) coq_ctx in
      let state, bo, gl2 = aux_lam coq_ctx ~depth state bo in
      let rno =
        match E.look ~depth rno with
        | E.CData n when CD.is_int n -> CD.to_int n
        | _ -> err Pp.(str"Not an int: " ++ str (P.Debug.show_term rno)) in
      state, EC.mkFix (([|rno|],0),([|name|],[|ty|],[|bo|])), gl1 @ gl2
  
  (* evar *)
  | E.UnifVar (elpi_evk,args) as x ->
      if debug () then
        Feedback.msg_debug Pp.(str"lp2term: evar: " ++
          str (pp2string (P.term depth) (E.kool x)));
      begin try
        let ext_key = UVMap.host elpi_evk (S.get UVMap.uvmap state) in

        if debug () then
          Feedback.msg_debug Pp.(str"lp2term: evar: already in Coq: " ++
          Evar.print ext_key);

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
            EC.mkApp(EC.mkEvar (ext_key,CArray.of_list args2),
                       CArray.rev_of_list args1)
          else
            EC.mkEvar (ext_key,CArray.of_list all_args) in

        if debug () then
          Feedback.msg_debug Pp.(str"lp2term: evar: args: " ++
            let _, args = EC.destEvar (get_sigma state) ev in
            prlist_with_sep spc (Printer.pr_econstr_env coq_ctx.env (get_sigma state)) (Array.to_list args)
         );
     
        state, ev, gl1
      with Not_found -> try
        let canonical_context, elpi_revkc, elpi_evkc, ty, relevant_constraint =
          find_evar_decl elpi_evk (E.constraints syntactic_constraints) in
        let state, k, gl1 = declare_evar_of_constraint ~calldepth elpi_revkc elpi_evkc elpi_evk syntactic_constraints canonical_context ty state in

        if debug () then Feedback.msg_debug Pp.(str"lp2term: evar: declared new: " ++
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
        let new_args, visible_ctx = args |> CList.map_filter (fun a ->
          match E.look ~depth a with
          | E.Const i as c ->
              if Int.Map.mem i coq_ctx.db2name || Int.Map.mem i coq_ctx.db2rel
              then Some (E.kool c, i)
              else None
          | _ -> err Pp.(str "Flexible term outside llam:\n"++str (pp2string (P.term depth) @@ E.kool x))
          ) |> List.split in
        if List.length new_args = List.length args then
          create_evar_unknown ~calldepth syntactic_constraints
            coq_ctx ~visible_ctx ~depth state elpi_evk ~on_ty (E.kool x)
        else (* TODO: we should record this restriction in case x is non-linear *)
          let state, new_uv = F.Elpi.make state in
          let newuv_args = E.mkUnifVar new_uv ~args:new_args state in
          let ass = E.mkApp E.Constants.eqc (E.kool x) [newuv_args] in
          if debug () then
            Feedback.msg_debug 
              Pp.(str"restriction assignment:\n" ++ str (pp2string (P.term depth) ass));
          let state, t, gls = aux ~depth state newuv_args in
          state, t, ass :: gls
      end

  (* errors *)
  | E.Lam _ ->
       err Pp.(str "out of place lambda: "++
               str (pp2string P.(term depth) t))
  | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Debug.show_term t))

(* Evar info out of thin air: the user wrote an X that was never encountered by
   type checking (of) hence we craft a tower ?1 : ?2 : Type and link X with ?1 *)
and create_evar_unknown ~calldepth syntactic_constraints (coq_ctx : coq_context) ~visible_ctx ~depth ~on_ty state elpi_evk orig =
  let env = (restrict_coq_context visible_ctx state coq_ctx).env in
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
  let state, gls_k = in_elpi_fresh_evar ~calldepth k elpi_evk elpi_evk state in
   if debug () then
    Feedback.msg_debug Pp.(str"lp2term: evar: new unknown: ? |> " ++
      Printer.pr_named_context_of env (get_sigma state) ++ str" |- ? = " ++ Evar.print k ++ cut() ++
      str(show_coq_engine @@ S.get engine state));
  let state, x, gls_orig = lp2constr ~calldepth syntactic_constraints coq_ctx ~depth state ~on_ty orig in
  state, x, gls_kty @ gls_k @ gls_orig

(* Evar info read back from a constraint (contains the context and the type) *)
and declare_evar_of_constraint ~calldepth elpi_revkc elpi_evkc elpi_evk syntactic_constraints ctx (depth_concl,concl) state =
  let state, coq_ctx, gl1 =
    of_elpi_ctx ~calldepth syntactic_constraints depth_concl ctx state in
  let state, ty, gl2 = lp2constr ~calldepth syntactic_constraints coq_ctx ~depth:depth_concl state concl in
  let state, k = S.update_return engine state (fun ({ sigma } as e) ->
    let sigma, t = Evarutil.new_evar~typeclass_candidate:false ~naming:(Namegen.IntroFresh (Names.Id.of_string "elpi_evar")) coq_ctx.env sigma ty in
    { e with sigma }, fst (EConstr.destEvar sigma t)) in
  let state =
    if F.Elpi.equal elpi_evkc elpi_evk then
      S.update UVMap.uvmap state (UVMap.add elpi_evk k)
    else
      S.update UVMap.uvmap state (UVMap.add elpi_revkc k) in
  if debug () then
    Feedback.msg_debug Pp.(str"lp2term: evar: new from constraint: " ++ int depth_concl ++ str" |> " ++
      pp_coq_ctx coq_ctx state ++ str" |- " ++
      str(pp2string (P.term depth_concl) concl) ++
      str " = " ++ Evar.print k);
  state, k, gl1 @ gl2
;;

let lp2constr syntactic_constraints coq_ctx ~depth state t =
    if debug () then
      Feedback.msg_debug Pp.(str"lp2term: depth=" ++ int depth ++
        str " ctx=[" ++ pp_coq_ctx coq_ctx state ++ str"]" ++
        str " term=" ++ str (pp2string (P.term depth) t));
    let state, t, gls = lp2constr ~calldepth:depth syntactic_constraints coq_ctx ~depth state t in
    if debug () then
      Feedback.msg_debug Pp.(str"lp2term: out=" ++ 
        (Printer.pr_econstr_env (get_global_env state) (get_sigma state) t) ++
        spc () ++ str "elpi2coq:" ++ cut () ++ str(UVMap.show (S.get UVMap.uvmap state)) ++ Termops.pr_evar_map None (Global.env()) (get_sigma state));
    state, t, gls

(* ********************************* }}} ********************************** *)

let push_env state name =
  let open Context.Rel.Declaration in
  S.update engine state (fun ({ global_env } as x) ->
     { x with global_env = Environ.push_rel (LocalAssum(Context.make_annot name Sorts.Relevant,C.mkProp)) global_env })
let pop_env state =
  S.update engine state (fun ({ global_env } as x) ->
     { x with global_env = Environ.pop_rel_context 1 global_env })

let get_global_env_sigma state =
  let { global_env; sigma } = S.get engine state in
  Environ.push_context_set (Evd.universe_context_set sigma) global_env, sigma


let set_sigma state sigma = S.update engine state (fun x -> { x with sigma })

(* We reset the evar map since it depends on the env in which it was created *)
let grab_global_env state =
  let env = Global.env () in
  let state = S.set engine state (CoqEngine_HOAS.empty_from_env env) in
  let state = S.set UVMap.uvmap state UVMap.empty in
  state



let solvec = E.Constants.declare_global_symbol "solve"
let goalc = E.Constants.declare_global_symbol "goal"
let nablac = E.Constants.declare_global_symbol "nabla"
let goal_namec = E.Constants.declare_global_symbol "goal-name"

let mk_goal hyps ev ty attrs =
  E.mkApp goalc hyps [ev;ty; U.list_to_lp_list attrs]

let in_elpi_goal ?goal_name ~hyps ~raw_ev ~ty =
  let name = match goal_name with None -> Anonymous | Some x -> Name x in
  let name = E.mkApp goal_namec (in_elpi_name name) [] in
  mk_goal hyps raw_ev ty [name]

let in_elpi_solve ?goal_name ~hyps ~raw_ev ~ty ~args ~new_goals =
  let g = in_elpi_goal ?goal_name ~hyps ~raw_ev ~ty in
  let gl = E.mkCons g E.mkNil in
  E.mkApp solvec args [gl; new_goals]

let embed_goal ~depth state k =
  let calldepth = depth in
  let env = get_global_env state in
  let sigma = get_sigma state in
  let state, elpi_goal_evar, elpi_raw_goal_evar, evar_decls = in_elpi_evar ~calldepth k state in
  let evar_concl, goal_ctx, goal_env =
    info_of_evar ~env ~sigma ~section:(section_ids env) k in
  let goal_name = Evd.evar_ident k sigma in
  under_coq2elpi_ctx ~calldepth state goal_ctx
     ~mk_ctx_item:(fun _ t -> E.mkApp nablac (E.mkLam t) [])
     (fun coq_ctx hyps ~depth state ->
          let state, hyps, raw_ev, _, goal_ty, gls =
            in_elpi_evar_concl evar_concl elpi_raw_goal_evar elpi_goal_evar
              coq_ctx hyps ~calldepth ~depth state in
         state, in_elpi_goal ?goal_name ~hyps ~raw_ev ~ty:goal_ty, gls)

let goal2query env sigma goal loc ?main args ~in_elpi_arg ~depth:calldepth state =
  if not (Evd.is_undefined sigma goal) then
    err Pp.(str (Printf.sprintf "Evar %d is not a goal" (Evar.repr goal)));

  let state = S.set command_mode state false in (* tactic mode *)

  let state = S.set engine state (empty_from_env_sigma env sigma) in
  let state, elpi_goal_evar, elpi_raw_goal_evar, evar_decls = in_elpi_evar ~calldepth goal  state in

  let evar_concl, goal_ctx, goal_env =
    info_of_evar ~env ~sigma ~section:(section_ids env) goal in
  let goal_name = Evd.evar_ident goal sigma in

  let state, query, gls =
    under_coq2elpi_ctx ~calldepth state goal_ctx
     ~mk_ctx_item:(fun _ t -> E.mkApp E.Constants.pic (E.mkLam t) [])
     (fun coq_ctx hyps ~depth state ->
      match main with
      | None ->
          let state, hyps, raw_ev, _, goal_ty, gls =
            in_elpi_evar_concl evar_concl elpi_raw_goal_evar elpi_goal_evar
              coq_ctx hyps ~calldepth ~depth state in

          let state, ek = F.Elpi.make ~name:"NewGoals" state in

          let new_goals = E.mkUnifVar ek ~args:(CList.init (calldepth+coq_ctx.proof_len) E.mkConst) state in
            
          let state, args =
            CList.fold_left_map (in_elpi_arg ~depth coq_ctx [] sigma) state args in
          let args = U.list_to_lp_list args in
          let q = in_elpi_solve ?goal_name ~hyps ~raw_ev ~ty:goal_ty ~args ~new_goals in
          state, q, gls
      | Some text ->
          let state, q = API.Quotation.lp ~depth state loc text in
          state, q, []) in
  let evarmap_query =
    match evar_decls @ gls @ [query] with
    | [] -> assert false
    | [g] -> g
    | x :: xs -> E.mkApp E.Constants.andc x xs in
  
  if debug () then
    Feedback.msg_debug Pp.(str"engine: " ++
      str (show_coq_engine (S.get engine state)));

  state, (loc, evarmap_query)
;;

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

let rec get_goal_ref ~depth syntactic_constraints state t =
  match E.look ~depth t with
  | E.App(c,_,[g;_;_]) when c == goalc ->
     begin match E.look ~depth g with
     | E.UnifVar(ev,_) ->
       begin try
         let ev = find_evar ev syntactic_constraints in
         Some (UVMap.host ev (S.get UVMap.uvmap state))
       with Not_found -> None
       end
     | _ -> err Pp.(str"Not a variable after goal: " ++ str(pp2string (P.term depth) g))
     end
  | E.App(c,g,[]) when c == nablac ->
     begin match E.look ~depth g with
     | E.Lam g -> get_goal_ref ~depth:(depth+1) syntactic_constraints state g
     | _ -> err Pp.(str"Not a lambda after nabla: " ++ str(pp2string (P.term depth) g))
     end
  | _ -> None
  
let no_list_given = function
  | E.UnifVar _ -> true
  | _ -> false

let rec skip_lams ~depth d t = match E.look ~depth t with
  | E.Lam t -> skip_lams ~depth:(depth+1) (d+1) t
  | x -> x, d

let show_engine state =
  show_coq_engine (S.get engine state) ^ "\nCoq-Elpi mapping:\n" ^
  UVMap.show (S.get UVMap.uvmap state)

let elpi_solution_to_coq_solution syntactic_constraints state =
  let { sigma; global_env } as e = S.get engine state in
  
  if debug () then
    Feedback.msg_debug Pp.(str"elpi sigma -> coq sigma: before:\n" ++ str (show_engine state));

  let state, assigned, changed, extra_gls =
    UVMap.fold (fun k elpi_evk elpi_solution (state, assigned, changed, extra) ->
      match elpi_solution with
      | None -> (state, assigned, changed, extra)
      | Some t ->

       (* The canonical context in which have to port the solution found by elpi *)
       let _, ctx, _ = info_of_evar ~env:global_env ~sigma ~section:(section_ids global_env) k in

       (* under_coq_ctx is tied to elpi terms, while here I need the coq_ctx to
          convert the term back, hence this spill hack *)
       let spilled_solution = ref (EConstr.mkProp) in
       let state, _, gls = under_coq2elpi_ctx ~calldepth:0 state ctx ~mk_ctx_item:(fun _ x -> x) 
         (fun coq_ctx hyps ~depth state ->
            if debug () then
              Feedback.msg_debug Pp.(str"solution for "++ Evar.print k ++ str" in ctx=" ++
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

       state, assigned, true, gls :: extra) (S.get UVMap.uvmap state) 
     (state, Evar.Set.empty, false, [])
  in
    
  (* Drop from the mapping the evars that were assigned *)
  let state = S.update UVMap.uvmap state
    (UVMap.filter (fun k _ -> not (Evar.Set.mem k assigned))) in

  if debug () then
    Feedback.msg_debug Pp.(str"elpi sigma -> coq sigma: after:\n" ++ str (show_engine state));

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
           match get_goal_ref ~depth syntactic_constraints state x with
           | Some g -> g
           | None -> err Pp.(str"Not a goal " ++ str(pp2string (P.term depth) x) ++ str " in " ++ cut () ++ str(pp2string (API.Pp.constraints pp_ctx) constraints))) l in
         let declared_set =
           List.fold_right Evar.Set.add declared Evar.Set.empty in
         declared,
         Evar.Set.elements @@ Evar.Set.diff all_goals declared_set
   (*i
   let sigma = (cs_get_engine state).sigma in
   (* Purge *)
   let state = cs_set_engine state (empty_from_env_sigma env sigma) in
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
  if debug () then
    Feedback.msg_debug
      Pp.(str"reachable from:" ++
          prlist_with_sep spc Evar.print (Evar.Set.elements roots) ++
          str" = " ++
          prlist_with_sep spc Evar.print (Evar.Set.elements res));
  res

let tclSOLUTION2EVD { API.Data.constraints; assignments; state; pp_ctx } =
  let open Proofview.Unsafe in
  let open Proofview.Notations in
  let open Tacticals.New in
  tclGETGOALS >>= fun gls ->
    let gls = gls |> List.map Proofview.drop_state in
    let roots = List.fold_right Evar.Set.add gls Evar.Set.empty in
    let state, solved_goals, _, _gls = elpi_solution_to_coq_solution constraints state in
    let all_goals = reachable (get_sigma state) roots Evar.Set.empty in
    let declared_goals, shelved_goals =
      get_declared_goals (Evar.Set.diff all_goals solved_goals) constraints state assignments pp_ctx in
  tclTHENLIST [
    tclEVARS (S.get engine state).sigma;
    tclSETGOALS @@ List.map Proofview.with_empty_state declared_goals;
    Proofview.shelve_goals shelved_goals
  ]

let rm_evarc = E.Constants.declare_global_symbol "rm-evar"

let set_current_sigma ~depth state sigma =
  let state = set_sigma state sigma in
  let state, assignments, decls, to_remove_coq, to_remove_elpi =
    UVMap.fold (fun k elpi_evk solution (state, assignments, decls, to_remove_coq, to_remove_elpi as acc) ->
      let info = Evd.find sigma k in
      match Evd.evar_body info with
      | Evd.Evar_empty -> acc
      | Evd.Evar_defined c ->
          let ctx = Evd.evar_filtered_context info in
          let env = get_global_env state in
          let section_ids = section_ids env in
          let ctx = ctx |> List.filter (fun e -> let id = Context.Named.Declaration.get_id e in not(List.mem id section_ids)) in
          let assigned = E.mkUnifVar elpi_evk ~args:[] state in
          if debug () then
            Feedback.msg_debug Pp.(str"preparing assignment for " ++ str (pp2string (P.term depth) assigned) ++
              str" under context " ++ Printer.pr_named_context env sigma (EConstr.Unsafe.to_named_context ctx));
          let state, t, dec = under_coq2elpi_ctx ~mk_ctx_item:(fun _ -> E.mkLam) ~calldepth:depth state ctx (fun coq_ctx hyps ~depth:new_ctx_depth state ->
            constr2lp coq_ctx ~calldepth:depth ~depth:new_ctx_depth state c) in
          (* TODO: it may be worth using unify-eq directly here, so to make the API
            less error prone (see coq-elaborator) but sometimes one needs unify-leq so
            it is unclear... *)
          let assignment = E.mkAppL E.Constants.eqc [assigned; t] in
          if debug () then
            Feedback.msg_debug Pp.(str"assignment:\n" ++ str (pp2string (P.term depth) assignment));
          state, assignment :: assignments, dec :: decls, k :: to_remove_coq, (elpi_evk, List.length ctx) :: to_remove_elpi
      ) (S.get UVMap.uvmap state) (state,[],[],[],[]) in
  let state = S.update UVMap.uvmap state (List.fold_right UVMap.remove_host to_remove_coq) in
  let removals = to_remove_elpi |> List.map (fun (k,ano) -> E.mkAppL rm_evarc [E.mkUnifVar k ~args:(CList.init ano (fun x -> E.mkConst (x+depth))) state]) in
  state, removals @ List.concat decls @ assignments

let get_goal_ref ~depth cst s t =
  get_goal_ref ~depth (E.constraints cst) s t

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


type 'a unspec = Given of 'a | Unspec
let unspec2opt = function Given x -> Some x | Unspec -> None
let opt2unspec = function Some x -> Given x | None -> Unspec

let unspecC data = let open API.ContextualConversion in {
  ty = data.ty;
  pp_doc = data.pp_doc;
  pp = (fun fmt -> function
    | Unspec -> Format.fprintf fmt "Unspec"
    | Given x -> Format.fprintf fmt "Given %a" data.pp x);
  embed = (fun ~depth hyps constraints state -> function
     | Given x -> data.embed ~depth hyps constraints state x
     | Unspec -> state, E.mkDiscard, []);
  readback = (fun ~depth hyps constraints state x ->
      match E.look ~depth x with
      | E.UnifVar _ -> state, Unspec, []
      | t ->
        let state, x, gls = data.readback ~depth hyps constraints state (E.kool t) in
        state, Given x, gls)
}
let unspec d = API.ContextualConversion.(!<(unspecC (!> d)))

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

let record_field_attributes = unspec (API.BuiltInData.list record_field_att)

let is_coercion_att = function
  | Unspec -> false
  | Given l ->
      let rec aux = function
      | [] -> false
      | Coercion x :: _ -> x
      | _ :: l -> aux l
      in
        aux l
let is_canonical_att = function
  | Unspec -> true
  | Given l ->
      let rec aux = function
      | [] -> true
      | Canonical x :: _ -> x
      | _ :: l -> aux l
      in
        aux l

let parameterc = E.Constants.declare_global_symbol "parameter"
let constructorc = E.Constants.declare_global_symbol "constructor"
let inductivec = E.Constants.declare_global_symbol "inductive"
let coinductivec = E.Constants.declare_global_symbol "coinductive"
let recordc = E.Constants.declare_global_symbol "record"
let fieldc = E.Constants.declare_global_symbol "field"
let end_recordc = E.Constants.declare_global_symbol "end-record"

let in_elpi_id = function
  | Names.Name.Name id -> CD.of_string (Names.Id.to_string id)
  | Names.Name.Anonymous -> CD.of_string "_"

let in_elpi_bool state b =
  let _, b, _ = Elpi.Builtin.bool.API.Conversion.embed ~depth:0 state b in
  b

let in_elpi_indtdecl_parameter id ty rest =
  E.mkApp parameterc (in_elpi_name id) [ty;E.mkLam rest]
let in_elpi_indtdecl_record rid arity kid rest =
  E.mkApp recordc (in_elpi_id rid) [arity;in_elpi_id kid;rest]
let in_elpi_indtdecl_endrecord () =
  E.mkConst end_recordc

type record_field_spec = { name : Name.t; is_coercion : bool; is_canonical : bool }
let in_elpi_indtdecl_field ~depth s { name; is_coercion; is_canonical } ty rest =
  let open API.Conversion in
  let s, att, gl = record_field_attributes.embed ~depth s (Given [Coercion is_coercion; Canonical is_canonical]) in
  assert(gl = []);
  s, E.mkApp fieldc att [in_elpi_id name;ty;E.mkLam rest], gl

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

let lp2inductive_entry ~depth coq_ctx constraints state t =

  let lp2constr coq_ctx ~depth state t =
    lp2constr constraints coq_ctx ~depth state t in

  let open Entries in

  (* turns a prefix of the arity (corresponding to the non-uniform parameters)
   * into a context *)
  let decompose_nu_arity sigma arity nupno msg =
    let ctx, rest = EC.decompose_prod_assum sigma arity in
    let n = Context.Rel.length ctx in
    if n < nupno then err Pp.(int nupno ++
      str" non uniform parameters declared, but only " ++ int n ++
      str " products found in " ++ str msg);
    let unpctx = CList.lastn nupno ctx in
    let ctx = CList.firstn (n - nupno) ctx in
    let nuparams = force_name_ctx unpctx in
    nuparams, EC.it_mkProd_or_LetIn rest ctx in

  (* To check if all constructors share the same context of non-uniform
   * parameters *)
  let rec cmp_nu_ctx sigma k ~arity_nuparams:c1 c2 =
    let open Context.Rel.Declaration in
    match c1, c2 with
    | [], [] -> ()
    | LocalAssum (n1, t1) :: c1, LocalAssum (n2, t2) :: c2 ->
        if not (EC.eq_constr_nounivs sigma (EC.Vars.lift 1 t1) t2) && 
           not (EC.isEvar sigma t2) then
          err Pp.(str"in constructor " ++ Id.print k ++
            str" the type of " ++
            str"non uniform argument " ++ Name.print n2.Context.binder_name ++
            str" is different from the type declared in the inductive"++
            str" type arity as " ++ Name.print n1.Context.binder_name);
      cmp_nu_ctx sigma k ~arity_nuparams:c1 c2
    | (LocalDef _ :: _, _) | (_, LocalDef _ :: _) ->
        err Pp.(str "let-in not supported here")
    | _ -> assert false in

  let aux_construtors coq_ctx ~depth params nupno arity itname finiteness state ks =

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
              let state, ty, gls = lp2constr coq_ctx ~depth state ty in
              (state, gls :: extra), (name, ty)
            | _ -> err Pp.(str"@gref expected: "  ++
                 str (pp2string P.(term depth) name))
            end
        | _ -> err Pp.(str"constructor expected: "  ++
                 str (pp2string P.(term depth) t)))
      (state,[]) ks in
    let knames, ktypes = List.split names_ktypes in 

    let sigma = get_sigma state in

    (* Handling of non-uniform parameters *)
    let arity, nuparams, ktypes =
      if nupno = 0 then arity, [], ktypes
      else
        let nuparams, arity =
          decompose_nu_arity sigma arity nupno "inductive type arity" in
        let replace_nup name t =
          let cur_nuparams, t =
            decompose_nu_arity sigma t nupno
              (" constructor " ^ Id.to_string name) in
          cmp_nu_ctx sigma name ~arity_nuparams:nuparams cur_nuparams;
          t
         in
        let ktypes = List.map2 replace_nup knames ktypes in
        arity, nuparams, ktypes in

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

    if debug () then
      Feedback.msg_debug Pp.(str"Inductive declaration with sigma:" ++ cut() ++
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
    if debug () then
      Feedback.msg_debug Pp.(str"Inductive declaration with restricted sigma:" ++ cut() ++
        Termops.pr_evar_map None (Global.env()) sigma);
    let oe = {
      mind_entry_typename = itname;
      mind_entry_arity = arity;
      mind_entry_template = false;
      mind_entry_consnames = knames;
      mind_entry_lc = ktypes } in
    state, {
      mind_entry_record = if finiteness = Declarations.BiFinite then Some None else None;
      mind_entry_finite = finiteness;
      mind_entry_params = params;
      mind_entry_inds = [oe];
      mind_entry_universes =
        Monomorphic_entry (Evd.universe_context_set sigma);
      mind_entry_cumulative = false;
      mind_entry_private = None; }, List.(concat (rev gls_rev))
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
          in_elpi_prod (in_coq_name ~depth n) ty tf
      | _ -> err Pp.(str"field/end-record expected: "++
                   str (pp2string P.(term depth) fields))
      end
    | E.Const c when c == end_recordc -> state, [], ind
    | _ ->  err Pp.(str"field/end-record expected: "++ 
                 str (pp2string P.(term depth) fields))
  in

  let rec aux_decl coq_ctx ~depth params state extra t =

    match E.look ~depth t with
    | E.App(c,name,[ty;decl]) when is_coq_name ~depth name && c == parameterc ->
        let name = in_coq_annot ~depth name in
        let state, ty, gls = lp2constr coq_ctx ~depth state ty in
        let e = Context.Rel.Declaration.LocalAssum(name,ty) in
        aux_lam e coq_ctx ~depth (e :: params) state (gls :: extra) decl
    | E.App(c,id,[nupno;arity;ks])
      when (c == inductivec || c == coinductivec) ->
      begin match E.look ~depth nupno  with
      | E.CData nupno when CD.is_int nupno ->
        let name = in_coq_annot ~depth id in
        if Name.is_anonymous (Context.binder_name name) then
          err Pp.(str"id expected, got: "++ str (pp2string P.(term depth) id));
        let nupno = CD.to_int nupno in
        let fin =
          if c == inductivec then Declarations.Finite
          else Declarations.CoFinite in
        let state, arity, gl1 = lp2constr coq_ctx ~depth state arity in
        let e = Context.Rel.Declaration.LocalAssum(name,arity) in
        let iname =
          match Context.binder_name name with Name x -> x | _ -> assert false in
        begin match E.look ~depth ks with
        | E.Lam t -> 
            let ks = U.lp_list_to_list ~depth:(depth+1) t in
            let state, idecl, gl2 = 
              aux_construtors (push_coq_ctx_local depth e coq_ctx) ~depth:(depth+1) params nupno arity iname fin
                state ks in
            state, (idecl, None), List.(concat (rev (gl2 :: gl1 :: extra)))
        | _ -> err Pp.(str"lambda expected: "  ++
                 str (pp2string P.(term depth) ks))
        end
      | _ -> err Pp.(str"int expected, got: "++ 
                 str (pp2string P.(term depth) nupno))
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
        let k = [E.mkApp constructorc kn [kty]] in
        let state, idecl, gl2 =
          aux_construtors (push_coq_ctx_local depth e coq_ctx) ~depth:(depth+1) params 0 arity iname Declarations.BiFinite
            state k in
        state, (idecl, Some fields_names_coercions), List.(concat (rev (gl2 :: gl1 :: extra)))
      | _ -> err Pp.(str"id expected, got: "++ 
                 str (pp2string P.(term depth) kn))
      end
    | _ -> err Pp.(str"(co)inductive/record expected: "++ 
                 str (pp2string P.(term depth) t))
  and aux_lam e coq_ctx ~depth params state extra t =
    match E.look ~depth t with
    | E.Lam t -> aux_decl (push_coq_ctx_local depth e coq_ctx) ~depth:(depth+1) params state extra t
    | _ -> err Pp.(str"lambda expected: "  ++
                 str (pp2string P.(term depth) t))
  in
    aux_decl coq_ctx ~depth [] state [] t

(* ********************************* }}} ********************************** *)
(* ****************************** API ********************************** *)

let get_current_env_sigma ~depth hyps constraints state =
(* TODO: cahe longer env in coq_engine for later reuse, use == on hyps+depth? *)
  let state, _, changed, gl1 = elpi_solution_to_coq_solution constraints state in
  let state, coq_ctx, gl2 =
    of_elpi_ctx ~calldepth:depth constraints depth (preprocess_context (fun _ -> true) (E.of_hyps hyps)) state in
  state, coq_ctx, get_sigma state, gl1 @ gl2
;;

let constr2lp ~depth coq_ctx _constraints state t =
  constr2lp coq_ctx ~calldepth:depth ~depth state t

let lp2constr ~depth coq_ctx constraints state t =
  lp2constr constraints coq_ctx ~depth state t

let lp2constr_closed ~depth constraints state t =
  lp2constr ~depth (mk_coq_context state) constraints state t

let constr2lp_closed ~depth constraints state t =
  constr2lp ~depth (mk_coq_context state) constraints state t

let lp2constr_closed_ground ~depth state t =
  let state, t1, _ as res = lp2constr ~depth (mk_coq_context state) E.no_constraints state t in
  if not (Evarutil.is_ground_term (get_sigma state) t1) then
    raise API.Conversion.(TypeErr(TyName"closed_term",depth,t));
  res

let constr2lp_closed_ground ~depth state t =
  assert (Evarutil.is_ground_term (get_sigma state) t);
  constr2lp ~depth (mk_coq_context state) E.no_constraints state t

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
  mod_constraints;    (* Univ.ContextSet.t *)
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
