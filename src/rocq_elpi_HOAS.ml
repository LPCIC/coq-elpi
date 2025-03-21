(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module E  = API.RawData
module CD = API.RawOpaqueData
module U  = API.Utils
module P  = API.RawPp
module S  = API.State
module F = API.FlexibleData
module A = API.Ast.Term

module C = Constr
module EC = EConstr
open Names
module G = GlobRef
open Rocq_elpi_utils

(* ************************************************************************ *)
(* ****************** HOAS of Coq terms and goals ************************* *)
(* See also coq-HOAS.elpi (terms)                                           *)
(* ************************************************************************ *)

(* {{{ CData ************************************************************** *)

(* names *)
let namein, naminc, isname, nameout, name =
  let { CD.cin; cino; isc; cout }, name  = CD.declare {
    CD.name = "name";
    doc = "Name.Name.t: Name hints (in binders), can be input writing a name between backticks, e.g. `x` or `_` for anonymous. Important: these are just printing hints with no meaning, hence in elpi two name are always related: `x` = `y`";
    pp = (fun fmt x ->
      Format.fprintf fmt "`%a`" Pp.pp_with (Name.print x));
    compare = (fun _ _ -> 0);
    hash = (fun _ -> 0);
    hconsed = false;
    constants = [];
  } in
  cin, cino, isc, cout, name
;;
let in_elpi_name x = namein x
let in_elpiast_name ~loc x = A.mkOpaque ~loc @@ naminc x
let coq_language = ref API.Quotation.elpi_language
let set_coq coq = coq_language := coq
let name_of_name = function
  | Names.Name.Anonymous -> None
  | Names.Name.Name id -> Some (API.Ast.Name.from_string @@ Names.Id.to_string id, !coq_language)

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

(* engine prologue, to break ciclicity *)

type coq_engine = {
   global_env : Environ.env;
   sigma : Evd.evar_map; (* includes universe constraints *)
}
let pre_engine : coq_engine S.component option ref = ref None

(* universes *)

module UnivOrd = struct
  type t = Univ.Universe.t
  let compare = Univ.Universe.compare
  let show x = Pp.string_of_ppcmds (Univ.Universe.pr UnivNames.pr_level_with_global_universes x)
  let pp fmt x = Format.fprintf fmt "%s" (show x)
end
module UnivSet = U.Set.Make(UnivOrd)
module UnivMap = U.Map.Make(UnivOrd)
module UnivLevelOrd = struct
  type t = Univ.Level.t
  let compare = Univ.Level.compare
  let show x = Pp.string_of_ppcmds (UnivNames.pr_level_with_global_universes x)
  let pp fmt x = Format.fprintf fmt "%s" (show x)
end
module UnivLevelSet = U.Set.Make(UnivLevelOrd)
module UnivLevelMap = U.Map.Make(UnivLevelOrd)

(* map from Elpi evars and Coq's universe levels *)
module UM = F.Map(struct
  type t = Univ.Universe.t
  let compare = Univ.Universe.compare
  let show x = Pp.string_of_ppcmds @@ Univ.Universe.pr UnivNames.pr_level_with_global_universes x
  let pp fmt x = Format.fprintf fmt "%a" Pp.pp_with (Univ.Universe.pr UnivNames.pr_level_with_global_universes x)
end)

let um = S.declare_component ~name:"rocq-elpi:evar-univ-map" ~descriptor:interp_state
  ~pp:UM.pp ~init:(fun () -> UM.empty) ~start:(fun x -> x) ()


let constraint_leq u1 u2 =
  let open UnivProblem in
  ULe (u1, u2)

let constraint_eq u1 u2 =
  let open UnivProblem in
  ULe (u1, u2)

let add_constraints state c = S.update (Option.get !pre_engine) state (fun ({ sigma } as x) ->
  { x with sigma = Evd.add_universe_constraints sigma c })
    
let add_universe_constraint state c =
  let open UnivProblem in
  try add_constraints state (Set.singleton c)
  with
  | UGraph.UniverseInconsistency p ->
      let sigma = (S.get (Option.get !pre_engine) state).sigma in
      Feedback.msg_debug
        (UGraph.explain_universe_inconsistency
          (Termops.pr_evd_qvar sigma)
          (Termops.pr_evd_level sigma)
           p);
      raise API.BuiltInPredicate.No_clause
  | Evd.UniversesDiffer | UState.UniversesDiffer ->
      Feedback.msg_debug Pp.(str"UniversesDiffer");
      raise API.BuiltInPredicate.No_clause

let new_univ_level_variable ?(flexible=false) state =
  S.update_return (Option.get !pre_engine) state (fun ({ sigma } as e) ->
    (* ~name: really mean the universe level is a binder as in Definition f@{x} *)
    let rigidity = if flexible then UState.univ_flexible_alg else UState.univ_rigid in
    let sigma, v = Evd.new_univ_level_variable ?name:None rigidity sigma in
    let u = Univ.Universe.make v in
    (*
    let sigma = Evd.add_universe_constraints sigma
        (UnivProblem.Set.singleton (UnivProblem.ULe (Sorts.set,Sorts.sort_of_univ u))) in
*)
    { e with sigma }, (v, u))

    
(* We patch data_of_cdata by forcing all output universes that
 * are unification variables to be a Coq universe variable, so that
 * we can always call Coq's API *)
let isuniv, univout, univino, (univ : Univ.Universe.t API.Conversion.t) =
  let { CD.cin = univin; cino = univino; isc = isuniv; cout = univout }, univ_to_be_patched = CD.declare {
    CD.name = "univ";
    doc = "universe level (algebraic: max, +1, univ.variable)";
    pp = (fun fmt x ->
      let s = Pp.string_of_ppcmds (Univ.Universe.pr UnivNames.pr_level_with_global_universes x) in
      Format.fprintf fmt "«%s»" s);
    compare = Univ.Universe.compare;
    hash = Univ.Universe.hash;
    hconsed = false;
    constants = [];
  } in
  (* turn UVars into fresh universes *)
  isuniv, univout, univino, { univ_to_be_patched with
  API.Conversion.readback = begin fun ~depth state t ->
    match E.look ~depth t with
    | E.UnifVar (b,args) ->
       let m = S.get um state in
       begin try
         let u = UM.host b m in
         state, u, []
       with Not_found ->
         (* flexible makes {{ Type }} = {{ Set }} also true when coq.unify-eq {{ Type }} {{ Set }} *)
         let state, (_,u) = new_univ_level_variable ~flexible:true state in
         let state = S.update um state (UM.add b u) in
         state, u, [ API.Conversion.Unify(E.mkUnifVar b ~args state,univin u) ]
       end
    | _ -> univ_to_be_patched.API.Conversion.readback ~depth state t
  end
}

let propc = E.Constants.declare_global_symbol "prop"
let spropc = E.Constants.declare_global_symbol "sprop"
let typc = E.Constants.declare_global_symbol "typ"

let sort =
  let open API.AlgebraicData in  declare {
  ty = API.Conversion.TyName "sort";
  doc = "Sorts (kinds of types)";
  pp = (fun fmt -> function
    | Sorts.Type _ -> Format.fprintf fmt "Type"
    | Sorts.Set -> Format.fprintf fmt "Set"
    | Sorts.Prop -> Format.fprintf fmt "Prop"
    | Sorts.SProp -> Format.fprintf fmt "SProp"
    | Sorts.QSort _ -> Format.fprintf fmt "Type");
  constructors = [
    K("prop","impredicative sort of propositions",N,
      B Sorts.prop,
      M (fun ~ok ~ko -> function Sorts.Prop -> ok | _ -> ko ()));
    K("sprop","impredicative sort of propositions with definitional proof irrelevance",N,
      B Sorts.sprop,
      M (fun ~ok ~ko -> function Sorts.SProp -> ok | _ -> ko ()));
    K("typ","predicative sort of data (carries a universe level)",A(univ,N),
      B (fun x -> Sorts.sort_of_univ x),
      M (fun ~ok ~ko -> function
        | Sorts.Type x -> ok x
        | Sorts.Set -> ok Univ.Universe.type0
        | _ -> ko ()));
    K("uvar","",A(F.uvar,N),
      BS (fun (k,_) state ->
        let m = S.get um state in
        try
          let u = UM.host k m in
          state, Sorts.sort_of_univ u
        with Not_found ->
          let state, (_,u) = new_univ_level_variable state in
          let state = S.update um state (UM.add k u) in
          state, Sorts.sort_of_univ u),
      M (fun ~ok ~ko _ -> ko ()));
  ]
} |> API.ContextualConversion.(!<)

let ast_sort ~loc = function
  | Sorts.Prop -> A.mkGlobal ~loc propc
  | Sorts.SProp -> A.mkGlobal ~loc spropc
  | Sorts.Set -> A.mkAppGlobal ~loc typc (A.mkOpaque ~loc @@ univino Univ.Universe.type0) []
  | Sorts.Type u -> A.mkAppGlobal ~loc typc (A.mkOpaque ~loc @@ univino u) []
  | _ -> assert false

let universe_level_variable =
  let { CD.cin = levelin }, universe_level_variable_to_patch = CD.declare {
    CD.name = "univ.variable";
    doc = "universe level variable";
    pp = (fun fmt x ->
      let s = Pp.string_of_ppcmds (UnivNames.pr_level_with_global_universes x) in
      Format.fprintf fmt "«%s»" s);
    compare = Univ.Level.compare;
    hash = Univ.Level.hash;
    hconsed = false;
    constants = [];
  } in
  { universe_level_variable_to_patch with
  API.Conversion.readback = begin fun ~depth state t ->
    match E.look ~depth t with
    | E.UnifVar (b,args) ->
       let m = S.get um state in
       begin try
         let u = UM.host b m in
         state, Option.get @@ Univ.Universe.level u, []
       with Not_found ->
         let state, (l,u) = new_univ_level_variable state in
         let state = S.update um state (UM.add b u) in
         state, l, [ API.Conversion.Unify(E.mkUnifVar b ~args state,levelin l) ]
       end
    | _ -> universe_level_variable_to_patch.API.Conversion.readback ~depth state t
  end
}

let universe_constraint : Univ.univ_constraint API.Conversion.t =
  let open API.Conversion in let open API.AlgebraicData in declare {
  ty = TyName "univ-constraint";
  doc = "Constraint between two universes level variables";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("lt","",A(universe_level_variable,A(universe_level_variable,N)),
      B (fun u1 u2 -> (u1,Univ.Lt,u2)),
      M (fun ~ok ~ko -> function (l1,Univ.Lt,l2) -> ok l1 l2 | _ -> ko ()));
    K("le","",A(universe_level_variable,A(universe_level_variable,N)),
      B (fun u1 u2 -> (u1,Univ.Le,u2)),
      M (fun ~ok ~ko -> function (l1,Univ.Le,l2) -> ok l1 l2 | _ -> ko ()));
    K("eq","",A(universe_level_variable,A(universe_level_variable,N)),
      B (fun u1 u2 -> (u1,Univ.Eq,u2)),
      M (fun ~ok ~ko -> function (l1,Univ.Eq,l2) -> ok l1 l2 | _ -> ko ()))
  ]
} |> API.ContextualConversion.(!<)

let universe_variance : (Univ.Level.t * UVars.Variance.t option) API.Conversion.t =
  let open API.Conversion in let open API.AlgebraicData in declare {
  ty = TyName "univ-variance";
  doc = "Variance of a universe level variable";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("auto","",A(universe_level_variable,N),
      B (fun u -> u,None),
      M (fun ~ok ~ko -> function (u,None) -> ok u | _ -> ko ()));
    K("covariant","",A(universe_level_variable,N),
      B (fun u -> u,Some UVars.Variance.Covariant),
      M (fun ~ok ~ko -> function (u,Some UVars.Variance.Covariant) -> ok u | _ -> ko ()));
    K("invariant","",A(universe_level_variable,N),
      B (fun u -> u,Some UVars.Variance.Invariant),
      M (fun ~ok ~ko -> function (u,Some UVars.Variance.Invariant) -> ok u | _ -> ko ()));
    K("irrelevant","",A(universe_level_variable,N),
      B (fun u -> u,Some UVars.Variance.Invariant),
      M (fun ~ok ~ko -> function (u,Some UVars.Variance.Irrelevant) -> ok u | _ -> ko ()));
  ]
} |> API.ContextualConversion.(!<)

type universe_decl = (Univ.Level.t list * bool) * (Univ.Constraints.t * bool)
let universe_decl : universe_decl API.Conversion.t =
  let open API.Conversion in let open API.BuiltInData in let open API.AlgebraicData in let open Elpi.Builtin in declare {
  ty = TyName "upoly-decl";
  doc = "Constraints for a non-cumulative declaration. Boolean tt means loose (e.g. the '+' in f@{u v + | u < v +})";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("upoly-decl","",A(list universe_level_variable,A(bool,A(list universe_constraint,A(bool,N)))),
     B (fun x sx y sy-> (x,sx),(Univ.Constraints.of_list  y,sy)),
     M (fun ~ok ~ko:_ ((x,sx),(y,sy)) -> ok x sx (Univ.Constraints.elements y) sy))
  ]
} |> API.ContextualConversion.(!<)

type universe_decl_cumul = ((Univ.Level.t * UVars.Variance.t option) list  * bool) * (Univ.Constraints.t * bool)
let universe_decl_cumul : universe_decl_cumul API.Conversion.t =
  let open API.Conversion in let open API.BuiltInData in let open API.AlgebraicData in let open Elpi.Builtin in declare {
  ty = TyName "upoly-decl-cumul";
  doc = "Constraints for a cumulative declaration. Boolean tt means loose (e.g. the '+' in f@{u v + | u < v +})";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("upoly-decl-cumul","",A(list universe_variance,A(bool,A(list universe_constraint,A(bool,N)))),
     B (fun x sx y sy -> ((x,sx),(Univ.Constraints.of_list y,sy))),
     M (fun ~ok ~ko:_ ((x,sx),(y,sy)) -> ok x sx (Univ.Constraints.elements y) sy))
  ]
} |> API.ContextualConversion.(!<)



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
type uinstanceoption =
  | NoInstance
    (* the elpi command involved has to generate a fresh instance *)
  | ConcreteInstance of UVars.Instance.t
    (* a concrete instance was provided, the command will use it *)
  | VarInstance of (F.Elpi.t * E.term list * inv_rel_key)
    (* a variable was provided, the command will compute the instance to unify with it *)
type universe_decl_option =
  | NotUniversePolymorphic
  | Cumulative of universe_decl_cumul
  | NonCumulative of universe_decl
type options = {
  hoas_holes : hole_mapping option;
  local : bool option;
  user_warns : UserWarn.t option;
  primitive : bool option;
  failsafe : bool; (* readback is resilient to illformed terms *)
  ppwidth : int;
  pp : ppoption;
  pplevel : Constrexpr.entry_relative_level;
  using : string option;
  inline : Declaremods.inline;
  uinstance : uinstanceoption;
  universe_decl : universe_decl_option;
  reversible : bool option;
  keepunivs : bool option;
  redflags : RedFlags.reds option;
  no_tc: bool option;
}
let default_options () = {
  hoas_holes = Some Verbatim;
  local = None;
  user_warns = None;
  primitive = None;
  failsafe = false;
  ppwidth = Option.default 80 (Topfmt.get_margin ());
  pp = Normal;
  pplevel = Constrexpr.LevelSome;
  using = None;
  inline = Declaremods.NoInline;
  uinstance = NoInstance;
  universe_decl = NotUniversePolymorphic;
  reversible = None;
  keepunivs = None;
  redflags = None;
  no_tc = None;
}
let make_options ~hoas_holes ~local ~warn ~depr ~primitive ~failsafe ~ppwidth
  ~pp ~pplevel ~using ~inline ~uinstance ~universe_decl ~reversible ~keepunivs
  ~redflags ~no_tc = 
  let user_warns = Some UserWarn.{ depr; warn } in
  { hoas_holes; local; user_warns; primitive; failsafe; ppwidth; pp;
    pplevel; using; inline; uinstance; universe_decl; reversible; keepunivs;
    redflags; no_tc; }
let make_warn = UserWarn.make_warn

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
fun ~depth dbl name ~names ->
  match in_coq_name ~depth name with
  | Name.Anonymous when id_only -> Name.Name (mk_fresh dbl)
  | Name.Anonymous as x -> x
  | Name.Name id when Id.Set.mem id names -> Name.Name (mk_fresh dbl)
  | Name.Name id as x -> x

let relevant = EConstr.ERelevance.relevant
let anonR = Context.make_annot Names.Name.Anonymous EConstr.ERelevance.irrelevant 
let nameR x = Context.make_annot (Names.Name.Name x) EConstr.ERelevance.irrelevant 
let annotR x = Context.make_annot x EConstr.ERelevance.irrelevant 
    
let in_coq_annot ~depth t = Context.make_annot (in_coq_name ~depth t) relevant

let in_coq_fresh_annot_name ~depth ~coq_ctx dbl t =
  Context.make_annot (in_coq_fresh ~id_only:false ~depth ~names:coq_ctx.names dbl t) relevant

let in_coq_fresh_annot_id ~depth ~names dbl t =
  let get_name = function Name.Name x -> x | Name.Anonymous -> assert false in
  Context.make_annot (in_coq_fresh ~id_only:true ~depth ~names dbl t |> get_name) relevant

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

let ({ CD.isc = isconstant; cout = constantout; cin = constantin; cino = constantino },constant),
    ({ CD.isc = isinductive; cout = inductiveout; cin = inductivein; cino = inductiveino },inductive),
    ({ CD.isc = isconstructor; cout = constructorout; cin = constructorin; cino = constructorino },constructor) =
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
let inductiveina ~loc x = A.mkOpaque ~loc (inductiveino x)
let constantina ~loc x = A.mkOpaque ~loc (constantino x)
let constructorina ~loc x = A.mkOpaque ~loc (constructorino x)

let compare_instances x y =
  let qx, ux = UVars.Instance.to_array x
  and qy, uy = UVars.Instance.to_array y in
  Util.Compare.(compare [(CArray.compare Sorts.Quality.compare, qx, qy); (CArray.compare Univ.Level.compare, ux, uy)])

let uinstancein, uinstanceino, isuinstance, uinstanceout, uinstance =
  let { CD.cin; cino; isc; cout }, uinstance = CD.declare {
    CD.name = "univ-instance";
    doc = "Universes level instance for a universe-polymorphic constant";
    pp = (fun fmt x ->
      let s = Pp.string_of_ppcmds (UVars.Instance.pr Sorts.QVar.raw_pr UnivNames.pr_level_with_global_universes x) in
      Format.fprintf fmt "«%s»" s);
    compare = compare_instances;
    hash = UVars.Instance.hash;
    hconsed = false;
    constants = [];
  } in
  cin, cino, isc, cout, uinstance
;;

let uinstanceina ~loc x = A.mkOpaque ~loc (uinstanceino x)

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

let constc = E.Constants.declare_global_symbol "const"
let indcc = E.Constants.declare_global_symbol "indc"
let indtc = E.Constants.declare_global_symbol "indt"

let gref : Names.GlobRef.t API.Conversion.t = {
  API.Conversion.ty = API.Conversion.TyName "gref";
  pp_doc = (fun fmt () ->
    Format.fprintf fmt "%% Global objects: inductive types, inductive constructors, definitions@\n";
    Format.fprintf fmt "kind gref type.@\n";
    Format.fprintf fmt "type const constant -> gref. %% Nat.add, List.append, ...@\n";
    Format.fprintf fmt "type indt inductive -> gref. %% nat, list, ...@\n";
    Format.fprintf fmt "type indc constructor -> gref. %% O, S, nil, cons, ...@\n";
    );
  pp = (fun fmt x ->
    Format.fprintf fmt "«%a»" Pp.pp_with (Printer.pr_global x));
  embed = (fun ~depth state -> function
    | GlobRef.IndRef i -> state, E.mkApp indtc (inductivein i) [], []
    | GlobRef.ConstructRef c -> state, E.mkApp indcc (constructorin c) [], []
    | GlobRef.VarRef v -> state, E.mkApp constc (constantin (Variable v)) [], []
    | GlobRef.ConstRef c -> state, E.mkApp constc (constantin (Constant c)) [], []
    );
  readback = (fun ~depth state t ->
    match E.look ~depth t with
    | E.App(c,t,[]) when c == indtc ->
        begin match E.look ~depth t with
        | E.CData d when isinductive d -> state, GlobRef.IndRef (inductiveout d), []
        | _ -> raise API.Conversion.(TypeErr(TyName"inductive",depth,t)); end
    | E.App(c,t,[]) when c == indcc ->
        begin match E.look ~depth t with
        | E.CData d when isconstructor d -> state, GlobRef.ConstructRef (constructorout d), []
        | _ -> raise API.Conversion.(TypeErr(TyName"constructor",depth,t)); end
    | E.App(c,t,[]) when c == constc ->
        begin match E.look ~depth t with
        | E.CData d when isconstant d ->
            begin match constantout d with
            | Variable v -> state, GlobRef.VarRef v, []
            | Constant v -> state, GlobRef.ConstRef v, [] end
        | _ -> raise API.Conversion.(TypeErr(TyName"constant",depth,t)); end
    | _ -> raise API.Conversion.(TypeErr(TyName"gref",depth,t));
  );
}

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
let pglobalc  = E.Constants.declare_global_symbol "pglobal"

module GrefCache = Hashtbl.Make(struct
  type t = GlobRef.t
  let equal = GlobRef.SyntacticOrd.equal
  let hash = GlobRef.SyntacticOrd.hash
end)
let cache = GrefCache.create 13

let assert_in_coq_gref_consistent ~poly gr =
  match Global.is_polymorphic gr, poly with
  | true, true -> ()
  | false, false -> ()
  | true, false ->
    U.type_error Printf.(sprintf "Universe polymorphic gref %s used with the 'global' term constructor" (GROrd.show gr))
  | false, true ->
    U.type_error Printf.(sprintf "Non universe polymorphic gref %s used with the 'pglobal' term constructor" (GROrd.show gr))
;;

let assert_in_elpi_gref_consistent ~poly gr =
  match Global.is_polymorphic gr, poly with
  | true, true -> ()
  | false, false -> ()
  | true, false ->
    U.anomaly Printf.(sprintf "Universe polymorphic gref %s used with the 'global' term constructor" (GROrd.show gr))
  | false, true ->
    U.anomaly Printf.(sprintf "Non universe polymorphic gref %s used with the 'pglobal' term constructor" (GROrd.show gr))
;;


let in_elpi_gr ~depth s r =
  assert_in_elpi_gref_consistent ~poly:false r;
  try
    GrefCache.find cache r
  with Not_found ->
    let s, t, gl = gref.API.Conversion.embed ~depth s r in
    assert (gl = []);
    let x = E.mkAppGlobal globalc t [] in
    GrefCache.add cache r x;
    x

let in_elpiast_gref ~loc r =
  match r with
  | GlobRef.IndRef i -> A.mkAppGlobal ~loc indtc (inductiveina ~loc i) []
  | GlobRef.ConstructRef c -> A.mkAppGlobal ~loc indcc (constructorina ~loc c) []
  | GlobRef.VarRef v -> A.mkAppGlobal ~loc constc (constantina ~loc (Variable v)) []
  | GlobRef.ConstRef c -> A.mkAppGlobal ~loc constc (constantina ~loc (Constant c)) []

let in_elpiast_gr ~loc r =
  assert_in_elpi_gref_consistent ~poly:false r;
  A.mkAppGlobal ~loc globalc (in_elpiast_gref ~loc r) []

let in_elpi_poly_gr ~depth s r i =
  assert_in_elpi_gref_consistent ~poly:true r;
  let open API.Conversion in
  let s, t, gl = gref.embed ~depth s r in
  assert (gl = []);
  E.mkApp pglobalc t [i]

let in_elpiast_poly_gr ~loc r i =
  assert_in_elpi_gref_consistent ~poly:true r;
  let t = in_elpiast_gref ~loc r in
  A.mkAppGlobal ~loc pglobalc t [i]

let in_elpi_poly_gr_instance ~depth s r i =
  assert_in_elpi_gref_consistent ~poly:true r;
  let open API.Conversion in
  let s, i, gl = uinstance.embed ~depth s i in
  assert (gl = []);
  in_elpi_poly_gr ~depth s r i

let in_elpiast_poly_gr_instance ~loc r i =
  assert_in_elpi_gref_consistent ~poly:true r;
  let i = uinstanceina ~loc i in
  in_elpiast_poly_gr ~loc r i
  
let in_coq_gref ~depth ~origin ~failsafe s t =
  try
    let s, t, gls = gref.API.Conversion.readback ~depth s t in
    assert_in_coq_gref_consistent ~poly:false t;
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

let in_elpiast_lam ~loc n s t =
  A.mkAppGlobal ~loc lamc (in_elpiast_name ~loc n) [s;A.mkLam ~loc (name_of_name n) t]

let prodc  = E.Constants.declare_global_symbol "prod"
let in_elpi_prod n s t = E.mkApp prodc (in_elpi_name n) [s;E.mkLam t]
let in_elpiast_prod ~loc n s t =
  A.mkAppGlobal ~loc prodc (in_elpiast_name ~loc n) [s;A.mkLam ~loc (name_of_name n) t]

let letc   = E.Constants.declare_global_symbol "let"
let in_elpi_let n b s t = E.mkApp letc (in_elpi_name n) [s;b;E.mkLam t]
let in_elpiast_let ~loc n ~ty:s ~bo:b t =
  A.mkAppGlobal ~loc letc (in_elpiast_name ~loc n) [s;b;A.mkLam ~loc (name_of_name n) t]

(* other *)
let appc   = E.Constants.declare_global_symbol "app"

let in_elpi_app_Arg ~depth hd args = E.mkAppMoreArgs ~depth hd args

let flatten_appc ~depth hd (args : E.term list) =
  if E.isApp ~depth hd then
  match E.look ~depth hd with
  | E.App(c,x,[]) when c == appc ->
      E.mkApp appc (U.list_to_lp_list (U.lp_list_to_list ~depth x @ args)) []
  | _ -> 
    E.mkApp appc (U.list_to_lp_list (hd :: args)) []
  else
    E.mkApp appc (U.list_to_lp_list (hd :: args)) []

let in_elpi_appl ~depth hd (args : E.term list) =
  if args = [] then hd
  else flatten_appc ~depth hd args

let flatten_appc_ast ~loc hd args =
  match hd with
  | { A.it = A.App(g,c,x,[]); loc } when API.Ast.Name.is_global c appc ->
      A.mkAppGlobal ~loc appc (A.ne_list_to_lp_list (A.lp_list_to_list x @ args)) []
  | { loc } -> A.mkAppGlobal ~loc appc (A.ne_list_to_lp_list (hd :: args)) []
  
let in_elpiast_appl ~loc hd args =
  if args = [] then hd
  else flatten_appc_ast ~loc hd args


let in_elpi_app ~depth hd (args : E.term array) =
  in_elpi_appl ~depth hd (Array.to_list args)

let matchc = E.Constants.declare_global_symbol "match"

let in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs =
  E.mkApp matchc t [rt; U.list_to_lp_list bs]

let in_elpiast_match ~loc t rt bs =
  A.mkAppGlobal ~loc matchc t [rt;A.list_to_lp_list ~loc bs]

let fixc   = E.Constants.declare_global_symbol "fix"

let in_elpi_fix name rno ty bo =
  E.mkApp fixc (in_elpi_name name) [CD.of_int rno; ty; E.mkLam bo]

let in_elpiast_fix ~loc n rno ty bo =
  A.mkAppGlobal ~loc fixc (in_elpiast_name ~loc n) [A.mkOpaque ~loc @@ CD.int.cino rno; ty; A.mkLam ~loc (name_of_name n) bo]
  
let primitivec   = E.Constants.declare_global_symbol "primitive"


type pstring = Pstring.t
let pp_pstring = Pstring.to_string
let eC_mkString = EC.mkString

type primitive_value =
  | Uint63 of Uint63.t
  | Float64 of Float64.t
  | Pstring of pstring
  | Projection of Projection.t

let ui63c = E.Constants.declare_global_symbol "uint63"
let fl64c = E.Constants.declare_global_symbol "float64"
let pstrc = E.Constants.declare_global_symbol "pstring"
let projc = E.Constants.declare_global_symbol "proj"

let uint63ina ~loc x =     A.mkAppGlobal ~loc primitivec (A.mkAppGlobal ~loc ui63c (A.mkOpaque ~loc (uint63c.cino x)) []) []
let float64ina ~loc x =    A.mkAppGlobal ~loc primitivec (A.mkAppGlobal ~loc fl64c (A.mkOpaque ~loc (float64c.cino x)) []) []
let projectionina ~loc p =
  let n = Names.Projection.(arg p + npars p) in
  A.mkAppGlobal ~loc primitivec (A.mkAppGlobal ~loc projc
    (A.mkOpaque ~loc (projectionc.cino p)) [A.mkOpaque ~loc @@ CD.int.cino n]) []
let pstringina ~loc x =    A.mkAppGlobal ~loc primitivec (A.mkAppGlobal ~loc pstrc (A.mkOpaque ~loc (pstringc.cino x)) []) []

let primitive_value : primitive_value API.Conversion.t =
  let module B = Rocq_elpi_utils in
  let open API.AlgebraicData in  declare {
  ty = API.Conversion.TyName "primitive-value";
  doc = "Primitive values";
  pp = (fun fmt -> function
    | Uint63 i -> Format.fprintf fmt "%s" (Uint63.to_string i)
    | Float64 f -> Format.fprintf fmt "%s" (Float64.to_string f)
    | Pstring s -> Format.fprintf fmt "%s" (pp_pstring s)
    | Projection p -> Format.fprintf fmt "%s" (Projection.to_string p));
  constructors = [
    K("uint63","unsigned integers over 63 bits",A(B.uint63,N),
      B (fun x -> Uint63 x),
      M (fun ~ok ~ko -> function Uint63 x -> ok x | _ -> ko ()));
    K("float64","double precision foalting points",A(B.float64,N),
      B (fun x -> Float64 x),
      M (fun ~ok ~ko -> function Float64 x -> ok x | _ -> ko ()));
    K("pstring","primitive string",A(B.pstring,N),
      B (fun x -> Pstring x),
      M (fun ~ok ~ko -> function Pstring x -> ok x | _ -> ko ()));
    K("proj","primitive projection",A(B.projection,A(API.BuiltInData.int,N)),
      B (fun p n -> Projection p),
      M (fun ~ok ~ko -> function Projection p -> ok p Names.Projection.(arg p + npars p) | _ -> ko ()));
  ]
} |> API.ContextualConversion.(!<)
  
let in_elpi_primitive ~depth state i =
  let state, i, _ = primitive_value.API.Conversion.embed ~depth state i in
  state, E.mkApp primitivec i []
 
let in_elpiast_primitive ~loc = function
  | Uint63 i -> uint63ina ~loc i
  | Float64 f -> float64ina ~loc f
  | Pstring s -> pstringina ~loc s
  | Projection p -> projectionina ~loc p

let in_elpi_primitive_value ~depth state = function
| C.Int i ->    in_elpi_primitive ~depth state (Uint63 i)
| C.Float f ->  in_elpi_primitive ~depth state (Float64 f)
| C.String s -> in_elpi_primitive ~depth state (Pstring s)
| C.Array _ -> nYI "HOAS for persistent arrays"
| (C.Fix _ | C.CoFix _ | C.Lambda _ | C.App _ | C.Prod _ | C.Case _ | C.Cast _ | C.Construct _ | C.LetIn _ | C.Ind _ | C.Meta _ | C.Rel _ | C.Var _ | C.Proj _ | C.Evar _ | C.Sort _ | C.Const _) -> assert false

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : Evd.evar_map -> elpi *************************************** *)

module CoqEngine_HOAS : sig 

  val show_coq_engine : ?with_univs:bool -> coq_engine -> string

  val engine : coq_engine S.component

  val from_env_sigma : Environ.env -> Evd.evar_map -> coq_engine

  (* when the env changes under the hood, we can adapt sigma or drop it but keep
     its constraints *)
  val from_env_keep_univ_of_sigma :  uctx:Univ.ContextSet.t -> env0:Environ.env -> env:Environ.env -> Evd.evar_map -> coq_engine
  val from_env_keep_univ_and_sigma : uctx:Univ.ContextSet.t -> env0:Environ.env -> env:Environ.env -> Evd.evar_map -> coq_engine

end = struct

 let pp_coq_engine ?with_univs fmt { sigma } =
   Format.fprintf fmt "%a" Pp.pp_with (Termops.pr_evar_map ?with_univs None (Global.env()) sigma)

let show_coq_engine ?with_univs e = Format.asprintf "%a" (pp_coq_engine ?with_univs) e

 let from_env_sigma global_env sigma =
   {
     global_env;
     sigma;
   }

 let from_env env = from_env_sigma env (Evd.from_env env)


[%%if coq = "8.20"]
let demote uctx sigma0 env = 
      let uctx = UState.update_sigma_univs (Evd.evar_universe_context sigma0) (Environ.universes env) in
      UState.demote_global_univs env uctx
[%%else]
 let demote uctx sigma0 env =
   UState.demote_global_univs uctx (Evd.evar_universe_context sigma0)
[%%endif]

 let from_env_keep_univ_and_sigma ~uctx ~env0 ~env sigma0 =
   assert(env0 != env);
   let uctx = demote uctx sigma0 env in
   from_env_sigma env (Evd.set_universe_context sigma0 uctx)

let from_env_keep_univ_of_sigma ~uctx ~env0 ~env sigma0 =
   assert(env0 != env);
   let uctx = demote uctx sigma0 env in
   from_env_sigma env (Evd.from_ctx uctx)
 
 let init () =
   from_env (Global.env ())

 let engine : coq_engine S.component =
   S.declare_component ~name:"rocq-elpi:evmap-constraint-type" ~descriptor:interp_state
     ~pp:pp_coq_engine ~init ~start:(fun _ -> init()) ()

end
let () = pre_engine := Some CoqEngine_HOAS.engine
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

  (* should we remove this "unsafe" API? *)
  let host elab s =
    try
      UVElabMap.host elab (S.get UVElabMap.uvmap s)
    with Not_found ->
      UVRawMap.host elab (S.get UVRawMap.uvmap s)
      
  let mem_elpi x s =
    try
      let _ = UVElabMap.host x (S.get UVElabMap.uvmap s) in true
    with Not_found -> try
      let _ = UVRawMap.host x (S.get UVRawMap.uvmap s) in true
    with Not_found ->
      false
  [@@ocaml.warning "-32"]

  let mem_host x s =
    try
      let _ = UVElabMap.elpi x (S.get UVElabMap.uvmap s) in true
    with Not_found -> try
      let _ = UVRawMap.elpi x (S.get UVRawMap.uvmap s) in true
    with Not_found ->
      false
    
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
  
  exception Return of Evar.t

  let rec morally_same_uvar ~depth uv bo =
    match E.look ~depth bo with
    | E.Lam x -> morally_same_uvar ~depth:(depth+1) uv x
    | E.UnifVar(ev,_) -> F.Elpi.equal ev uv
    | _ -> false

  let host_upto_assignment f s =
    try
      UVElabMap.fold (fun ev _ sol _ ->
        match sol with
        | None -> () (* the fast lookup can only fail if the uvar was instantiated (as is expanded or pruned)*)
        | Some sol ->
            if f ev sol then raise (Return ev) else ())
      (S.get UVElabMap.uvmap s) ();
      raise Not_found
    with Return a -> a

  let host_failsafe elab s =
    try
      UVElabMap.host elab (S.get UVElabMap.uvmap s)
    with Not_found ->
    try
      UVRawMap.host elab (S.get UVRawMap.uvmap s)
    with Not_found ->
      host_upto_assignment (fun evar bo -> morally_same_uvar ~depth:0 elab bo) s

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

let sortc  = E.Constants.declare_global_symbol "sort"
let typc   = E.Constants.declare_global_symbol "typ"  

let force_level_of_universe state u =
  match Univ.Universe.level u with
  | Some lvl -> state, lvl, u, Sorts.sort_of_univ u
  | None ->
      let state, (l,v) = new_univ_level_variable state in
      let w = Sorts.sort_of_univ v in
      add_universe_constraint state (constraint_eq (Sorts.sort_of_univ u) w), l, v, w

let purge_algebraic_univs_sort state s =
  let sigma = (S.get engine state).sigma in
  match EConstr.ESorts.kind sigma s with
  | Sorts.Type u | Sorts.QSort (_ , u) ->
      let state, _, _, s = force_level_of_universe state u in
      state, s
  | x -> state, x

let in_elpi_flex_sort t = E.mkApp sortc (E.mkApp typc t []) []
let in_elpiast_flex_sort ~loc t =
  A.mkAppGlobal ~loc sortc (A.mkAppGlobal ~loc typc t []) []

let sort = { sort with API.Conversion.embed = (fun ~depth state s ->
  let state, s = purge_algebraic_univs_sort state (EConstr.ESorts.make s) in
  sort.API.Conversion.embed ~depth state s) }

let in_elpi_sort ~depth state s =
  let state, s, gl = sort.API.Conversion.embed ~depth state s in
  assert(gl=[]);
  state, E.mkApp sortc s []

let in_elpiast_sort ~loc state s =
  A.mkAppGlobal ~loc sortc (ast_sort ~loc s) []
 

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : EConstr.t -> elpi ******************************************* *)

let get_sigma s = (S.get engine s).sigma
let update_sigma s f = (S.update engine s (fun e -> { e with sigma = f e.sigma }))
let get_global_env s = (S.get engine s).global_env

let declare_evc = E.Constants.declare_global_symbol "declare-evar"
let rm_evarc = E.Constants.declare_global_symbol "rm-evar"

(* We extend extra_goal with two /delayed/ actions: declaring a new evear to
   elpi and removing a previously declared one. When the actions happen in
   the same FFI call, we cancel them out, see set_extra_goals_postprocessing *)
type API.Conversion.extra_goal +=
  | DeclareEvar of Evar.t * int * F.Elpi.t * F.Elpi.t
  | RmEvar of Evar.t * E.term * E.term

let rec cancel_opposites acc removals = function
  | [] -> []
  | DeclareEvar(e,_,_,_) :: rest when Evar.Set.mem e removals ->
      debug Pp.(fun () -> str "cancelling extra_goal for " ++ Evar.print e);
      cancel_opposites (Evar.Set.add e acc) removals rest
  | RmEvar(e,_,_) :: rest when Evar.Set.mem e acc -> cancel_opposites acc removals rest
  | x :: rest -> x :: cancel_opposites acc removals rest

let rec removals_of acc = function
  | [] -> acc
  | RmEvar(e,_,_) :: rest -> removals_of (Evar.Set.add e acc) rest
  | _ :: rest -> removals_of acc rest

let pp_coq_ctx { env } state =
  try
    Printer.pr_named_context_of env (get_sigma state)
  with e when CErrors.noncritical e ->
    Pp.(str "error in printing: " ++ str (Printexc.to_string e))

let module_inline_core = let open API.AlgebraicData in let open Declaremods in declare {
  ty = API.Conversion.TyName "coq.inline";
  doc = "Coq Module inline directive";
  pp = (fun fmt -> function
    | NoInline -> Format.fprintf fmt "NoInline"
    | DefaultInline -> Format.fprintf fmt "DefaultInline"
    | InlineAt x -> Format.fprintf fmt "InlineAt %d" x);
  constructors = [
    K("coq.inline.no", "Coq's [no inline] (aka !)",N,
      B NoInline,
      M (fun ~ok ~ko -> function NoInline -> ok | _ -> ko ()));
    K("coq.inline.default","The default, can be omitted",N,
      B DefaultInline,
      M (fun ~ok ~ko -> function DefaultInline -> ok | _ -> ko ()));
    K("coq.inline.at","Coq's [inline at <num>]",A(API.BuiltInData.int,N),
      B (fun x -> InlineAt x),
      M (fun ~ok ~ko -> function InlineAt x -> ok x | _ -> ko ()));
  ]
} |> API.ContextualConversion.(!<)
let module_inline_unspec = Elpi.Builtin.unspec module_inline_core
let module_inline_default = { module_inline_unspec with
  API.Conversion.pp = (fun fmt x ->
    module_inline_unspec.API.Conversion.pp fmt (Elpi.Builtin.Given x));
  API.Conversion.embed = (fun ~depth state x ->
    module_inline_unspec.API.Conversion.embed ~depth state (Elpi.Builtin.Given x));
  API.Conversion.readback = (fun ~depth state x ->
     match module_inline_unspec.API.Conversion.readback ~depth state x with
     | state, Elpi.Builtin.Given x, gls -> state,x,gls
     | state, Elpi.Builtin.Unspec, gls -> state,Declaremods.DefaultInline,gls)
}

let reduction_flags = let open API.OpaqueData in let open RedFlags in declare {
  name = "coq.redflags";
  doc = "Set of flags for lazy, cbv, ... reductions";
  pp = (fun fmt (x : RedFlags.reds) -> Format.fprintf fmt "TODO");
  compare = Stdlib.compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [
    "coq.redflags.all",           all          ;
    "coq.redflags.allnolet",      allnolet     ;
    "coq.redflags.beta",          beta         ;
    "coq.redflags.betadeltazeta", betadeltazeta;
    "coq.redflags.betaiota",      betaiota     ;
    "coq.redflags.betaiotazeta",  betaiotazeta ;
    "coq.redflags.betazeta",      betazeta     ;
    "coq.redflags.delta",         delta        ;
    "coq.redflags.zeta",          zeta         ;
    "coq.redflags.nored",         nored        ;
];
}

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
  let get_module_inline_option name =
    try
      let t, depth = API.Data.StrMap.find name map in
      let _, b, _ = module_inline_core.API.Conversion.readback ~depth state t in
      b
    with Not_found -> Declaremods.NoInline in
  let get_pair_option fst snd name =
    try
      let t, depth = API.Data.StrMap.find name map in
      let _, b, _ = Elpi.Builtin.(pair (unspec fst) (unspec snd)).API.Conversion.readback ~depth state t in
      Some b
    with Not_found -> None in
  let get_uinstance_option name =
    match API.Data.StrMap.find_opt name map with
    | Some (t, depth) when t <> E.mkDiscard -> begin
      match E.look ~depth t with
      | E.UnifVar (head, args) -> VarInstance (head, args, depth)
      | _ ->
        let _, i, gl = uinstance.Elpi.API.Conversion.readback ~depth state t in
        assert (gl = []);
        ConcreteInstance i
    end
    | _ -> NoInstance in
  let empty2none = function Some "" -> None | x -> x in
  let deprecation = function
    | None -> None
    | Some(since,note) ->
        let since = unspec2opt since |> empty2none in
        let note = unspec2opt note |> empty2none in
        Some { Deprecation.since; note } in
  let warn = function
    | None -> []
    | Some(cats,note) ->
        let cats = unspec2opt cats |> empty2none in
        let note = unspec2opt note |> empty2none in
        Option.cata (fun note -> [make_warn ~note ?cats ()]) [] note in      
  let get_universe_decl () =
    match API.Data.StrMap.find_opt "coq:udecl-cumul" map, API.Data.StrMap.find_opt "coq:udecl" map with
    | None, None -> NotUniversePolymorphic
    | Some _, Some _ -> err Pp.(str"Conflicting attributes: @udecl! and @udecl-cumul! (or @univpoly! and @univpoly-cumul!)")
    | Some (t,depth), None ->
        let _, ud, gl = universe_decl_cumul.Elpi.API.Conversion.readback ~depth state t in
        assert (gl = []);
        Cumulative ud
    | None, Some (t,depth) ->
      let _, ud, gl = universe_decl.Elpi.API.Conversion.readback ~depth state t in
      assert (gl = []);
      NonCumulative ud
    in
  let get_redflags_option () =
    match API.Data.StrMap.find_opt "coq:redflags" map with
    | None -> None
    | Some (t,depth) ->
      let _, rd, gl = reduction_flags.Elpi.API.Conversion.readback ~depth state t in
      assert (gl = []);
      Some rd in
    let depr = deprecation @@ get_pair_option API.BuiltInData.string API.BuiltInData.string "coq:deprecation" in
    let warn = warn @@ get_pair_option API.BuiltInData.string API.BuiltInData.string "coq:warn" in
    let hoas_holes =
      begin match get_bool_option "HOAS:holes" with
      | None -> None
      | Some true -> Some Heuristic
      | Some false -> Some Verbatim end in
    let local = locality @@ get_string_option "coq:locality" in
    let primitive = get_bool_option "coq:primitive" in
    let failsafe = false in
    let ppwidth = ppwidth @@ get_int_option "coq:ppwidth" in
    let pp = pp @@ get_string_option "coq:pp" in
    let pplevel = pplevel @@ get_int_option "coq:pplevel" in
    let using = get_string_option "coq:using" in
    let inline = get_module_inline_option "coq:inline" in
    let uinstance = get_uinstance_option "coq:uinstance" in
    let universe_decl = get_universe_decl () in
    let reversible = get_bool_option "coq:reversible" in
    let no_tc = get_bool_option "coq:no_tc" in
    let keepunivs = get_bool_option "coq:keepunivs" in
    let redflags = get_redflags_option () in
    make_options ~hoas_holes ~local ~warn ~depr ~primitive ~failsafe ~ppwidth
      ~pp ~pplevel ~using ~inline ~uinstance ~universe_decl ~reversible ~keepunivs
      ~redflags ~no_tc

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
    names = Environ.named_context env |> Context.Named.to_vars;
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
  let evi = Evd.find_undefined sigma k in
  let info = Evarutil.nf_evar_info sigma evi in
  let filtered_hyps = Evd.evar_filtered_hyps info in
  let ctx = EC.named_context_of_val filtered_hyps in
  let ctx = ctx |> CList.filter (fun x ->
    not(CList.mem_f Id.equal (Declaration.get_id x) section)) in
  Evd.evar_concl info, ctx, Environ.reset_with_named_context filtered_hyps env

(* ******************************************* *)
(*  <---- depth ---->                          *)
(*  proof_ctx |- pis \ t                       *)
(* ******************************************* *)
type hyp = { ctx_entry : E.term; depth : int }

let declc = E.Constants.declare_global_symbol "decl"
let defc = E.Constants.declare_global_symbol "def"
let evarc = E.Constants.declare_global_symbol "evar"

let mk_pi rest =
  E.mkApp E.Constants.pic (E.mkLam rest) []

let mk_pi_arrow hyp rest =
  mk_pi (E.mkApp E.Constants.implc hyp [rest])

let mk_decl ~depth name ~ty =
  E.mkApp declc E.(mkConst depth) [in_elpi_name name; ty]

let in_elpiast_decl ~loc ~v name ~ty =
  A.mkAppGlobal ~loc declc v [in_elpiast_name ~loc name;ty]

let mk_def ~depth name ~bo ~ty =
  E.mkApp defc E.(mkConst depth) [in_elpi_name name; ty; bo]

let in_elpiast_def ~loc ~v name ~ty ~bo =
  A.mkAppGlobal ~loc defc v [in_elpiast_name ~loc name;ty;bo]
  
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
         let args = Evd.expand_existential sigma (k, args) in
         let argno = List.length args - coq_ctx.section_len in
         if (argno < 0) then 
            nYI "constr2lp: cleared section variables";
         let args = CList.firstn argno args in
         let state, args = CList.fold_left_map (aux ~depth env) state args in
         state, E.mkUnifVar elpi_uvk ~args:(List.rev args) state
    | C.Sort s -> in_elpi_sort ~depth state (EC.ESorts.kind sigma s)
    | C.Cast (t,_,ty0) ->
         let state, t = aux ~depth env state t in
         let state, ty = aux ~depth env state ty0 in
         let env = EConstr.push_rel Context.Rel.Declaration.(LocalAssum(Context.make_annot Anonymous relevant,ty0)) env in
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
    | C.Const(c,i) when Global.is_polymorphic (G.ConstRef c) ->
         state, in_elpi_poly_gr_instance ~depth state (G.ConstRef c) (EC.EInstance.kind sigma i)
    | C.Const(c,i) ->
         state, in_elpi_gr ~depth state (G.ConstRef c)
    | C.Ind (ind, i) when Global.is_polymorphic (G.IndRef ind) ->
         state, in_elpi_poly_gr_instance ~depth state (G.IndRef ind) (EC.EInstance.kind sigma i)
    | C.Ind (ind, i) ->
         state, in_elpi_gr ~depth state (G.IndRef ind)
    | C.Construct (construct, i) when Global.is_polymorphic (G.ConstructRef construct) ->
         let gref = G.ConstructRef construct in
         state, in_elpi_poly_gr_instance ~depth state gref (EC.EInstance.kind sigma i)
    | C.Construct (construct, i) ->
         state, in_elpi_gr ~depth state (G.ConstructRef construct)
    | C.Case(ci, u, pms, rt, iv, t, bs) ->
         let (_, (rt,_), _, t, bs) = EConstr.expand_case env sigma (ci, u, pms, rt, iv, t, bs) in
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
    | C.Proj(p,_,t) ->
         let state, t = aux ~depth env state t in
         let state, p = in_elpi_primitive ~depth state (Projection p) in
         state, in_elpi_app ~depth p [|t|]
    | C.Fix _ -> nYI "HOAS for mutual fix"
    | C.CoFix _ -> nYI "HOAS for cofix"
    | x -> in_elpi_primitive_value ~depth state x
  in
  debug Pp.(fun () ->
      str"term2lp: depth=" ++ int depth ++
      str " ctx=" ++ pp_coq_ctx coq_ctx state ++
      str " term=" ++Printer.pr_econstr_env (get_global_env state) (get_sigma state) t);
  let state, t = aux ~depth coq_ctx.env state t in
  debug Pp.(fun () -> str"term2lp (out): " ++ str (pp2string (P.term depth) t));
  state, t, !gls

and under_coq2elpi_ctx ~calldepth state ctx ?(mk_ctx_item=fun decl -> mk_pi_arrow decl) kont =
  let open Context.Named.Declaration in
  let gls = ref [] in
  let rec aux i ~depth coq_ctx hyps state = function
    | [] -> state, coq_ctx, hyps
    | LocalAssum (Context.{binder_name=coq_name}, ty) as e :: rest ->
        let name = Name coq_name in
        let state, ty, gls_ty = constr2lp coq_ctx ~calldepth ~depth:(depth+1) state ty in
        gls := gls_ty @ !gls;
        let hyp = mk_decl ~depth name ~ty in
        let hyps = { ctx_entry = hyp ; depth = depth + 1 } :: hyps in
        let coq_ctx = push_coq_ctx_proof depth e coq_ctx in
        aux (succ i) ~depth:(depth+1) coq_ctx hyps state rest
      | LocalDef (Context.{binder_name=coq_name},bo,ty) as e :: rest ->
        let name = Name coq_name in
        let state, ty, gls_ty = constr2lp coq_ctx ~calldepth ~depth:(depth+1) state ty in
        let state, bo, gls_bo = constr2lp coq_ctx ~calldepth ~depth:(depth+1) state bo in
        gls := gls_ty @ gls_bo @ !gls;
        let hyp = mk_def ~depth name ~bo ~ty in
        let hyps = { ctx_entry = hyp ; depth = depth + 1 } :: hyps in
        let coq_ctx = push_coq_ctx_proof depth e coq_ctx in
        aux (succ i) ~depth:(depth+1) coq_ctx hyps state rest
  in
  let state, coq_ctx, hyps =
      let state, coq_ctx, hyps =
        aux 0 ~depth:calldepth (mk_coq_context ~options:(default_options ()) state) [] state (List.rev ctx) in
      state, coq_ctx, hyps in
  let state, t, gls_t = kont coq_ctx hyps ~depth:(calldepth + List.length hyps) state in
  gls := gls_t @ !gls;
  let t = List.fold_left (fun rest hyp -> mk_ctx_item hyp.ctx_entry rest) t hyps in
  state, t, !gls
  
and in_elpi_evar_concl evar_concl ~raw_uvar elpi_evk coq_ctx hyps ~calldepth ~depth state =
  let state, evar_concl, gls_evar_concl = constr2lp coq_ctx ~calldepth ~depth state evar_concl in
  let args = CList.init coq_ctx.proof_len (fun i -> E.mkConst @@ i + calldepth) in
  debug Pp.(fun () -> str"in_elpi_evar_concl: moving Ctx down to" ++ int depth);
  let hyps = List.map (fun { ctx_entry; depth = from } ->
    U.move ~from ~to_:depth ctx_entry) hyps in
  state, U.list_to_lp_list hyps,
  (E.mkUnifVar raw_uvar ~args state),
  (E.mkUnifVar elpi_evk ~args state),
  evar_concl, gls_evar_concl

and in_elpi_evar_info ~calldepth ~env ~sigma ctx ~raw_ev:elpi_revk elpi_evk evar_concl state =
  under_coq2elpi_ctx ~mk_ctx_item:(fun _ -> mk_pi) ~calldepth state ctx (fun coq_ctx hyps ~depth state ->
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
    let state = UVMap.add k raw_ev elpi_evk state in
    state, [DeclareEvar(k,calldepth,raw_ev,elpi_evk)]
;;

let rec postprocess_DeclareEvar calldepth k raw_ev elpi_evk state =
  let { sigma; global_env } as e = S.get engine state in
  debug Pp.(fun () -> str"in_elpi_fresh_evar: unknown " ++ Evar.print k ++ str " <-> " ++ str(pp2string (P.term calldepth) (E.mkUnifVar raw_ev ~args:[] state)) ++ cut () ++
    str (UVMap.show state));
  let evar_concl, ctx, _ = info_of_evar ~env:global_env ~sigma ~section:(section_ids global_env) k in
  let state, evar_decl, gls = in_elpi_evar_info ~calldepth ~env:global_env ~sigma ctx ~raw_ev elpi_evk evar_concl state in
  debug Pp.(fun () -> str"in_elpi_fresh_evar: new decl at depth:" ++ int calldepth ++ str" for " ++ Evar.print k ++ str " <-> " ++ str(pp2string (P.term calldepth) (E.mkUnifVar raw_ev ~args:[] state)) ++ cut () ++
    str(pp2string (P.term calldepth) evar_decl));
  let state, gls = generate_actual_goals state gls in
  state, gls @ [API.RawData.RawGoal evar_decl]

and generate_actual_goals state = function
  | [] -> state, []
  (* We reset the UVmap when we change Coq's global state *)
  | DeclareEvar (k,_,_,_) :: rest when not (UVMap.mem_host k state) -> generate_actual_goals state rest

  | DeclareEvar(k,calldepth,raw_ev,elpi_evk) :: rest ->
      let state, gls1 = postprocess_DeclareEvar calldepth k raw_ev elpi_evk state in
      let state, rest = generate_actual_goals state rest in
      state, gls1 @ rest
  | RmEvar (k,raw_ev,ev) :: rest ->
      let state, rest = generate_actual_goals state rest in
      (*let state = UVMap.remove_host k state in*)
      state, API.RawData.RawGoal (E.mkAppGlobalL rm_evarc [raw_ev; ev]) :: rest
  | (API.Conversion.Unify _ | API.RawData.RawGoal _) as x :: xs ->
      let state, xs = generate_actual_goals state xs in
      state, x :: xs
  | _ -> assert false

let prepend_removals l =
  let removals, rest = List.partition (function RmEvar _ -> true | _ -> false) l in
  removals @ rest

let () = E.set_extra_goals_postprocessing ~descriptor:interp_hoas (fun l state ->
  generate_actual_goals state
    (prepend_removals
      (cancel_opposites Evar.Set.empty (removals_of Evar.Set.empty l) l)))

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : elpi -> Constr.t * Evd.evar_map ***************************** *)

let poly_ctx_size_of_gref env gr =
  let open Names.GlobRef in
  match gr with
  | VarRef _ -> 0, 0
  | ConstRef c ->
    let cb = Environ.lookup_constant c env in
    let univs = Declareops.constant_polymorphic_context cb in
    UVars.AbstractContext.size univs
  | IndRef ind ->
    let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
    let univs = Declareops.inductive_polymorphic_context mib in
    UVars.AbstractContext.size univs
  | ConstructRef cstr ->
    let (mib,_ as specif) =
      Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
    let univs = Declareops.inductive_polymorphic_context mib in
    UVars.AbstractContext.size univs

let mk_global state gr inst_opt = S.update_return engine state (fun x ->
  match inst_opt with
  | None ->
      let sigma, t = EConstr.fresh_global x.global_env x.sigma gr in
      let _, i = EConstr.destRef sigma t in
      { x with sigma }, (t, Some (EConstr.EInstance.kind sigma i))
  | Some ui ->
      let expected = poly_ctx_size_of_gref x.global_env gr in
      let actual = UVars.Instance.length ui in
      if not (UVars.eq_sizes expected actual) then begin
        let plen (qlen,ulen) = Pp.(prlist_with_sep (fun () -> str ", ") int [qlen;ulen]) in
        U.type_error Pp.(string_of_ppcmds
          (str"Global reference " ++ Printer.pr_global gr ++
           str " takes a univ-instance of size " ++ plen expected ++
           str " but was given an instance of size " ++ plen actual))
      end;
      let i = EConstr.EInstance.make ui in
      x, (EConstr.mkRef (gr,i), None)
) |> (fun (x,(y,z)) -> x,y,z)

let body_of_constant state c inst_opt = S.update_return engine state (fun x ->
  match
    Global.body_of_constant_body Library.indirect_accessor (Environ.lookup_constant c x.global_env)
  with
  | Some (bo, priv, ctx) ->
     let c, ctx = UnivGen.fresh_global_instance x.global_env (ConstRef c) ?names:inst_opt  in
     let c, inst = Constr.destConst c in
     let bo = Vars.subst_instance_constr inst bo in
     let sigma = Evd.merge_sort_context_set Evd.univ_rigid x.sigma ctx in
     let sigma = match priv with
     | Opaqueproof.PrivateMonomorphic () -> sigma
     | Opaqueproof.PrivatePolymorphic ctx ->
      let ctx = Util.on_snd (Univ.subst_univs_level_constraints (snd (UVars.make_instance_subst inst))) ctx in
      Evd.merge_context_set Evd.univ_rigid sigma ctx
     in
     { x with sigma }, (Some (EConstr.of_constr bo), Some inst)
  | None -> x, (None, None)) |> (fun (x,(y,z)) -> x,y,z)

let evar_arity k state =
  let EvarInfo info = Evd.find (S.get engine state).sigma k in
  let filtered_hyps = Evd.evar_filtered_hyps info in
  List.length (Environ.named_context_of_val filtered_hyps)

(* This is random: u < v /\ u <= FOO.123 /\ FOO.123 <= u ===>
                   u < FOO.123
   even if u is a binder, and FOO.123 is not.
   Hence this is disabled. *)
let minimize_universes state = state (*
  S.update engine state (fun ({ sigma } as x) ->
    { x with sigma = Evd.minimize_universes sigma })
*)

let is_sort ~depth x =
  match E.look ~depth x with
  | E.App(s,_,[]) -> sortc == s
  | _ -> false

let is_prod ~depth x =
  match E.look ~depth x with
  | E.App(s,_,[ty;bo]) when prodc == s ->
    begin match E.look ~depth bo with
    | E.Lam bo -> Some(ty,bo)
    | _ -> None end
  | _ -> None

let is_let ~depth x =
  match E.look ~depth x with
  | E.App(s,_,[ty;d;bo]) when letc == s ->
    begin match E.look ~depth bo with
    | E.Lam bo -> Some(ty,d,bo)
    | _ -> None end
  | _ -> None
  

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
  csts |> CList.find_map_exn (fun ({ E.goal = (depth,concl); context } as cst) ->
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
  csts |> CList.find_map_exn (fun ({ E.goal = (depth,concl); context } as cst) ->
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

module UIM = F.Map(struct
  type t = UVars.Instance.t
  let compare = compare_instances
  let show x = Pp.string_of_ppcmds @@ UVars.Instance.pr Sorts.QVar.raw_pr UnivNames.pr_level_with_global_universes x
  let pp fmt x = Format.fprintf fmt "%a" Pp.pp_with (UVars.Instance.pr Sorts.QVar.raw_pr UnivNames.pr_level_with_global_universes x)
end)
    
let uim = S.declare_component ~name:"rocq-elpi:evar-univ-instance-map" ~descriptor:interp_state
  ~pp:UIM.pp ~init:(fun () -> UIM.empty) ~start:(fun x -> x) ()
    
let in_coq_poly_gref ~depth ~origin ~failsafe s t i =
  let open API.Conversion in
  let uinstance_readback s i t =
    match E.look ~depth i with
    | E.UnifVar (b, args) ->
      let m = S.get uim s in
      begin try
        let u = UIM.host b m in
        s, u, []
      with Not_found ->
        let u, ctx = UnivGen.fresh_global_instance (get_global_env s) t in
        let s = update_sigma s (fun sigma -> Evd.merge_sort_context_set UState.univ_flexible_alg sigma ctx) in
        let u =
          match C.kind u with
          | C.Const (_, u) -> u
          | C.Ind (_, u) -> u
          | C.Construct (_, u) -> u
          | _ -> assert false
        in
        let s = S.update uim s (UIM.add b u) in
        s, u, [API.Conversion.Unify (E.mkUnifVar b ~args s,uinstancein u)]
      end
    | _ -> uinstance.readback ~depth s i
  in
  try
    let s, t, gls1 = gref.readback ~depth s t in
    assert_in_coq_gref_consistent ~poly:true t;
    let s, i, gls2 = uinstance_readback s i t in
    assert (gls1 = []);
    s, t, i, gls2
  with API.Conversion.TypeErr _ ->
    if failsafe then
      s, Coqlib.lib_ref "elpi.unknown_gref", UVars.Instance.empty, []
    else
      let open Pp in
      err ?loc:None @@
        str "The term " ++ str (pp2string (P.term depth) origin) ++
        str " cannot be represented in Coq since its gref or univ-instance part is illformed"


type global_or_pglobal =
  | Global of E.term option
  | PGlobal of E.term option * UVars.Instance.t option
  | NotGlobal
  | Var

let is_global_or_pglobal ~depth t =
  let do_gr x =
    match E.look ~depth x with
    | E.UnifVar _ -> None
    | _ -> Some x in
  let do_ui x =
    match E.look ~depth x with
    | E.CData c when isuinstance c -> Some (uinstanceout c)
    | _ -> None in
  match E.look ~depth t with
  | E.App(c,gr,[]) when c == globalc -> (Global(do_gr gr))
  | E.App(c,gr,[]) when c == pglobalc -> (PGlobal(do_gr gr, None))
  | E.App(c,gr,[ui]) when c == pglobalc -> (PGlobal(do_gr gr, do_ui ui))
  | E.UnifVar _ -> Var
  | _ -> NotGlobal
  

let rec of_elpi_ctx ~calldepth syntactic_constraints depth dbl2ctx state initial_coq_ctx =

  let aux coq_ctx depth state t =
    lp2constr ~calldepth syntactic_constraints coq_ctx ~depth state t
  in
  let of_elpi_ctx_entry id dbl coq_ctx ~depth e state =
    match e with
    | `Decl(name_hint,ty) ->
        debug Pp.(fun () -> str "decl name (hint/actual): " ++ str(pp2string (P.term depth) name_hint) ++ spc () ++ Id.print (Context.binder_name id));
        debug Pp.(fun () -> str "decl ty: " ++ str(pp2string (P.term depth) ty));
        let state, ty, gls = aux coq_ctx depth state ty in
        state, Context.Named.Declaration.LocalAssum(id,ty), gls
    | `Def(name_hint,ty,bo) ->
        debug Pp.(fun () -> str "def name (hint/actual): " ++ str(pp2string (P.term depth) name_hint) ++ spc () ++ Id.print (Context.binder_name id));
        debug Pp.(fun () -> str "def ty: " ++ str(pp2string (P.term depth) ty));
        debug Pp.(fun () -> str "def bo: " ++ str(pp2string (P.term depth) bo));
        let state, ty, gl1 = aux coq_ctx depth state ty in
        let state, bo, gl2 = aux coq_ctx depth state bo in
        state, Context.Named.Declaration.LocalDef(id,bo,ty), gl1 @ gl2
  in
  let of_elpi_ctx_entry_name dbl names ~depth e =
    match e with
    | `Decl(name_hint,_) -> in_coq_fresh_annot_id ~depth ~names dbl name_hint
    | `Def(name_hint,_,_) -> in_coq_fresh_annot_id ~depth ~names dbl name_hint
  in
  let rec build_ctx_entry coq_ctx state gls = function
    | [] -> state, coq_ctx, List.(concat (rev gls))
    | (i,id,d,e) :: rest ->
      debug Pp.(fun () -> str "<<< context entry for DBL "++ int i ++ str" at depth" ++ int d);
      let state, e, gl1 = of_elpi_ctx_entry id i coq_ctx ~depth:d e state in
      debug Pp.(fun () -> str "<<< context entry for DBL "++ int i ++ str" at depth" ++ int d);
      let coq_ctx = push_coq_ctx_proof i e coq_ctx in
      build_ctx_entry coq_ctx state (gl1 :: gls) rest
  in
  (* we go from the bottom (most recent addition) to the top in order to
     give precedence to the name recently introduced *)
  let rec ctx_entries_names names i =
    if i < 0 then []
    else (* context entry for the i-th variable *)
      if not (Int.Map.mem i dbl2ctx)
      then ctx_entries_names names (i - 1)
      else
        let d, e = Int.Map.find i dbl2ctx in
        let id = of_elpi_ctx_entry_name i names ~depth:d e in
        let names = Id.Set.add (Context.binder_name id) names in
        (i,id,d,e) :: ctx_entries_names names (i - 1)
  in
    ctx_entries_names Id.Set.empty (depth-1) |>
    List.rev |> (* we need to readback the context from top to bottom *)
    build_ctx_entry initial_coq_ctx state []

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
      let state, u, gsl = sort.API.Conversion.readback ~depth state p in
      state, EC.mkSort (EC.ESorts.make u), gsl
 (* constants *)
  | E.App(c,d,[]) when globalc == c ->
     let state, gr = in_coq_gref ~depth ~origin:t ~failsafe:coq_ctx.options.failsafe state d in
     begin match gr with
     | G.VarRef x -> state, EC.mkVar x, []
     | G.ConstRef x -> state, EC.UnsafeMonomorphic.mkConst x, []
     | G.ConstructRef x -> state, EC.UnsafeMonomorphic.mkConstruct x, []
     | G.IndRef x -> state, EC.UnsafeMonomorphic.mkInd x, []
     end
  | E.App(c,d,[i]) when pglobalc == c ->
    let state, gr, i, gls =
      in_coq_poly_gref ~depth ~origin:t ~failsafe:coq_ctx.options.failsafe state d i in
    begin match gr with
    | G.VarRef x -> assert false
    | G.ConstRef x -> state, EC.mkConstU (x, EC.EInstance.make i), gls
    | G.ConstructRef x -> state, EC.mkConstructU (x, EC.EInstance.make i), gls
    | G.IndRef x -> state, EC.mkIndU (x, EC.EInstance.make i), gls
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
        err Pp.(str"lp2constr: wrong constant: " ++ int n ++ str " " ++ str (E.Constants.show n))

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
                  (* TODO handle relevance *)
                  state, EC.mkApp (EC.mkProj (p,relevant,i),Array.of_list xs), gls @ gl1 @ gl2
              | _ ->  err Pp.(str"not a primitive projection:" ++ str (E.Constants.show c))
              end
          | x, _ ->
              let state, x, gl1 = aux ~depth state (E.kool x) in
              let state, xs, gl2 = API.Utils.map_acc (aux ~depth ~on_ty:false) state xs in
              state, EC.mkApp (x, Array.of_list xs), gl1 @ gl2
          end
       | _ -> U.type_error "the app term constructor expects a non empty list"
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
            C.LetStyle in
        let ci_pp_info = unknown_ind_cinfo.Constr.ci_pp_info in
        { unknown_ind_cinfo with Constr.ci_pp_info} in
      let { sigma } = S.get engine state in
      begin match ind with
      | `SomeInd ind ->
          let ci = Inductiveops.make_case_info (get_global_env state) ind C.RegularStyle in
          state, EC.mkCase (EConstr.contract_case (get_global_env state) sigma (ci,(rt,relevant),C.NoInvert,t,Array.of_list bt)), gl1 @ gl2 @ gl3
      | `None -> CErrors.anomaly Pp.(str "non dependent match on unknown, non singleton, inductive")
      | `SomeTerm (n,rt) ->
          let ci = default_case_info () in
          let b =
            match bt with
            | [t] -> [||], t
            | _ -> assert false in
          state, EConstr.mkCase (ci,EConstr.EInstance.empty,[||],(([|n|],rt),relevant),Constr.NoInvert,t,[|b|]), gl1 @ gl2 @ gl3
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
      | Pstring s -> state, eC_mkString s, gls
      | Projection p -> state, EC.UnsafeMonomorphic.mkConst (Names.Projection.constant p), gls
      end

  (* evar *)
  | E.UnifVar (elpi_evk,args) as x ->
      debug Pp.(fun () ->
        str"lp2term: evar: calldepth:" ++ int calldepth ++ str" " ++
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
          let { sigma } = S.get engine state in
          let all_args = args @ section_args in
          let nargs = List.length all_args in
          if nargs > arity then
            let args1, args2 = CList.chop (nargs - arity) all_args in
            EC.mkApp(EC.mkLEvar sigma (ext_key, args2),
                       CArray.rev_of_list args1)
          else
            EC.mkLEvar sigma (ext_key, all_args) in

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

        debug Pp.(fun () -> str"lp2term: evar: unknown: calldepth:" ++ int calldepth ++ str " " ++ str(F.Elpi.show elpi_evk));

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
            let u = E.mkUnifVar elpi_evk ~args:[] state in
            debug Pp.(fun () ->
              str"evar: unknown: restriction assignment: "
              ++ str (pp2string (P.term calldepth) u)
              ++ str " = "
              ++ str (pp2string (P.term calldepth) ass));
            API.Conversion.Unify(u ,ass) in
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
    let ty_key, _ = EConstr.destEvar sigma ty in
    if on_ty then
      { e with sigma }, (ty_key, None)
    else
      let sigma, t = Evarutil.new_evar ~typeclass_candidate:false ~naming:(Namegen.IntroFresh (Names.Id.of_string "e")) env sigma ty in
      let t_key, _ = EConstr.destEvar sigma t in
      { e with sigma }, (t_key, Some ty_key)) in
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

let set_sigma state sigma = S.update engine state (fun x -> { x with sigma })

(* We reset the evar map since it depends on the env in which it was created *)
let grab_global_env ~uctx state =
  let env0 = get_global_env state in
  let env = Global.env () in
  if env == env0 then state
  else
    if Environ.universes env0 == Environ.universes env then
      let state = S.set engine state (CoqEngine_HOAS.from_env_sigma  env (get_sigma state)) in
      state  
    else
      let state = S.set engine state (CoqEngine_HOAS.from_env_keep_univ_and_sigma ~uctx ~env0 ~env (get_sigma state)) in
      state
let grab_global_env_drop_univs_and_sigma state =
  let env0 = get_global_env state in
  let env = Global.env () in
  if env == env0 then state
  else
    let state = S.set engine state (CoqEngine_HOAS.from_env_sigma env (Evd.from_env env)) in
    let state = UVMap.empty state in
    state

let grab_global_env_drop_sigma state =
  let env0 = get_global_env state in
  let env = Global.env () in
  if env == env0 then state
  else begin
    let sigma = get_sigma state in
    let ustate = Evd.evar_universe_context sigma in
    let state = S.set engine state (CoqEngine_HOAS.from_env_sigma env (Evd.from_ctx ustate)) in
    let state = UVMap.empty state in
    state
  end
    
let grab_global_env_drop_sigma_keep_univs ~uctx state =
  let env0 = get_global_env state in
  let env = Global.env () in
  if env == env0 then state
  else begin
    let sigma = get_sigma state in
    let state = S.set engine state (CoqEngine_HOAS.from_env_keep_univ_of_sigma ~uctx ~env0 ~env sigma) in
    let state = UVMap.empty state in
    state
  end
  
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

let sealed_goal2lp ~depth ~args ~in_elpi_tac_arg ~base state k =
  let calldepth = depth in
  let env = get_global_env state in
  let sigma = get_sigma state in
  let state, elpi_goal_evar, elpi_raw_goal_evar, evar_decls = in_elpi_evar ~calldepth k state in
  let evar_concl, goal_ctx, goal_env =
    info_of_evar ~env ~sigma ~section:(section_ids env) k in
  let state, g, gls =
    under_coq2elpi_ctx ~calldepth state goal_ctx
      ~mk_ctx_item:(fun _ t -> E.mkApp nablac (E.mkLam t) [])
      (fun coq_ctx hyps ~depth state ->
            let state, args, gls_args = API.Utils.map_acc (in_elpi_tac_arg ~base ~depth ?calldepth:(Some calldepth) coq_ctx [] sigma) state args in
            let args = List.flatten args in
            let state, hyps, raw_ev, ev, goal_ty, gls =
              in_elpi_evar_concl evar_concl ~raw_uvar:elpi_raw_goal_evar elpi_goal_evar
                coq_ctx hyps ~calldepth ~depth state in
          state, E.mkApp sealc (in_elpi_goal state ~args ~hyps ~raw_ev ~ty:goal_ty ~ev) [], gls_args @ gls) in
  state, g, evar_decls @ gls

let solvegoal2query sigma goals loc args ~in_elpi_tac_arg ~depth:calldepth ~base state =

  let state = S.set engine state (from_env_sigma (get_global_env state) sigma) in

  let state, gl, gls =
    API.Utils.map_acc (fun state goal ->
      if not (Evd.is_undefined sigma goal) then
        err Pp.(str (Printf.sprintf "Evar %d is not a goal" (Evar.repr goal)));

      sealed_goal2lp ~depth:calldepth ~in_elpi_tac_arg ~args ~base state goal) state goals in

  let state, ek = F.Elpi.make ~name:"NewGoals" state in
  let newgls = E.mkUnifVar ek ~args:[] state in

  let query =
    E.mkApp API.RawData.Constants.orc
      (E.mkApp msolvec (U.list_to_lp_list gl) [newgls])
      [E.mkApp allc (E.mkApp openc (E.mkConst solvec) []) [U.list_to_lp_list gl;newgls]] in

  state, query, gls
;;

let sealed_goal2lp ~depth state goal =
  sealed_goal2lp ~depth ~args:[] ~base:() ~in_elpi_tac_arg:(fun ~base ~depth ?calldepth _ _ _ _ _ -> assert false) state goal

let customtac2query sigma goals loc text ~depth:calldepth ~base state =
  match goals with
  | [] | _ :: _ :: _ ->
     CErrors.user_err Pp.(str "elpi query can only be used on one goal")
  | [goal] ->
    let EvarInfo info = Evd.find sigma goal in
    let env = get_global_env state in
    let env = Environ.reset_with_named_context (Evd.evar_filtered_hyps info) env in
    if not (Evd.is_undefined sigma goal) then
      err Pp.(str (Printf.sprintf "Evar %d is not a goal" (Evar.repr goal)));
    let state = S.set engine state (from_env_sigma env sigma) in
    let state, elpi_goal_evar, elpi_raw_goal_evar, evar_decls = in_elpi_evar ~calldepth goal  state in
    let evar_concl, goal_ctx, goal_env =
      info_of_evar ~env ~sigma ~section:(section_ids env) goal in
    let state, query, gls =
      under_coq2elpi_ctx ~calldepth state goal_ctx
      (fun coq_ctx hyps ~depth state ->
          let q = API.Quotation.elpi ~language:API.Quotation.elpi_language state loc text in
          let _amap, q = API.RawQuery.term_to_raw_term state base ~depth q in
          state, q, []) in
    debug Pp.(fun () -> str"engine: " ++ str (show_coq_engine (S.get engine state)));
    state, query, evar_decls @ gls
;;

type 'arg tactic_main = Solve of 'arg list | Custom of string

let solvegoals2query sigma goals loc ~main:args ~in_elpi_tac_arg ~depth ~base state =
  solvegoal2query sigma goals loc args ~in_elpi_tac_arg ~depth ~base state
    
let txtgoals2query sigma goals loc ~main:text ~depth ~base state =
  customtac2query sigma goals loc text ~depth ~base state
  
let eat_n_lambdas ~depth t upto state =
  let open E in
  let rec aux n t =
    if n = upto then t
    else match look ~depth:n t with
      | Lam t -> aux (n+1) t
      | UnifVar(r,a) -> aux (n+1) (mkUnifVar r ~args:(a@[mkConst n]) state)
      | Const c -> aux (n+1) (mkApp c (mkConst n) [])
      | App (c, x, xs) -> aux (n+1) (mkApp c x (xs@[mkConst n]))
      | _ -> CErrors.anomaly Pp.(str "rocq-elpi eat_n_lambdas : " ++
        str(pp2string (P.term depth) t))
      in

    aux depth t

type declared_goal =
  | Open of { evar:Evar.t; scope: E.term list; ctx: E.term; args: E.term list}
  | Closed_by_side_effect
  | Not_a_goal

let get_goal_ref ~depth syntactic_constraints state t =
  match E.look ~depth t with
  | E.App(c,ctx,[_;_;g;i]) when c == goalc ->
     begin match E.look ~depth g with
     | E.UnifVar(ev,scope) ->
       begin try
         let uv = find_evar ev syntactic_constraints in
         let evar = UVMap.host_failsafe uv state in
         Open {ctx; evar; scope; args = U.lp_list_to_list ~depth i}
       with Not_found -> 
         Not_a_goal
       end
     | _ -> Closed_by_side_effect
     end
  | _ -> Not_a_goal
  
let rec get_sealed_goal_ref ~depth syntactic_constraints state t =
  match E.look ~depth t with
  | E.App(c,g,[]) when c == nablac ->
     begin match E.look ~depth g with
     | E.Lam g -> get_sealed_goal_ref ~depth:(depth+1) syntactic_constraints state g
     | _ -> err Pp.(str"Not a lambda after nabla: " ++ str(pp2string (P.term depth) g))
     end
  | E.App(c,g,[]) when c == sealc ->
     get_goal_ref ~depth syntactic_constraints state g
  | _ -> Not_a_goal

let no_list_given = function
  | E.UnifVar _ -> true
  | _ -> false

let rec skip_lams ~depth d t = match E.look ~depth t with
  | E.Lam t -> skip_lams ~depth:(depth+1) (d+1) t
  | x -> x, d

let show_coq_engine ?with_univs state =
  show_coq_engine ?with_univs (S.get engine state)
  
let show_coq_elpi_engine_mapping state =
  "Rocq-Elpi mapping:\n" ^ UVMap.show state

let show_all_engine state = show_coq_engine ~with_univs:true state ^ "\n" ^ show_coq_elpi_engine_mapping state

let is_uvar ~depth t =
  match E.look ~depth t with
  | E.UnifVar(e,_) -> Some e
  | _ -> None

let elpi_solution_to_coq_solution ~eta_contract_solution ~calldepth syntactic_constraints state =
  let { sigma; global_env } as e = S.get engine state in
  
  debug Pp.(fun () -> str"elpi sigma -> coq sigma: before:\n" ++ str (show_all_engine state));

  (* if ?X <-> Y   =  Z, we have two cases:
     - Z unknown  ---> we update the link, i.e. ?X <-> Z (no update, the code below does it)
     - ?B <-> Z   ---> we propagate the unif to Coq, i.e. ?X = ?B
  *)
  let updates =
    UVMap.fold (fun k er e elpi_solution updates ->
      match elpi_solution with
      | None -> updates
      | Some t ->
          match is_uvar ~depth:0 t with
          | None -> updates
          | Some e' when UVMap.mem_elpi e' state && not @@ Evar.equal k (UVMap.host_failsafe e' state) -> updates
          | Some e' -> (k,er,e') :: updates
    ) state [] in
  let state = List.fold_left (fun state (k,r,e) ->
    let state = UVMap.remove_host k state in
    UVMap.add k r e state
    ) state updates in

  debug Pp.(fun () -> str"elpi sigma -> coq sigma: synchronized:\n" ++ str (show_all_engine state));

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
       let eta_reduced = ref false in
       let state, _, gls = under_coq2elpi_ctx ~calldepth:0 state ctx ~mk_ctx_item:(fun _ x -> x) 
         (fun coq_ctx hyps ~depth state ->
           debug Pp.(fun () ->
               str"solution for "++ Evar.print k ++ str" in ctx=" ++ cut () ++
               Printer.pr_named_context_of coq_ctx.env (get_sigma state) ++ cut () ++
               str" at depth=" ++ int depth ++ str" id term=" ++ str(pp2string (P.term 0) t));

           (* These meta-level-lambdas are elpi specific, they don't exist in Coq *)
           debug Pp.(fun () -> str "before:" ++ str(pp2string (P.term 0) t));
           let t = eat_n_lambdas ~depth:0 t coq_ctx.proof_len state in
           debug Pp.(fun () -> str "after:" ++ str(pp2string (P.term coq_ctx.proof_len) t)); 

           let state, solution, gls = lp2constr
               syntactic_constraints coq_ctx ~depth state t in

            let solution =
              if eta_contract_solution then
                let sol' = eta_contract coq_ctx.env (get_sigma state) solution in
                eta_reduced := sol' != solution;
                sol'
              else solution in

            let gls = gls |> List.map (function
              | DeclareEvar(k,d,r,s) -> DeclareEvar(k,calldepth,r,s)
              | x -> x
            ) in

           spilled_solution := solution;
           state, E.mkNil (* dummy *), gls)
       in
       let coq_solution = !spilled_solution in

       let state = S.update engine state (fun ({ sigma } as e) ->
          let sigma = 
            if !eta_reduced then
              let info = Evd.find_undefined sigma k in
              let ty = Evd.evar_concl info  in 
              Typing.check (Evd.evar_env global_env info) sigma coq_solution ty 
            else sigma in
          let sigma = Evd.define k coq_solution sigma in
          { e with sigma }) in

       (* since the order in which we add is not topological*)
       let assigned = Evar.Set.add k assigned in

       state, assigned, true, gls :: extra) state
     (state, Evar.Set.empty, false, [])
  in
    
  (* Drop from the mapping the evars that were assigned *)
  let state = UVMap.filter_host (fun k -> not (Evar.Set.mem k assigned)) state in

  debug Pp.(fun () -> str"elpi sigma -> coq sigma: after:\n" ++ str (show_all_engine state));

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
         let declared = CList.filter_map (fun x ->
           match get_sealed_goal_ref ~depth syntactic_constraints state x with
           | Open {evar; _} -> Some evar
           | Closed_by_side_effect -> None 
           | Not_a_goal -> err Pp.(str"Not a goal " ++ str(pp2string (P.term depth) x) ++ str " in " ++ cut () ++ str(pp2string (API.Pp.constraints pp_ctx) constraints))) l in
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
  let EvarInfo info = Evd.find sigma root in
  let res =
    match Evd.evar_body info with
    | Evd.Evar_empty -> Evar.Set.add root acc
    | Evd.Evar_defined d -> acc in
  let res = Evar.Set.union res @@ Evarutil.filtered_undefined_evars_of_evar_info sigma info in
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

let solution2evd ~eta_contract_solution sigma0 { API.Data.constraints; assignments; state; pp_ctx } roots =
  let state, solved_goals, _, _gls = elpi_solution_to_coq_solution ~eta_contract_solution ~calldepth:0 constraints state in
  let sigma = get_sigma state in
  let roots = Evd.fold_undefined (fun k _ acc -> Evar.Set.add k acc) sigma0 roots in 
  let reachable_undefined_evars = reachable sigma roots Evar.Set.empty in
  let declared_goals, shelved_goals =
    get_declared_goals (Evar.Set.diff reachable_undefined_evars solved_goals) constraints state assignments pp_ctx in
  debug Pp.(fun () -> str "Goals: " ++ prlist_with_sep spc Evar.print declared_goals);
  debug Pp.(fun () -> str "Shelved Goals: " ++ prlist_with_sep spc Evar.print shelved_goals);
  Evd.fold_undefined (fun k _ sigma ->
    if Evar.Set.mem k reachable_undefined_evars then sigma
    else Evd.remove sigma k
    ) sigma sigma,
  declared_goals,
  shelved_goals

let tclSOLUTION2EVD ~eta_contract_solution sigma0 solution =
  let open Proofview.Unsafe in
  let open Tacticals in
  let open Proofview.Notations in
    tclGETGOALS >>= fun gls ->
    let gls = gls |> List.map Proofview.drop_state in
    let roots = List.fold_right Evar.Set.add gls Evar.Set.empty in
    let sigma, declared_goals, shelved_goals = solution2evd ~eta_contract_solution sigma0 solution roots in
  tclTHENLIST [
    tclEVARS sigma;
    tclSETGOALS @@ List.map Proofview.with_empty_state declared_goals;
    Proofview.shelve_goals shelved_goals
  ]


let set_current_sigma ~depth state sigma =

  debug Pp.(fun () -> str"bringing updated sigma back to lp");

  let state = set_sigma state sigma in
  let state, assignments, decls, to_remove_coq, to_remove_elpi =
    UVMap.fold (fun k elpi_raw_evk elpi_evk solution (state, assignments, decls, to_remove_coq, to_remove_elpi as acc) ->
      let EvarInfo info = Evd.find sigma k in
      match Evd.evar_body info with
      | Evd.Evar_empty -> acc
      | Evd.Evar_defined c ->
          let ctx = Evd.evar_filtered_context info in
          let env = get_global_env state in
          let section_ids = section_ids env in
          let ctx = ctx |> CList.filter (fun e -> let id = Context.Named.Declaration.get_id e in not(List.mem id section_ids)) in
          let assigned = E.mkUnifVar elpi_evk ~args:[] state in
          debug Pp.(fun () ->
              str"set_current_sigma: preparing assignment for " ++ str (pp2string (P.term depth) assigned) ++
              str" under context " ++ Printer.pr_named_context env sigma (EConstr.Unsafe.to_named_context ctx));
          let state, t, dec = under_coq2elpi_ctx ~mk_ctx_item:(fun _ -> E.mkLam) ~calldepth:depth state ctx (fun coq_ctx hyps ~depth:new_ctx_depth state ->
            constr2lp coq_ctx ~calldepth:depth ~depth:new_ctx_depth state c) in
          let assignment = API.Conversion.Unify(assigned, t) in
          debug Pp.(fun () ->
            str"set_current_sigma: assignment at depth" ++ int depth ++
            str" is: " ++ str (pp2string (P.term depth) assigned) ++
            str" = " ++ str (pp2string (P.term depth) t));
          state, assignment :: assignments, dec :: decls, k :: to_remove_coq, (elpi_raw_evk, elpi_evk, List.length ctx) :: to_remove_elpi
      ) state (state,[],[],[],[]) in
  let state = List.fold_right UVMap.remove_host to_remove_coq state in
  let removals = List.map2 (fun (rk,k,ano) e ->
    let args = CList.init ano (fun x -> E.mkConst (x+depth)) in
    let raw_ev = E.mkUnifVar rk ~args state in
    let ev = E.mkUnifVar k ~args state in
    RmEvar (e,raw_ev, ev)) to_remove_elpi to_remove_coq in
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

type coercion_status = Regular | Off | Reversible
type record_field_att =
  | Coercion of coercion_status
  | Canonical of bool

let coercion_status = let open API.Conversion in let open API.AlgebraicData in declare {
  ty = TyName "coercion-status";
  doc = "Status of a record field w.r.t. coercions";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("regular","",N,
        B Regular,
        M (fun ~ok ~ko -> function Regular -> ok | _ -> ko ()));
    K("reversible","",N,
        B Reversible,
        M (fun ~ok ~ko -> function Reversible -> ok | _ -> ko ()));
    K("off","",N,
      B Off,
      M (fun ~ok ~ko -> function Off -> ok | _ -> ko ()));
  ]
} |> API.ContextualConversion.(!<)
  
let record_field_att = let open API.Conversion in let open API.AlgebraicData in let open Elpi.Builtin in declare {
  ty = TyName "field-attribute";
  doc = "Attributes for a record field. Can be left unspecified, see defaults below.";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("coercion","default off",A(coercion_status,N),
        B (fun x -> Coercion (x)),
        M (fun ~ok ~ko -> function Coercion x -> ok (x) | _ -> ko ()));
    K("canonical","default true, if field is named",A(bool,N),
        B (fun x -> Canonical(x)),
        M (fun ~ok ~ko -> function Canonical x -> ok (x) | _ -> ko ()));  
  ]
} |> API.ContextualConversion.(!<)

let record_field_attributes = Elpi.Builtin.unspec (API.BuiltInData.list record_field_att)

let is_coercion_att = function
  | Elpi.Builtin.Unspec -> Off
  | Elpi.Builtin.Given l ->
      let rec aux = function
      | [] -> Off
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
  let coind = not (Declarations.CoFinite = find) in
  E.mkApp inductivec (in_elpi_id id) [in_elpi_bool state coind; arity;E.mkLam @@ U.list_to_lp_list constructors]

let in_elpi_indtdecl_constructor id ty =
  E.mkApp constructorc (in_elpi_id id) [ty]

type record_field_spec = { name : Name.t; is_coercion : coercion_status; is_canonical : bool }
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


let inference_nonuniform_params_off =
  CWarnings.create
    ~name:"elpi.unsupported-nonuniform-parameters-inference"
    ~category:Rocq_elpi_utils.elpi_cat Pp.(fun () ->
      strbrk"Inference of non-uniform parameters is not available in Elpi, please use the explicit | mark in the inductive declaration or Set Uniform Inductive Parameters")
      
let restricted_sigma_of s state =
  let sigma = get_sigma state in
  let ustate = Evd.evar_universe_context sigma in
  let ustate = UState.restrict_even_binders ustate s in
  let ustate = UState.fix_undefined_variables ustate in
  let ustate = UState.collapse_sort_variables ustate in
  let sigma = Evd.set_universe_context sigma ustate in
  sigma

let universes_of_term state t =
  let sigma = get_sigma state in
  snd (EConstr.universes_of_constr sigma t)

let universes_of_udecl state ({ UState.univdecl_instance ; univdecl_constraints } : UState.universe_decl) =
  let used1 = univdecl_instance in
  let used2 = List.map (fun (x,_,y) -> [x;y]) (Univ.Constraints.elements univdecl_constraints) in
  let used = List.fold_right Univ.Level.Set.add used1 Univ.Level.Set.empty in
  let used = List.fold_right Univ.Level.Set.add (List.flatten used2) used in
  used

let name_universe_level = ref 0

let name_universe_level state l =
  S.update_return engine state (fun e ->
    let ustate = Evd.evar_universe_context e.sigma in
    match UState.id_of_level ustate l with
    | Some id -> e, id
    | None ->
        incr name_universe_level;
        let id = Id.of_string Printf.(sprintf "eu%d" !name_universe_level) in
        let ustate = UState.name_level l id ustate in
        let sigma = Evd.set_universe_context e.sigma ustate in
        { e with sigma }, id
  )


let mk_universe_decl univdecl_extensible_instance univdecl_extensible_constraints univdecl_constraints univdecl_instance =
  let open UState in
  { univdecl_qualities = [];
    univdecl_extensible_instance;
    univdecl_extensible_qualities = false;
    univdecl_extensible_constraints;
    univdecl_constraints;
    univdecl_instance}

let poly_cumul_udecl_variance_of_options state options =
  match options.universe_decl with
  | NotUniversePolymorphic -> state, false, false, UState.default_univ_decl, [| |]
  | Cumulative ((univ_lvlt_var,univdecl_extensible_instance),(univdecl_constraints,univdecl_extensible_constraints)) ->
    let univdecl_instance, variance = List.split univ_lvlt_var in
    state, true, true,
    mk_universe_decl univdecl_extensible_instance univdecl_extensible_constraints univdecl_constraints univdecl_instance,
    Array.of_list variance
  | NonCumulative((univ_lvlt,univdecl_extensible_instance),(univdecl_constraints,univdecl_extensible_constraints)) ->
    let univdecl_instance = univ_lvlt in
    let variance = List.init (List.length univdecl_instance) (fun _ -> None) in
    state, true, false,
    mk_universe_decl univdecl_extensible_instance univdecl_extensible_constraints univdecl_constraints univdecl_instance,
    Array.of_list variance

[%%if coq = "8.20"]
let comInductive_interp_mutual_inductive_constr ~cumulative ~poly ~template ~finite =
  ComInductive.interp_mutual_inductive_constr ~arities_explicit:[true] ~template_syntax:[SyntaxAllowsTemplatePoly] ~cumulative ~poly ~template ~finite 
[%%elif coq = "9.0"]
let comInductive_interp_mutual_inductive_constr ~cumulative ~poly ~template ~finite =
  let flags = {
    ComInductive.poly;
    cumulative;
    template = Some false;
    finite;
    mode = None;
  }
  in
  ComInductive.interp_mutual_inductive_constr ~arities_explicit:[true] ~template_syntax:[SyntaxAllowsTemplatePoly] ~flags
[%%else]
let comInductive_interp_mutual_inductive_constr ~cumulative ~poly ~template ~finite ~ctx_params ~env_ar_params =
  let flags = {
    ComInductive.poly;
    cumulative;
    template = Some false;
    finite;
    mode = None;
  }
  in
  let env_ar = Environ.pop_rel_context (List.length ctx_params) env_ar_params in
  ComInductive.interp_mutual_inductive_constr ~arities_explicit:[true] ~template_syntax:[SyntaxAllowsTemplatePoly] ~flags ~env_ar ~ctx_params
[%%endif]


let comInductive_interp_mutual_inductive_constr_post x = x

let lp2inductive_entry ~depth coq_ctx constraints state t =

  let lp2constr coq_ctx ~depth state t =
    lp2constr constraints coq_ctx ~depth state t in

  let check_consistency_and_drop_nuparams sigma nuparams name params arity =
    let eq_param ind_index x y =
      Name.equal
        (Context.Rel.Declaration.get_name x)
        (Context.Rel.Declaration.get_name y) &&
      EConstr.eq_constr_nounivs sigma
       (EConstr.Vars.liftn 1 ind_index (Context.Rel.Declaration.get_type x))
       (Context.Rel.Declaration.get_type y) in
    let rec aux n nuparams params =
      match nuparams, params with
      | [], params -> EC.it_mkProd_or_LetIn arity (List.rev params)
      | x :: nuparams, y :: params when eq_param n x y ->
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
     * This latter context is called, later, env_ar_params
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

    let state, (melims, mind, ubinders, uctx) =
      let private_ind = false in
      let state, poly, cumulative, udecl, variances =
        poly_cumul_udecl_variance_of_options state coq_ctx.options in
      let the_type =
        let open Context.Rel.Declaration in
        LocalAssum(nameR itname, EConstr.it_mkProd_or_LetIn arity (nuparams @ params)) in
      let env_ar_params = (Global.env ()) |> EC.push_rel the_type |> EC.push_rel_context (nuparams @ params) in

    (* restruction to used universes *)
    let state = minimize_universes state in
    let used =
      List.fold_left (fun acc t ->
          Univ.Level.Set.union acc
            (universes_of_term state t))
        (universes_of_term state arity) ktypes in
    let used =
      let open Context.Rel.Declaration in
      List.fold_left (fun acc -> function
        | (LocalDef(_,t,b)) ->
          Univ.Level.Set.union acc
           (Univ.Level.Set.union
            (universes_of_term state t)
            (universes_of_term state b))
        | (LocalAssum(_,t)) ->
          Univ.Level.Set.union acc
            (universes_of_term state t))
        used (nuparams @ params) in
      let sigma = restricted_sigma_of used state in

      state, comInductive_interp_mutual_inductive_constr
        ~sigma
        ~template:(Some false)
        ~udecl
        ~variances
        ~ctx_params:(nuparams @ params)
        ~indnames:[itname]
        ~arities:[arity]
        ~constructors:[knames, ktypes]
        ~env_ar_params
        ~cumulative
        ~poly
        ~private_ind
        ~finite:finiteness |> comInductive_interp_mutual_inductive_constr_post
      in
    let mind = { mind with
      Entries.mind_entry_record =
        if finiteness = Declarations.BiFinite then
          if coq_ctx.options.primitive = Some true then Some (Some [|Names.Id.of_string "record"|]) (* primitive record *)
          else Some None (* regular record *)
        else None } (* not a record *) in
    let i_impls = impls @ nuimpls in

    state, melims, mind, uctx, ubinders, i_impls, kimpls, List.(concat (rev gls_rev))
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
            let state, melims, idecl, uctx, ubinders, i_impls, ks_impls, gl2 =
              aux_construtors (push_coq_ctx_local depth e coq_ctx) ~depth:(depth+1) (params,List.rev impls) (nuparams, List.rev nuimpls) arity iname fin
                state ks in
            state, (melims, idecl, uctx, ubinders, None, [i_impls, ks_impls]), List.(concat (rev (gl2 :: gl1 :: extra)))
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
        let state, melims, idecl, uctx, ubinders, i_impls, ks_impls, gl2 =
          aux_construtors (push_coq_ctx_local depth e coq_ctx) ~depth:(depth+1) (params,List.rev impls) ([],[]) arity iname Declarations.BiFinite
            state k in
        let primitive = coq_ctx.options.primitive = Some true in
        state, (melims, idecl, uctx, ubinders, Some (primitive,fields_names_coercions), [i_impls, ks_impls]), List.(concat (rev (gl2 :: gl1 :: extra)))
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
;;

let rec safe_combine3 l1 l2 l3 ~default3 =
  match l1, l2, l3 with
  | [], [], [] -> []
  | x::xs, y::ys, z::zs -> (x,y,z) :: safe_combine3 xs ys zs ~default3
  | x::xs, y::ys, [] -> (x,y,default3) :: safe_combine3 xs ys [] ~default3
  | _ -> raise (Invalid_argument "safe_combine3")

let rec safe_combine2_impls l1 l2 ~default2 =
  match l1, l2 with
  | [], _ -> []
  | x::xs, y::ys -> (x,y) :: safe_combine2_impls xs ys ~default2
  | x::xs, [] -> (x,default2) :: safe_combine2_impls xs [] ~default2
let safe_combine2_impls l1 l2 ~default2 =
  let l = safe_combine2_impls (List.rev l1) l2 ~default2 in
  List.rev l


(* convention: nuparams are also in each constructor *)
type 'a ctx_entry = { id : Id.t; typ : EConstr.t; extra : 'a }
type constructor = { id : Id.t; arity : Glob_term.binding_kind ctx_entry list; typ : EConstr.t } 
type ind_decl =
  | Inductive of {
      id : Id.t;
      nuparams : Glob_term.binding_kind ctx_entry list;
      typ : EConstr.t;
      constructors : constructor list;
      kind : Declarations.recursivity_kind;
    }
  | Record of {
      id : Id.t;
      kid : Id.t;
      typ : EConstr.t;
      fields : record_field_att list ctx_entry list;
    }
type hoas_ind = {
  params : Glob_term.binding_kind ctx_entry list;
  decl : ind_decl;
}

let mk_parameter2 ~depth name impl ty rest state =
  let state, imp = in_elpi_imp ~depth state impl in
  state, in_elpi_parameter ~imp name ty rest

let mk_ctx_item_record_field ~depth name atts ty rest state =
  let state, atts, gls = record_field_attributes.API.Conversion.embed ~depth state (Elpi.Builtin.Given atts) in
  state, in_elpi_field atts name ty rest

let under_coq2elpi_relctx ~calldepth state (ctx : 'a ctx_entry list) ~coq_ctx ~mk_ctx_item kont =
  let gls = ref [] in
  let rec aux ~depth coq_ctx hyps state = function
    | [] ->
        let state, t, gls_t = kont coq_ctx hyps ~depth state in
        gls := gls_t @ !gls;
        state, t
    | { id; typ; extra } :: rest ->
        let name = Names.Name id in
        let state, ty, gls_ty = constr2lp coq_ctx ~calldepth ~depth state typ in
        gls := gls_ty @ !gls;
        let hyp = mk_decl ~depth name ~ty in
        let hyps = { ctx_entry = hyp ; depth = depth } :: hyps in
        let e = Context.Rel.Declaration.LocalAssum (annotR name, typ) in
        let coq_ctx = push_coq_ctx_local depth e coq_ctx in
        let state, rest = aux ~depth:(depth+1) coq_ctx hyps state rest in
        mk_ctx_item ~depth name extra ty rest state
  in
    let state, t = aux ~depth:calldepth coq_ctx [] state (List.rev ctx) in
    state, t, !gls
;;


let type_of_global state r inst_opt = API.State.update_return engine state (fun x ->
  let sigma, c = Evd.fresh_global x.global_env x.sigma r ?names:inst_opt in
  let ty = Retyping.get_type_of x.global_env sigma c in
  { x with sigma }, (ty, EConstr.Unsafe.to_instance @@ snd @@ EConstr.destRef sigma c))


let compute_with_uinstance ~depth options state f x inst_opt =
  match options.uinstance with
  | NoInstance ->
    let state, r, i = f state x inst_opt in
    state, r, i, []
  | ConcreteInstance i ->
    let state, r, i = f state x (Option.append inst_opt (Some i)) in
    state, r, i, []
  | VarInstance (v_head, v_args, v_depth) ->
    let state, r, i = f state x inst_opt in
    match i with
    | None -> state, r, None, []
    | Some uinst ->
      let v' = U.move ~from:v_depth ~to_:depth (E.mkUnifVar v_head ~args:v_args state) in
      let state, lp_uinst, extra_goals = uinstance.API.Conversion.embed ~depth state uinst in
      state, r, Some uinst, API.Conversion.Unify (v', lp_uinst) :: extra_goals
    

let embed_arity ~depth coq_ctx state (relctx,ty) =
  let calldepth = depth in
  under_coq2elpi_relctx ~calldepth ~coq_ctx state relctx
    ~mk_ctx_item:mk_parameter2
    (fun coq_ctx hyps ~depth state ->
        let state, ty, gl = constr2lp coq_ctx ~calldepth ~depth state ty in
        state, in_elpi_arity ty, gl)
;;
    

let hoas_ind2lp ~depth coq_ctx state { params; decl } =
  let calldepth = depth in
  under_coq2elpi_relctx ~calldepth ~coq_ctx state params
    ~mk_ctx_item:mk_parameter2
    (fun coq_ctx hyps ~depth state -> match decl with
    | Inductive { id; nuparams; typ; constructors; kind } ->
      let sigma = get_sigma state in
      let paramsno = List.length params in
     (* Relocation to match Coq's API.
      * From
      *  Ind, Params, NuParams |- ktys
      * To
      *  Params, Ind, NuParams |- ktys
      *)
      let rec iter n acc f =
        if n = 0 then acc
        else iter (n-1) (f acc) f in
      let subst arityno = CList.init (arityno + paramsno + 1) (fun i ->
        let i = i + 1 in (* init is 0 based, rels are 1 base *)
        if i = arityno + paramsno + 1 then
          let ind = EC.mkRel (arityno + 1) in
          iter paramsno ind (fun x -> EConstr.mkLambda (anonR,EConstr.mkProp,EConstr.Vars.lift 1 x))
        else if i > arityno then EC.mkRel(i+1)
        else EC.mkRel i) in
      let reloc ctx_len t =
        let t = EC.Vars.substl (subst ctx_len) t in
        Reductionops.nf_beta (Global.env()) sigma t in
    
      let state, arity, gls1 = embed_arity ~depth coq_ctx state (nuparams,typ) in
      let coq_ctx = push_coq_ctx_local depth (Context.Rel.Declaration.LocalAssum(anonR,EConstr.mkProp)) coq_ctx in
      let depth = depth+1 in
      let embed_constructor state { id; arity; typ } =
        let alen = List.length arity in
        let kctx = List.mapi (fun i ({ extra; typ } as x) -> { x with typ = reloc (alen - i -1) typ }) arity in
        let state, karity, gl = embed_arity ~depth coq_ctx state (kctx,reloc alen typ) in
        state, in_elpi_indtdecl_constructor (Name id) karity, gl in
      let state, ks, gls2 =
        API.Utils.map_acc embed_constructor state constructors in
      state, in_elpi_indtdecl_inductive state kind (Name id) arity ks, List.flatten [gls1 ; gls2]
   | Record { id; kid; typ; fields } ->
      let embed_record_constructor state fields =
        under_coq2elpi_relctx ~calldepth:depth state fields
          ~coq_ctx
          ~mk_ctx_item:mk_ctx_item_record_field
            (fun coq_ctx hyps ~depth state -> state, in_elpi_indtdecl_endrecord (), [])
      in
      let state, sort, gls1 = constr2lp coq_ctx ~calldepth ~depth state typ in
      let state, rd, gls2 = embed_record_constructor state fields in
      state, in_elpi_indtdecl_record (Name id) sort (Name kid) rd, gls1 @ gls2
    )
;;

let param2ctx l =
  let open Context.Rel.Declaration in
  List.map (function
  | LocalAssum( { Context.binder_name = Anonymous },typ), (Glob_term.Explicit as bk) -> { id = Id.of_string "_"; typ; extra = bk }
  | LocalAssum( { Context.binder_name = Name id },typ), bk -> { id; typ; extra = bk }
  | LocalDef _, _ -> nYI "let-in in inductive parameters"
  | _ -> assert false) l

let nonexpimpls impls =
  let rec aux = function
    | [] -> []
    | Glob_term.Explicit :: l -> aux l
    | l -> l in
    aux (List.rev impls)

let drop_nparams_from_ctx n ctx =
  let ctx, _ = CList.chop (List.length ctx - n) ctx in
  ctx

let ideclc = E.Constants.declare_global_symbol "indt-decl"
let uideclc = E.Constants.declare_global_symbol "upoly-indt-decl"

let inductive_decl2lp ~depth coq_ctx constraints state (mutind,uinst,(mind,ind),(i_impls,k_impls)) =
  let { Declarations.mind_params_ctxt;
        mind_finite = kind;
        mind_nparams = allparamsno;
        mind_nparams_rec = paramsno;
        mind_ntypes = ntyps;
        mind_record } = mind in
  let mind_params_ctxt = Vars.subst_instance_context uinst mind_params_ctxt in
  let allparams = List.map EConstr.of_rel_decl mind_params_ctxt in
  let allparams = safe_combine2_impls allparams i_impls ~default2:Glob_term.Explicit |> param2ctx in
  let nuparamsno = allparamsno - paramsno in
  let nuparams, params = CList.chop nuparamsno allparams in
  let { Declarations.mind_consnames = constructor_names;
        mind_typename = id;
        mind_nf_lc = constructor_types } = ind in
  let constructor_types = constructor_types |> Array.map (fun (ctx,ty) -> Vars.subst_instance_context uinst ctx, Vars.subst_instance_constr uinst ty) in
  let arity_w_params = Inductive.type_of_inductive ((mind,ind),uinst) in
  let sigma = get_sigma state in
  let drop_nparams_from_term n x =
    let x = EConstr.of_constr x in
    let ctx, sort = EConstr.decompose_prod_decls sigma x in
    let ctx = drop_nparams_from_ctx n ctx in
    EConstr.it_mkProd_or_LetIn sort ctx in
  let decl =
    if mind_record = Declarations.NotRecord then
      let typ = drop_nparams_from_term allparamsno arity_w_params in
      let constructors =
        safe_combine3 (Array.to_list constructor_names) (Array.to_list constructor_types) k_impls ~default3:[] |>
        List.map (fun (id,(ctx,x),impls) ->
          let x =
            Term.it_mkProd_or_LetIn x ctx |>
            Inductive.abstract_constructor_type_relatively_to_inductive_types_context ntyps mutind in
          let nonexpimplsno = List.length (nonexpimpls impls) in
          let ctx, typ = Term.decompose_prod_n_decls (max allparamsno nonexpimplsno) x in
          let ctx = EConstr.of_rel_context ctx in
          let typ = EConstr.of_constr typ in
          let ctx = safe_combine2_impls ctx impls ~default2:Glob_term.Explicit in
          let arity = drop_nparams_from_ctx paramsno ctx |> param2ctx in
          { id; arity; typ }) in
      Inductive { nuparams; id; typ; kind; constructors }
    else
      let kid = constructor_names.(0) in
      if (nuparamsno != 0) then nYI "record with non uniform paramters";
      let projections = Structures.Structure.((find (mutind,0)).projections) in
      let fieldsno = List.length projections in
      let kctx, _ = constructor_types.(0) in
      let kctx = EConstr.of_rel_context kctx in
      let kctx = drop_nparams_from_ctx paramsno kctx in
      if (List.length kctx != fieldsno) then CErrors.anomaly Pp.(str"record fields number != projections");
      let typ = drop_nparams_from_term allparamsno arity_w_params in
      let open Structures.Structure in
      let fields_atts = List.map (fun { proj_name; proj_body; proj_canonical; } ->
        proj_name,
          (match proj_body with
            | None -> Coercion Off
            | Some c ->
               try
                  let { Coercionops.coe_reversible } = Coercionops.coercion_info (Names.GlobRef.ConstRef c) in
                  Coercion (if coe_reversible then Reversible else Regular)
               with Not_found -> Coercion Off) ::
          (Canonical proj_canonical) :: [])
        (List.rev projections) in
      let param2field l =
        let open Context.Rel.Declaration in
        List.map (function
        | LocalAssum( { Context.binder_name = Anonymous },typ), (Anonymous,atts) -> { id = Id.of_string "_"; typ; extra = atts }
        | LocalAssum( { Context.binder_name = Name id },typ), (Name id1,atts) when Id.equal id id1 -> { id; typ; extra = atts }
        | LocalAssum _, _ -> CErrors.anomaly Pp.(str"record fields names != projections");
        | LocalDef _, _ -> nYI "let-in in record fields parameters") l in
      let fields = List.combine kctx fields_atts |> param2field in
      Record { id; kid; typ; fields }
    in
  let ind = { params; decl } in
  hoas_ind2lp ~depth coq_ctx state ind
;;
       
let upoly_decl_of ~depth state ~loose_udecl mie =
  let open Entries in
  match mie.mind_entry_universes with
  | Template_ind_entry _ -> nYI "template polymorphic inductives"
  | Polymorphic_ind_entry uc ->
    let qvars, vars = UVars.Instance.to_array @@ UVars.UContext.instance uc in
    if not (CArray.is_empty qvars) then nYI "sort poly inductives"
    else
      let state, vars = CArray.fold_left_map (fun s l -> fst (name_universe_level s l), l) state vars in
      let csts = UVars.UContext.constraints uc in
      begin match mie.mind_entry_variance with
      | None ->
          let state, up, gls = universe_decl.API.Conversion.embed ~depth state ((Array.to_list vars,loose_udecl),(csts,loose_udecl)) in
          state, (fun i -> E.mkApp uideclc i [up]), gls
      | Some variance ->
          assert(Array.length variance = Array.length vars);
          let uv = Array.map2 (fun x y -> (x,y)) vars variance |> Array.to_list in
          let state, up, gls = universe_decl_cumul.API.Conversion.embed ~depth state ((uv,loose_udecl),(csts,loose_udecl)) in
          state, (fun i -> E.mkApp uideclc i [up]), gls
      end
  | Monomorphic_ind_entry -> state, (fun i -> E.mkApp ideclc i []), []

let inductive_entry2lp ~depth coq_ctx constraints state ~loose_udecl e =
  let open ComInductive.Mind_decl in
  let open Entries in
  let { mie; nuparams; univ_binders; implicits; uctx } = e in
  let i_impls, k_impls = match implicits with
    | [i,k] ->
      List.map binding_kind_of_manual_implicit i,
      List.map (List.map binding_kind_of_manual_implicit) k
    | _ -> nYI "mutual inductives" in
  let ind = match mie.mind_entry_inds with
  | [ x ] -> x
  | _ -> nYI "mutual inductives" in
  let indno = 1 in
  let state = 
    S.update engine state (fun e ->
      { e with sigma = Evd.merge_context_set UState.univ_flexible e.sigma uctx}) in
  let state = match mie.mind_entry_universes with
    | Template_ind_entry _ -> nYI "template polymorphic inductives"
    | Monomorphic_ind_entry -> state
    | Polymorphic_ind_entry cs -> S.update engine state (fun e ->
        { e with sigma = Evd.merge_context_set UState.univ_flexible e.sigma (snd (UVars.UContext.to_context_set cs)) }) (* ???? *) in
  let state, upoly_decl_of, upoly_decl_gls = upoly_decl_of ~depth state ~loose_udecl mie in
  let allparams = mie.mind_entry_params in
  let allparams = Vars.lift_rel_context indno allparams in
  let kind = mie.mind_entry_finite in
  let nuparamsno =
    match nuparams with
    | Some x -> x
    | None ->
        let open Declarations in
        match kind with
        | BiFinite -> 0
        | Finite | CoFinite ->
          if (allparams <> []) then inference_nonuniform_params_off ();
          0 in
  let allparams = EConstr.of_rel_context allparams in
  let allparams = safe_combine2_impls allparams i_impls ~default2:Glob_term.Explicit |> param2ctx in
  let nuparams, params = CList.chop nuparamsno allparams in
  let id = ind.mind_entry_typename in
  let typ = EConstr.of_constr ind.mind_entry_arity in
  let constructors = List.combine ind.mind_entry_consnames ind.mind_entry_lc in
  let constructors = List.map (fun (id,typ) ->
    (* FIXME, arity could be longer *)
    { id; arity = nuparams; typ = EConstr.of_constr typ }) constructors in
  let ind = { params; decl = Inductive { id; nuparams; typ; kind; constructors } } in
  let state, i, gls = hoas_ind2lp ~depth coq_ctx state ind in
  state, upoly_decl_of i, gls @ upoly_decl_gls
;;

[%%if coq = "8.20" || coq = "9.0"]
let record_entry2lp ~depth coq_ctx constraints state ~loose_udecl e =
  let open Record.Record_decl in
  let open Record.Data in
  let open Entries in
  let { mie; impls; ubinders; globnames; global_univ_decls; records; _ } = e in
  let i_impls, k_impls = match impls with
    | [i,k] ->
      List.map binding_kind_of_manual_implicit i,
      List.map (List.map binding_kind_of_manual_implicit) k
    | _ -> nYI "mutual record" in
  let ind = match mie.mind_entry_inds with
  | [ x ] -> x
  | _ -> nYI "mutual record" in
  let record = match records with
  | [ x ] -> x
  | _ -> nYI "mutual record" in
  let indno = 1 in
    
  let state = global_univ_decls |> Option.cata (fun ctx ->
      S.update engine state (fun e ->
        { e with sigma = Evd.merge_context_set UState.univ_flexible e.sigma ctx})) state in

  let state = match mie.mind_entry_universes with
    | Template_ind_entry _ -> nYI "template polymorphic inductives"
    | Monomorphic_ind_entry -> state
    | Polymorphic_ind_entry cs -> S.update engine state (fun e ->
      { e with sigma = Evd.merge_context_set UState.univ_flexible e.sigma (snd (UVars.UContext.to_context_set cs)) }) (* ???? *) in
  
  let state, upoly_decl_of, upoly_decl_gls = upoly_decl_of ~depth state ~loose_udecl mie in

  let params = mie.mind_entry_params in
  let params = Vars.lift_rel_context indno params in

  let params = EConstr.of_rel_context params in
  let params = safe_combine2_impls params i_impls ~default2:Glob_term.Explicit |> param2ctx in
  let _paramsno = List.length params in

  let id = ind.mind_entry_typename in
  let typ = EConstr.of_constr ind.mind_entry_arity in
  let kid = List.hd ind.mind_entry_consnames in

  let fieldsno = List.length record.proj_flags in
  let kctx, _ = Term.decompose_prod_decls @@ List.hd ind.mind_entry_lc in
  let kctx = EConstr.of_rel_context kctx in
  if (List.length kctx != fieldsno) then CErrors.anomaly Pp.(str"record fields number != projections");

  let fields = List.map2 (fun { pf_coercion; pf_reversible; pf_canonical } -> 
    let open Context.Rel.Declaration in
    let coe_status = if pf_coercion then if pf_reversible then Reversible else Regular else Off in
    function
    | LocalAssum( { Context.binder_name = Anonymous },typ) ->
        { id = Id.of_string "_"; typ; extra = [Coercion coe_status; Canonical pf_canonical] }
    | LocalAssum( { Context.binder_name = Name id },typ) ->
        { id; typ; extra = [Coercion coe_status; Canonical pf_canonical] }
    | _ -> nYI "let-in in record fields"
    ) (List.rev record.proj_flags) kctx in

  let ind = { params; decl = Record { id; kid; typ; fields } } in
  let state, i, gls = hoas_ind2lp ~depth coq_ctx state ind in
  state, upoly_decl_of i, gls @ upoly_decl_gls
[%%else]
let record_entry2lp ~depth coq_ctx constraints state ~loose_udecl (decl:Record.Record_decl.t) =
  let open Record.Record_decl in
  let open Record.Data in
  let open Entries in
  let i_impls = List.map binding_kind_of_manual_implicit decl.entry.param_impls in

  let mie = decl.entry.mie in
  let ind = match mie.mind_entry_inds with
  | [ x ] -> x
  | _ -> nYI "mutual record"
  in
  let record = match decl.records with
  | [ x ] -> x
  | _ -> nYI "mutual record" in
  let indno = 1 in

  let state =
    S.update engine state (fun e ->
        { e with sigma = Evd.merge_context_set UState.univ_flexible e.sigma decl.entry.global_univs})
  in

  let state = match mie.mind_entry_universes with
    | Template_ind_entry _ -> nYI "template polymorphic inductives"
    | Monomorphic_ind_entry -> state
    | Polymorphic_ind_entry cs -> S.update engine state (fun e ->
      { e with sigma = Evd.merge_context_set UState.univ_flexible e.sigma (snd (UVars.UContext.to_context_set cs)) }) (* ???? *) in

  let state, upoly_decl_of, upoly_decl_gls = upoly_decl_of ~depth state ~loose_udecl mie in

  let params = mie.mind_entry_params in
  let params = Vars.lift_rel_context indno params in

  let params = EConstr.of_rel_context params in
  let params = safe_combine2_impls params i_impls ~default2:Glob_term.Explicit |> param2ctx in

  let id = ind.mind_entry_typename in
  let typ = EConstr.of_constr ind.mind_entry_arity in
  let kid = List.hd ind.mind_entry_consnames in

  let fieldsno = List.length record.proj_flags in
  let kctx, _ = Term.decompose_prod_decls @@ List.hd ind.mind_entry_lc in
  let kctx = EConstr.of_rel_context kctx in
  if (List.length kctx != fieldsno) then CErrors.anomaly Pp.(str"record fields number != projections");

  let fields = List.map2 (fun { pf_coercion; pf_reversible; pf_canonical } ->
    let open Context.Rel.Declaration in
    let coe_status = if pf_coercion then if pf_reversible then Reversible else Regular else Off in
    function
    | LocalAssum( { Context.binder_name = Anonymous },typ) ->
        { id = Id.of_string "_"; typ; extra = [Coercion coe_status; Canonical pf_canonical] }
    | LocalAssum( { Context.binder_name = Name id },typ) ->
        { id; typ; extra = [Coercion coe_status; Canonical pf_canonical] }
    | _ -> nYI "let-in in record fields"
    ) (List.rev record.proj_flags) kctx in

  let ind = { params; decl = Record { id; kid; typ; fields } } in
  let state, i, gls = hoas_ind2lp ~depth coq_ctx state ind in
  state, upoly_decl_of i, gls @ upoly_decl_gls
[%%endif]

let merge_universe_context state uctx =
  S.update engine state (fun e -> { e with sigma = Evd.merge_universe_context e.sigma uctx })

(* ********************************* }}} ********************************** *)
(* ****************************** API ********************************** *)

module CtxReadbackCache = Ephemeron.K1.Make(struct
  type t = API.Data.hyp list
  let equal = (==)
  let hash = Hashtbl.hash
end)
let ctx_cache_lp2c = CtxReadbackCache.create 1

let get_current_env_sigma ~depth hyps constraints state =
  let state, _, changed, gl1 = elpi_solution_to_coq_solution ~eta_contract_solution:true ~calldepth:depth constraints state in
  if changed then CtxReadbackCache.reset ctx_cache_lp2c;
  let state, coq_ctx, gl2 =
    match CtxReadbackCache.find ctx_cache_lp2c hyps with
    | (c,e,d) when d == depth && e == Global.env () -> state, c, []
    | _ ->
      of_elpi_ctx ~calldepth:depth constraints depth
        (preprocess_context (fun _ -> true) (E.of_hyps hyps))
        state (mk_coq_context ~options:(get_options ~depth hyps state) state)
    | exception Not_found -> 
        of_elpi_ctx ~calldepth:depth constraints depth
          (preprocess_context (fun _ -> true) (E.of_hyps hyps))
          state (mk_coq_context ~options:(get_options ~depth hyps state) state)
  in
  CtxReadbackCache.reset ctx_cache_lp2c;
  CtxReadbackCache.add ctx_cache_lp2c hyps (coq_ctx,Global.env (),depth);
  state, coq_ctx, get_sigma state, gl1 @ gl2
;;

let get_global_env_current_sigma ~depth hyps constraints state =
  let state, _, changed, gls = elpi_solution_to_coq_solution ~eta_contract_solution:true ~calldepth:depth constraints state in
  let coq_ctx = mk_coq_context ~options:(get_options ~depth hyps state) state in
  let coq_ctx = { coq_ctx with env = Environ.set_universes (Evd.universes (get_sigma state)) coq_ctx.env } in
  state, coq_ctx, get_sigma state, gls
;;

let rec lp2goal ~depth hyps syntactic_constraints state t =
  match get_goal_ref ~depth (E.constraints syntactic_constraints) state t with
  | Closed_by_side_effect -> assert false
  | Not_a_goal -> assert false
  | Open {ctx; evar = k; scope; args} ->
    let state, _, changed, gl1 =
      elpi_solution_to_coq_solution ~eta_contract_solution:true ~calldepth:depth syntactic_constraints state in
    if changed then lp2goal ~depth hyps syntactic_constraints state t
    else
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
  let gt = Rocq_elpi_utils.detype ?keepunivs:coq_ctx.options.keepunivs coq_ctx.env sigma t in
  let gt =
    let is_GRef_hole x =
      match DAst.get x with
      | Glob_term.GRef(r,None) -> Environ.QGlobRef.equal coq_ctx.env r (Coqlib.lib_ref "elpi.hole")
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

type module_item =
  | Module of Names.ModPath.t * module_item list
  | ModuleType of Names.ModPath.t
  | Gref of Names.GlobRef.t
  | Functor of Names.ModPath.t * Names.ModPath.t list
  | FunctorType of Names.ModPath.t * Names.ModPath.t list

[%%if coq = "8.20" || coq = "9.0"]
type 'a generic_module_body = 'a Declarations.generic_module_body
let module_view m = m.Declarations.mod_type
let mod_type m = m.Declarations.mod_type

let rec functor_params x =
  let open Declarations in
  match x with
  | MoreFunctor(_,{ mod_type_alg = Some (MENoFunctor (MEident mod_mp)) },rest) -> mod_mp :: functor_params rest
  | _ -> [] (* XXX non trivial functors, eg P : X with type a = nat, are badly described (no params) *)
[%%else]
type 'a generic_module_body = 'a Mod_declarations.generic_module_body
let module_view m = Mod_declarations.mod_type m
let mod_type = Mod_declarations.mod_type

let rec functor_params x =
  let open Declarations in
  match x with
  | MoreFunctor (_, mtb, rest) ->
    begin match Mod_declarations.mod_type_alg mtb with
    | Some (MENoFunctor (MEident mod_mp)) -> mod_mp :: functor_params rest
    | _ -> [] (* XXX *)
    end
  | _ -> [] (* XXX non trivial functors, eg P : X with type a = nat, are badly described (no params) *)
[%%endif]

let rec in_elpi_module_item ~depth path state (name, item) =
  let open Declarations in
  match item with
  | SFBconst _ ->
      [Gref (GlobRef.ConstRef (Constant.make2 path name))]
  | SFBmind { mind_packets } ->
      CList.init (Array.length mind_packets) (fun i -> Gref (GlobRef.IndRef (MutInd.make2 path name,i)))
  | SFBrules _ -> nYI "rewrite rules"
  | SFBmodule b ->
    let mod_mp = MPdot (path, name) in
    begin match module_view b with
    | NoFunctor _ -> [Module (mod_mp,in_elpi_module ~depth state mod_mp b) ]
    | (MoreFunctor _ as l) -> [Functor(mod_mp,functor_params l)]
    end
  | SFBmodtype m ->
    let mod_mp = MPdot (path, name) in
    begin match module_view m with
    | NoFunctor _ -> [ModuleType mod_mp]
    | (MoreFunctor _ as l) -> [FunctorType (mod_mp,functor_params l)]
    end

and in_elpi_module : 'a. depth:int -> API.Data.state -> ModPath.t -> 'a generic_module_body -> module_item list =
  fun ~depth state mp mb ->
  match mod_type mb with
  | Declarations.MoreFunctor _ -> nYI "functors"
  | Declarations.NoFunctor contents ->
      let l =
        CList.map (in_elpi_module_item ~depth mp state) contents in
      CList.flatten l

let rec in_elpi_modty_item (name, item) = match item with
  | Declarations.SFBconst _ ->
      [ Label.to_string name ]
  | Declarations.SFBmind _ ->
      [ Label.to_string name ]
  | SFBrules _ -> nYI "rewrite rules"
  | Declarations.SFBmodule mb -> in_elpi_modty mb
  | Declarations.SFBmodtype _ -> []

and in_elpi_modty : 'a.'a generic_module_body -> string list =
  fun mb ->
  match mod_type mb with
  | Declarations.MoreFunctor _ -> nYI "functors"
  | Declarations.NoFunctor contents ->
      CList.flatten (CList.map in_elpi_modty_item contents)

let in_elpi_module ~depth s mp x = in_elpi_module ~depth s mp x

let in_elpi_module_type x = in_elpi_modty x

(* ********************************* }}} ********************************** *)

(* vim:set foldmethod=marker: *)
