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
(* See also coq-term.elpi (terms)                                           *)
(* ************************************************************************ *)

(* {{{ CData ************************************************************** *)

(* names *)
let namein, isname, nameout, name =
  let { CD.cin; isc; cout }, name  = CD.declare {
    CD.name = "name";
    doc = "Name.Name.t: Name hints (in binders), can be input writing a name between backticks, e.g. `x` or `_` for anonymous. Important: these are just printing hints with no meaning, hence in elpi two @name are always related: `x` = `y`";
    pp = (fun fmt x ->
      Format.fprintf fmt "`%s`" (Pp.string_of_ppcmds (Name.print x)));
    eq = (fun _ _ -> true);
    hash = (fun _ -> 0);
    hconsed = false;
    constants = [];
  } in
  cin, isc, cout, name
;;
let in_elpi_name x = E.mkCData (namein x)

let is_coq_name ~depth t =
  match E.look ~depth t with
  | E.CData n -> isname n
  | _ -> false

let in_coq_name ~depth t =
  match E.look ~depth t with
  | E.CData n when isname n -> nameout n
  | E.CData n when CD.is_string n ->
     let s = CD.to_string n in
     if s = "_" then Name.Anonymous
     else Name.Name (Id.of_string s)
  | E.Discard -> Name.Anonymous
  | E.UnifVar _ -> Name.Anonymous
  | _ -> err Pp.(str"Not a name: " ++ str (API.RawPp.Debug.show_term t))

let in_coq_annot ~depth t = Context.make_annot (in_coq_name ~depth t) Sorts.Relevant

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
    eq = Univ.Universe.equal;
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
let equal_global_constat x y = match x,y with
  | Variable v1, Variable v2 -> Names.Id.equal v1 v2
  | Constant c1, Constant c2 -> Names.Constant.equal c1 c2
  | _ -> false

let constant, inductive, constructor = 
  let open API.OpaqueData in
  declare {
    name = "constant";
    doc = "global constant name";
    pp = (fun fmt x ->
      let x = match x with
        | Variable x -> Globnames.VarRef x
        | Constant c -> Globnames.ConstRef c in
      Format.fprintf fmt "«%s»" (Pp.string_of_ppcmds (Printer.pr_global x)));
    eq = equal_global_constat;
    hash = hash_global_constant;
    hconsed = false;
    constants = [];
  },
  declare {
    name = "inductive";
    doc = "inductive type name";
    pp = (fun fmt x -> Format.fprintf fmt "«%s»" (Pp.string_of_ppcmds (Printer.pr_global (Globnames.IndRef x))));
    eq = Names.eq_ind;
    hash = Names.ind_hash;
    hconsed = false;
    constants = [];
  },
  declare {
    name = "constructor";
    doc = "inductive constructor name";
    pp = (fun fmt x -> Format.fprintf fmt "«%s»" (Pp.string_of_ppcmds (Printer.pr_global (Globnames.ConstructRef x))));
    eq = Names.eq_constructor;
    hash = Names.constructor_hash;
    hconsed = false;
    constants = [];
  }
;;


let gref =
  let open Globnames in
  let open API.AlgebraicData in declare {
    ty = API.Conversion.TyName "gref";
    doc = "constants: inductive types, inductive constructors, definitions";
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
}

let in_elpi_gr ~depth s r =
  let s, t, gl = 
    gref.API.Conversion.embed ~depth [] API.RawData.no_constraints
      s r in
  assert (gl = []);
  E.mkAppS "global" t []

let globalc  = E.Constants.from_stringc "global"

let in_coq_gref ~depth s t =
  let s, t, gls =
    gref.API.Conversion.readback ~depth [] API.RawData.no_constraints s t in
  assert(gls = []);
  s, t

let mpin, ismp, mpout, modpath =
  let { CD.cin; isc; cout }, x = CD.declare {
    CD.name = "modpath";
    doc = "ModPath.t";
    pp = (fun fmt x ->
            Format.fprintf fmt "«%s»" (Names.ModPath.to_string x));
    eq = Names.ModPath.equal;
    hash = Names.ModPath.hash;
    hconsed = false;
    constants = [];
  } in
  cin, isc, cout, x
;;
let mptyin, istymp, mptyout, modtypath =
  let { CD.cin; isc; cout }, x = CD.declare {
    CD.name = "modtypath";
    doc = "ModTypePath.t";
    pp = (fun fmt x ->
            Format.fprintf fmt "«%s»" (Names.ModPath.to_string x));
    eq = Names.ModPath.equal;
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
let lamc   = E.Constants.from_stringc "fun"
let in_elpi_lam n s t = E.mkApp lamc (in_elpi_name n) [s;E.mkLam t]

let prodc  = E.Constants.from_stringc "prod"
let in_elpi_prod n s t = E.mkApp prodc (in_elpi_name n) [s;E.mkLam t]

let letc   = E.Constants.from_stringc "let"
let in_elpi_let n b s t = E.mkApp letc (in_elpi_name n) [s;b;E.mkLam t]

(* other *)
let appc   = E.Constants.from_stringc "app"
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

let matchc = E.Constants.from_stringc "match"
let in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs =
  E.mkApp matchc t [rt; U.list_to_lp_list bs]

let fixc   = E.Constants.from_stringc "fix"
let in_elpi_fix name rno ty bo =
  E.mkApp fixc (in_elpi_name name) [CD.of_int rno; ty; E.mkLam bo]

(* implicit *)
let holec   = E.Constants.from_stringc "hole"
let in_elpi_hole = E.mkConst holec

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : Evd.evar_map -> elpi *************************************** *)

let command_mode =
  S.declare ~name:"coq-elpi:command-mode"
    ~init:(fun () -> true)
    ~pp:(fun fmt b -> Format.fprintf fmt "%b" b)

module CoqEngine_HOAS : sig 

  type coq_engine  = {
   env : Environ.env; (* global env *)
   sigma : Evd.evar_map; (* universe constraints *)

  }

  val show_coq_engine : coq_engine -> string

  val engine : coq_engine S.component

  val empty_from_env : Environ.env -> coq_engine
  val empty_from_env_sigma : Environ.env -> Evd.evar_map -> coq_engine

end = struct

 type coq_engine = { 
   env : Environ.env [@printer (fun _ _ -> ())];
   sigma : Evd.evar_map [@printer (fun fmt m ->
     Format.fprintf fmt "%s" Pp.(string_of_ppcmds (Termops.pr_evar_map None (Global.env()) m)))];
 }
 [@@deriving show]

 let empty_from_env_sigma env sigma =
   {
     env;
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
  API.Conversion.readback = begin fun ~depth hyps constraints state t ->
    match E.look ~depth t with
    | E.UnifVar (b,args) ->
       let state, u = new_univ state in
       state, u, [ E.mkApp E.Constants.eqc (E.mkUnifVar b ~args state) [E.mkCData (univin u)]]
    | E.Discard ->
       let state, u = new_univ state in
       state, u, []
    | _ ->
       univ_to_be_patched.API.Conversion.readback ~depth hyps constraints state t
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
}

let sortc  = E.Constants.from_stringc "sort"

let in_elpi_sort s =
  E.mkApp
    sortc
    (match s with
    | Sorts.SProp -> E.mkGlobalS "sprop"
    | Sorts.Prop -> E.mkGlobalS "prop"
    | Sorts.Set -> E.mkAppS "typ" (E.mkCData (univin Univ.type0_univ)) []
    | Sorts.Type u -> E.mkAppS "typ" (E.mkCData (univin u)) [])
    []

let in_elpi_flex_sort t = E.mkApp sortc (E.mkAppS "typ" t []) []

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : EConstr.t -> elpi ******************************************* *)

let rec pos name cur = function
  | [] -> None
  | Name n :: _ when Names.Id.equal n name -> Some cur
  | Name _ :: xs -> pos name (cur+1) xs
  | Anonymous :: xs -> pos name cur xs

let check_univ_inst univ_inst =
  if not (Univ.Instance.is_empty univ_inst) then
    nYI "HOAS universe polymorphism"
    
let get_sigma s = (S.get engine s).sigma
let get_env s = (S.get engine s).env

let declare_evc = E.Constants.from_stringc "declare-evar"

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

type coq_proof_ctx_names = Name.t list * int

let declc = E.Constants.from_stringc "decl"
let defc = E.Constants.from_stringc "def"
let evarc = E.Constants.from_stringc "evar"

let mk_pi_arrow hyp rest =
  E.mkApp E.Constants.pic (E.mkLam (E.mkApp E.Constants.implc hyp [rest])) []

let mk_decl ~depth name ~ty =
  E.mkApp declc E.(mkConst depth) [in_elpi_name name; ty]

let mk_def ~depth name ~bo ~ty ~ctx_len state =
  let state, k = F.Elpi.make ~lvl:0 state in
  let norm = E.mkUnifVar k ~args:(CList.init ctx_len E.mkConst) state in
  state, E.mkApp defc E.(mkConst depth) [in_elpi_name name; ty; bo; norm]

(* Maps a Coq name (bound in the context) to its De Bruijn level
 * The type (and optionally body) is given by the hyps. Each hyp is generated
 * at a depth level, and it may need to be pushed down. Cfr:
 *
 *  pi x\ decl x t => py y\ def y t b => ....
 *  pi x y\ decl x t => def y t b => ....
 *
 * Given that a priori you may not know the size of the context things are
 * generated in the first form, and eventually lifted down. *)
type hyp = { ctx_entry : E.term; depth : int }
type coq2lp_ctx = { coq_name2dbl : int Id.Map.t; hyps : hyp list }

let empty_coq2lp_ctx = { coq_name2dbl = Id.Map.empty; hyps = [] }

let push_coq2lp_ctx ~depth n ctx_entry ctx = {
  coq_name2dbl = Id.Map.add n depth ctx.coq_name2dbl;
  hyps = { ctx_entry ; depth = depth + 1 } :: ctx.hyps
}

let pp_coq2lp_ctx fmt { coq_name2dbl; hyps } =
  Id.Map.iter (fun name d ->
    Format.fprintf fmt "@[%s |-> %a@]" (Id.to_string name)
      (P.term d) (E.mkConst d))
    coq_name2dbl;
  Format.fprintf fmt "@[<hov>";
  List.iter (fun { ctx_entry; depth } ->
    Format.fprintf fmt "%a@ "
      (P.term depth) ctx_entry)
    hyps
;;

let rec constr2lp (proof_ctx, proof_ctx_len) ~calldepth ~depth state t =
  assert(depth >= proof_ctx_len);
  let { sigma } = S.get engine state in
  let gls = ref [] in
  let rec aux ~depth state t = match EC.kind sigma t with
    | C.Rel n -> state, E.mkConst (depth - n)
    | C.Var n ->
         begin match pos n 0 proof_ctx with
         | Some i -> state, E.mkConst i
         | None -> state, in_elpi_gr ~depth state (G.VarRef n)
         end
    | C.Meta _ -> nYI "constr2lp: Meta"
    | C.Evar (k,args) ->
        (* the evar is created at the depth the conversion is called, not at
          the depth at which it is found *)
         let state, elpi_uvk, gsl_t = in_elpi_evar ~calldepth k state in
         gls := gsl_t @ !gls;          
         let section_len = List.length (section_ids (S.get engine state).env) in
         let args = Array.sub args 0 (Array.length args - section_len) in
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
         if G.equal ref (Coqlib.lib_ref "elpi.hole") then state, in_elpi_hole
         else state, in_elpi_gr ~depth state ref
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
  in
  if debug () then
    Feedback.msg_debug Pp.(str"term2lp: depth=" ++ int depth ++
      str " ctx=" ++ pr_sequence Name.print proof_ctx ++
      str " term=" ++Printer.pr_econstr_env (get_env state) (get_sigma state) t);
  let state, t = aux ~depth state t in
  if debug () then
    Feedback.msg_debug Pp.(str"term2lp (out): " ++
      str (pp2string (P.term depth) t));
  state, t, !gls

and in_elpi_ctx ~calldepth state ctx ?(mk_ctx_item=mk_pi_arrow) kont =
  let open Context.Named.Declaration in
  let gls = ref [] in
  let rec aux ~depth (ctx, ctx_len as ctx_w_len) coq2lp_ctx state = function
    | [] ->
        let coq2lp_ctx = { coq2lp_ctx with hyps = List.rev coq2lp_ctx.hyps } in
        let state, t, gls_t = kont (ctx, ctx_len) coq2lp_ctx ~depth state in
        gls := gls_t @ !gls;
        state, t
    | LocalAssum (Context.{binder_name=coq_name}, ty) :: rest ->
        let name = Name coq_name in
        let state, ty, gls_ty = constr2lp ctx_w_len ~calldepth ~depth:(depth+1) state ty in
        gls := gls_ty @ !gls;
        let hyp = mk_decl ~depth name ~ty in
        let coq2lp_ctx = push_coq2lp_ctx ~depth coq_name hyp coq2lp_ctx in
        let ctx_w_len = ctx @ [name], ctx_len+1 in
        let state, rest = aux ~depth:(depth+1) ctx_w_len coq2lp_ctx state rest in
        state, mk_ctx_item hyp rest
      | LocalDef (Context.{binder_name=coq_name},bo,ty) :: rest ->
        let name = Name coq_name in
        let state, ty, gls_ty = constr2lp ctx_w_len ~calldepth ~depth:(depth+1) state ty in
        let state, bo, gls_bo = constr2lp ctx_w_len ~calldepth ~depth:(depth+1) state bo in
        gls := gls_ty @ gls_bo @ !gls;
        let state, hyp = mk_def ~depth name ~bo ~ty ~ctx_len state in
        let coq2lp_ctx = push_coq2lp_ctx ~depth coq_name hyp coq2lp_ctx in
        let ctx_w_len = ctx @ [name], ctx_len+1 in
        let state, rest = aux ~depth:(depth+1) ctx_w_len coq2lp_ctx state rest in
        state, mk_ctx_item hyp rest
  in
    let state, t = aux ~depth:calldepth ([],0) empty_coq2lp_ctx state (List.rev ctx) in
    state, t, !gls

and in_elpi_evar_concl evar_concl elpi_revk elpi_evk (_, ctx_len as ctx) ~scope { hyps } ~calldepth ~depth state =
  let state, evar_concl, gls_evar_concl = constr2lp ctx ~calldepth ~depth state evar_concl in
  let args = CList.init scope (fun i -> E.mkConst @@ i + calldepth) in
  let hyps = List.map (fun { ctx_entry; depth = from } ->
    U.move ~from ~to_:depth ctx_entry) hyps in
  state, U.list_to_lp_list hyps,
  (E.mkUnifVar elpi_revk ~args state),
  (E.mkUnifVar elpi_evk ~args state),
  evar_concl, gls_evar_concl

and in_elpi_evar_info ~calldepth ~env ~sigma ctx elpi_revk elpi_evk evar_concl state =
  in_elpi_ctx ~calldepth state ctx (fun (ctx, ctx_len) coq2lp_ctx ~depth state ->
    let state, hyps, raw_ev, ev, ty, gls =
      in_elpi_evar_concl evar_concl elpi_revk elpi_evk (ctx,ctx_len) ~scope:ctx_len coq2lp_ctx
        ~calldepth ~depth state in
    state, E.mkApp declare_evc hyps [raw_ev; ty; ev], gls)

and in_elpi_evar ~calldepth k state =
  if debug () then Feedback.msg_debug Pp.(str"in_elpi_evar:" ++ Evar.print k);
  try
    let elpi_evk = UVMap.elpi k (S.get UVMap.uvmap state) in
    if debug () then Feedback.msg_debug Pp.(str"in_elpi_evar: known " ++
      Evar.print k ++ str" as " ++ str(F.Elpi.show elpi_evk));
    state, elpi_evk, []
  with Not_found ->
    let state, elpi_evk = F.Elpi.make ~lvl:0 state in
    let state, elpi_raw_evk = F.Elpi.make ~lvl:0 state in
    let state, gls = in_elpi_fresh_evar ~calldepth k elpi_raw_evk elpi_evk state in
    state, elpi_evk, gls

and in_elpi_fresh_evar ~calldepth k elpi_raw_evk elpi_evk state =
    let { sigma; env } as e = S.get engine state in
    let state = S.update UVMap.uvmap state (UVMap.add elpi_evk k) in
    if debug () then Feedback.msg_debug Pp.(str"in_elpi_fresh_evar: unknown " ++ Evar.print k);
    let evar_concl, ctx, _ = info_of_evar ~env ~sigma ~section:(section_ids env) k in
    let state, evar_decl, gls = in_elpi_evar_info ~calldepth ~env ~sigma ctx elpi_raw_evk elpi_evk evar_concl state in
    if debug () then Feedback.msg_debug Pp.(str"in_elpi_fresh_evar: new decl" ++ cut () ++
      str(pp2string (P.term calldepth) evar_decl));
    state, gls @ [evar_decl]
;;

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : elpi -> Constr.t * Evd.evar_map ***************************** *)

let in_coq_hole () =
  EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref "elpi.hole"))

let add_constraints state c = S.update engine state (fun ({ sigma } as x) ->
  { x with sigma = Evd.add_universe_constraints sigma c })


let type_of_global state r = S.update_return engine state (fun x ->
  let ty, ctx = Typeops.type_of_global_in_context x.env r in
  let inst, ctx = UnivGen.fresh_instance_from ctx None in
  let ty = Vars.subst_instance_constr inst ty in
  let sigma = Evd.merge_context_set Evd.univ_rigid x.sigma ctx in
  { x with sigma }, EConstr.of_constr ty)

let body_of_constant state c = S.update_return engine state (fun x ->
  match Global.body_of_constant_body (Environ.lookup_constant c x.env) with
  | Some (bo, ctx) ->
     let inst, ctx = UnivGen.fresh_instance_from ctx None in
     let bo = Vars.subst_instance_constr inst bo in
     let sigma = Evd.merge_context_set Evd.univ_rigid x.sigma ctx in
     { x with sigma }, Some (EConstr.of_constr bo)
  | None -> x, None)

let new_evar info state =
  S.update_return engine state (fun ({ sigma } as x) ->
     let sigma, k = Evd.new_evar sigma info in
     { x with sigma }, k)

let evar_arity k state =
  let { Evd.evar_hyps } = Evd.find (S.get engine state).sigma k in
  List.length (Environ.named_context_of_val evar_hyps)

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

exception Undeclared_evar of int (*depth*) * E.term

let pp_cst fmt { E.goal = (depth,concl); context } =
  Format.fprintf fmt "%d |> %a |- %a" depth
    (P.list (fun fmt { E.hdepth; E.hsrc } ->
        Format.fprintf fmt "%d:%a" hdepth (P.term hdepth) hsrc) ", ")
      context
     (P.term depth) concl

let find_evar var syntactic_constraints =
  let is_evar depth t =
    match E.look ~depth t with
    | E.App(c,x,[t;rx]) when c == evarc ->
          Some(E.look ~depth x,E.look ~depth rx,t)
    | _ -> None in
    CList.find_map (fun ({ E.goal = (depth,concl); context } as cst) ->
      if debug () then
        Feedback.msg_debug Pp.(str"lp2term: evar: constraint: " ++
          str(pp2string pp_cst cst)); 
      match is_evar depth concl with
      | Some(E.UnifVar(raw,_),E.UnifVar(r,_),ty) when F.Elpi.(equal raw var || equal r var) ->
          Some (context, raw, r, (depth,ty))
      | _ -> None) syntactic_constraints

exception Undeclared_ctx_entry of int (*depth*) * E.term

let nth_name ~depth l n =
  match List.nth l n with
  | Name id -> id
  | Anonymous -> raise (Undeclared_ctx_entry(depth,E.mkConst n))

let get_id = function Name.Anonymous -> Id.of_string "_" | Name x -> x


let rec of_elpi_ctx syntactic_constraints depth hyps state =

  let mk_fresh =
    let i = ref 0 in
    fun n ->
      incr i;
      Name.mk_name
        (Id.of_string_soft
          (Printf.sprintf "_elpi_renamed_%s_%d_" n !i)) in
  let in_coq_fresh_name ~depth name names =
    match in_coq_name ~depth name with
    | Name.Anonymous -> mk_fresh "Anonymous"
    | Name.Name id as x when List.mem x names ->
        mk_fresh (Id.to_string id)
    | x -> x in

  let aux names depth state t =
    lp2constr ~tolerate_undef_evar:false syntactic_constraints names ~depth state t in

  let of_elpi_ctx_entry (names,n_names as proof_ctx) ~depth e state =
    match e with
    | `Decl(name,ty) ->
        let name = in_coq_fresh_name ~depth name names in
        let id = get_id name in
        let state, ty, gls = aux proof_ctx depth state ty in
        state, name, Context.Named.Declaration.LocalAssum(Context.make_annot id Sorts.Relevant,ty), gls
    | `Def(name,ty,bo) ->
        let name = in_coq_fresh_name ~depth name names in
        let id = get_id name in
        let state, ty, gl1 = aux proof_ctx depth state ty in
        let state, bo, gl2 = aux proof_ctx depth state bo in
        state, name, Context.Named.Declaration.LocalDef(Context.make_annot id Sorts.Relevant,bo,ty), gl1 @ gl2
  in

  let select_ctx_entries { E.hdepth = depth; E.hsrc = t } =
    let isConst t = match E.look ~depth t with E.Const _ -> true | _ -> false in
    let destConst t = match E.look ~depth t with E.Const x -> x | _ -> assert false in
    match E.look ~depth t with
    | E.App(c,v,[name;ty]) when c == declc && isConst v ->
       Some (destConst v, depth, `Decl(name,ty))
    | E.App(c,v,[name;ty;bo;_]) when c == defc && isConst v ->
       Some (destConst v, depth, `Def (name,ty,bo))
    | _ ->
        if debug () then            
          Feedback.msg_debug Pp.(str "skip entry" ++
            str(pp2string (P.term depth) t));
        None
  in
  let ctx_hyps = CList.map_filter select_ctx_entries hyps in
  let dbl2ctx =
    List.fold_right (fun (i,d,e) m ->
      if Int.Map.mem i m
      then err Pp.(str "Duplicate context entry for " ++
                   str(pp2string (P.term d) (E.mkConst i)))
      else Int.Map.add i (d,e) m)
    ctx_hyps Int.Map.empty in
  
  let rec ctx_entries ctx (n,n_no as proof_ctx) to_restrict state gls i =
    if i = depth then state, ctx, proof_ctx, to_restrict, List.(concat (rev gls))
    else (* context entry for the i-th variable *)
      if not (Int.Map.mem i dbl2ctx)
      then ctx_entries ctx (n@[Anonymous],n_no+1) (i::to_restrict) state gls (i+1)
      else
        let d, e = Int.Map.find i dbl2ctx in
        let state, name, e, gl1 = of_elpi_ctx_entry proof_ctx ~depth:d e state in
        ctx_entries (e::ctx) (n@[name],n_no+1) to_restrict state (gl1 :: gls) (i+1)
  in
    ctx_entries [] ([],0) [] state [] 0

(* ***************************************************************** *)
(* <-- depth -->                                                     *)
(* names |- pis |- t                                                 *)
(*   |        \- lp fresh constans                                   *)
(*   \- proof_ctx                                                    *)
(* ***************************************************************** *)

and lp2constr ~tolerate_undef_evar syntactic_constraints (names,n_names as ctx) ~depth state t =
  let aux = lp2constr ~tolerate_undef_evar syntactic_constraints ctx in
  let aux_lam ~depth s t = match E.look ~depth t with
  | E.Lam t -> aux ~depth:(depth+1) s t
  | E.UnifVar(r,args) ->
       aux ~depth:(depth+1) s (E.mkUnifVar r ~args:(List.map (U.move ~from:depth ~to_:(depth+1)) args @ [E.mkConst depth]) state)
  | _ -> err Pp.(str"HOAS: expecting a lambda, got: " ++
           str(pp2string (P.term depth) t)) in
  match E.look ~depth t with
  | E.App(s,p,[]) when sortc == s ->
      let state, u, gsl = universe.API.Conversion.readback ~depth [] syntactic_constraints state p in
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
      let name = in_coq_annot ~depth name in
      let state, s, gl1 = aux ~depth state s in
      let state, t, gl2 = aux_lam ~depth state t in
      if lamc == c then state, EC.mkLambda (name,s,t), gl1 @ gl2
      else state, EC.mkProd (name,s,t), gl1 @ gl2
  | E.App(c,name,[s;b;t]) when letc == c ->
      let name = in_coq_annot ~depth name in
      let state, s, gl1 = aux ~depth state s in
      let state, b, gl2 = aux ~depth state b in
      let state, t, gl3 = aux_lam ~depth state t in
      state, EC.mkLetIn (name,b,s,t), gl1 @ gl2 @ gl3
      
  | E.Const n ->
                  
     if n == holec then 
       state, in_coq_hole (), []
     else if n >= 0 then
       if n < n_names then state, EC.mkVar(nth_name ~depth names n), []
       else if n < depth then state, EC.mkRel(depth - n), []
       else 
         err Pp.(str"wrong bound variable (BUG):" ++ str (E.Constants.show n))
     else
        err Pp.(str"wrong constant:" ++ str (E.Constants.show n))
 (* app *)
  | E.App(c,x,[]) when appc == c ->
       (match U.lp_list_to_list ~depth x with
       | x :: xs -> 
          let state, x, gl1 = aux ~depth state x in
          let state, xs, gl2 = API.Utils.map_acc (aux ~depth) state xs in
          state, EC.mkApp (x, Array.of_list xs), gl1 @ gl2
       | _ -> assert false) (* TODO *)
  
  (* match *)
  | E.App(c,t,[rt;bs]) when matchc == c ->
      let state, t, gl1 = aux ~depth state t in
      let state, rt, gl2 = aux ~depth state rt in
      let state, bt, gl3 =
        API.Utils.map_acc (aux ~depth) state (U.lp_list_to_list ~depth bs) in
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
        Inductiveops.make_case_info (get_env state) ind Sorts.Relevant C.RegularStyle in
      state, EC.mkCase (ci,rt,t,Array.of_list bt), gl1 @ gl2 @ gl3
 (* fix *)
  | E.App(c,name,[rno;ty;bo]) when fixc == c ->
      let name = in_coq_annot ~depth name in
      let state, ty, gl1 = aux ~depth state ty in
      let state, bo, gl2 = aux_lam ~depth state bo in
      let rno =
        match E.look ~depth rno with
        | E.CData n when CD.is_int n -> CD.to_int n
        | _ -> err Pp.(str"Not an int: " ++ str (P.Debug.show_term rno)) in
      state, EC.mkFix (([|rno|],0),([|name|],[|ty|],[|bo|])), gl1 @ gl2
  
  (* evar *)
  | E.UnifVar (elpi_evk,orig_args) as x ->
      if debug () then
        Feedback.msg_debug Pp.(str"lp2term: evar: " ++
          str (pp2string (P.term depth) (E.kool x)));
      let lvl = F.Elpi.lvl elpi_evk in
      let args = CList.init lvl E.mkConst @ orig_args in
      begin try
        let ext_key = UVMap.host elpi_evk (S.get UVMap.uvmap state) in

        if debug () then
          Feedback.msg_debug Pp.(str"lp2term: evar: already in Coq: " ++
          Evar.print ext_key);

        let state, args, gl1 = API.Utils.map_acc (aux ~depth) state args in
        let args = List.rev args in
        let section_args =
          CList.rev_map EC.mkVar (section_ids (S.get engine state).env) in
        let arity = evar_arity ext_key state in
        let ev =
          let all_args = args @ section_args in
          let nargs = List.length all_args in
          if nargs > arity then
            let args1, args2 = CList.chop (nargs - arity) all_args in
            EC.mkApp(EC.mkEvar (ext_key,Array.of_list args2),
                       CArray.rev_of_list args1)
          else EC.mkEvar (ext_key,Array.of_list (args @ section_args)) in
        state, ev, gl1
      with Not_found ->
        let context, elpi_revk, elpi_evk, ty =
          try
            find_evar elpi_evk (E.constraints syntactic_constraints)
          with
          | Not_found when tolerate_undef_evar ->
              (* pretty printing should not fail *)
              [], elpi_evk, elpi_evk, (0, in_elpi_sort Sorts.prop)
          | Not_found ->
              raise (Undeclared_evar(depth,t))
        in
        let state, k, gl1 = declare_evar ~tolerate_undef_evar elpi_revk elpi_evk syntactic_constraints context ty state in
        if debug () then Feedback.msg_debug Pp.(str"lp2term: evar: declared new: " ++
          Evar.print k ++ str" = " ++ str(F.Elpi.show elpi_evk));
        let x =
          (* eta contraction in elpi *)
          let missing = List.length context - List.length args in
          if missing <= 0 then t else
          let ano = List.length args in
          let extra = CList.init missing (fun i -> E.mkConst(i+ano)) in
          E.mkUnifVar elpi_evk ~args:(orig_args @ extra) state
          in
        if debug () then Feedback.msg_debug Pp.(str"lp2term: evar: instance: " ++
           str (pp2string (P.term depth) t) ++ str"  ->  " ++
           str (pp2string (P.term depth) x));
        let state, x, gls = aux ~depth state x in
        state, x, gl1 @ gls
      end

  (* errors *)
  | E.Lam _ ->
       err Pp.(str "out of place lambda: "++
               str (pp2string P.(term depth) t))
  | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Debug.show_term t))

  (* evar info read back *)

and declare_evar ~tolerate_undef_evar elpi_revk elpi_evk syntactic_constraints ctx (depth_concl,concl) state =
  let state, named_ctx, (names,n_names), to_restrict, gl1 = (* TODO: honor restrict *)
    of_elpi_ctx syntactic_constraints depth_concl ctx state in
  if debug () then
    Feedback.msg_debug Pp.(str"lp2term: evar: new: " ++ int depth_concl ++ str" |> " ++
      pr_sequence Name.print names ++ str" |- " ++
      str(pp2string (P.term depth_concl) concl));
  let state, ty, gl2 = lp2constr ~tolerate_undef_evar syntactic_constraints (names,n_names) ~depth:depth_concl state concl in
  let named_ctx =
    named_ctx @ EC.named_context (S.get engine state).env in
  if debug () then
    Feedback.msg_debug Pp.(str"lp2term: evar: new: " ++
     let { sigma; env } = S.get engine state in
     Printer.pr_named_context env sigma (Obj.magic named_ctx) ++ str " |- " ++
     Printer.pr_econstr_env (EConstr.push_named_context named_ctx env) sigma ty);
  let info = Evd.make_evar (EC.val_of_named_context named_ctx) ty in
  let state, k = new_evar info state in
  let state = S.update UVMap.uvmap state (UVMap.add elpi_evk k) in
  if debug () then
    Feedback.msg_debug Pp.(str"lp2term: evar: new info: " ++
      Evar.print k ++ str " info= " ++
        let { sigma; env } = S.get engine state in
        Termops.pr_evar_info env sigma info);
  state, k, gl1 @ gl2
;;

let lp2constr ~tolerate_undef_evar syntactic_constraints proof_ctx ~depth state t =
  try
    if debug () then
      Feedback.msg_debug Pp.(str"lp2term: depth=" ++ int depth ++
        str " ctx=[" ++ pr_sequence Name.print (fst proof_ctx) ++ str"]" ++
        str " term=" ++ str (pp2string (P.term depth) t));
    let state, t, gls = lp2constr ~tolerate_undef_evar syntactic_constraints proof_ctx ~depth state t in
    if debug () then
      Feedback.msg_debug Pp.(str"lp2term: out=" ++ 
        (Printer.pr_econstr_env (S.get engine state).env
                                (S.get engine state).sigma t) ++
        str "elpi2coq=" ++ str(UVMap.show (S.get UVMap.uvmap state)));
    state, t, gls
  with
  | Undeclared_evar(x_depth,x) ->
    err Pp.(str"The term "++
      str(pp2string P.(term depth) t) ++ 
      str" contains the unification variable " ++
      str(pp2string P.(term x_depth) x) ++
      str" that has no declared type in the constraint store:" ++ spc() ++
      str(pp2string P.(list (fun fmt { E.goal = (depth,t) } ->
             term depth fmt t) ", ")
          (E.constraints syntactic_constraints)))
  | Undeclared_ctx_entry(x_depth,x) ->
    err Pp.(str"The term "++
      str(pp2string P.(term depth) t) ++ 
      str" contains the name " ++
      str(pp2string P.(term x_depth) x) ++
      str" that has no declared type in the context:" ++
      prlist_with_sep spc Names.Name.print (fst proof_ctx))

let of_elpi_ctx syntactic_constraints depth hyps state =
  try
    of_elpi_ctx syntactic_constraints depth hyps state
  with
  | Undeclared_evar(x_depth,x) ->
    err Pp.(str"The hypothetical context "++
      str(pp2string P.(list (fun fmt { E.hdepth; hsrc } ->
             term hdepth fmt hsrc) ",") hyps) ++
      str" contains the unification variable " ++
      str(pp2string P.(term x_depth) x) ++
      str" that has no declared type in the constraint store:" ++ spc() ++
      str(pp2string P.(list (fun fmt { E.goal = (depth,t) } ->
             term depth fmt t) ",")
          (E.constraints syntactic_constraints)))
  | Undeclared_ctx_entry(x_depth,x) ->
      err Pp.(str"The hypothetical context "++
      str(pp2string P.(list (fun fmt { E.hdepth; hsrc } ->
             term hdepth fmt hsrc) ",") hyps) ++
      str" contains the name " ++
      str(pp2string P.(term x_depth) x) ++
      str" that has no declared type in the context")



(* ********************************* }}} ********************************** *)


(*
let cs_get_solution2ev state = (CS.get engine state).solution2ev
*)
let push_env state name =
  let open Context.Rel.Declaration in
  S.update engine state (fun ({ env } as x) ->
     { x with env = Environ.push_rel (LocalAssum(name,C.mkProp)) env })
let pop_env state =
  S.update engine state (fun ({ env } as x) ->
     { x with env = Environ.pop_rel_context 1 env })

let get_global_env_sigma state =
  let { env; sigma } = S.get engine state in
  Environ.push_context_set (Evd.universe_context_set sigma) env, sigma


let set_sigma state sigma = S.update engine state (fun x -> { x with sigma })

(* We reset the evar map since it depends on the env in which it was created *)
let grab_global_env state =
  let env = Global.env () in
  S.update engine state (fun _ -> CoqEngine_HOAS.empty_from_env env)



let solvec = E.Constants.from_stringc "solve"
let goalc = E.Constants.from_stringc "goal"
let nablac = E.Constants.from_stringc "nabla"
let goal_namec = E.Constants.from_stringc "goal-name"

let mk_goal hyps ev ty attrs =
  E.mkApp goalc hyps [ev;ty; U.list_to_lp_list attrs]

let in_elpi_goal ?goal_name ~hyps ~raw_ev ~ty =
  let name = match goal_name with None -> Anonymous | Some x -> Name x in
  let name = E.mkApp goal_namec (in_elpi_name name) [] in
  E.mkCons (mk_goal hyps raw_ev ty [name]) E.mkNil

let in_elpi_solve ?goal_name ~hyps ~raw_ev ~ty ~args ~new_goals =
  let g = in_elpi_goal ?goal_name ~hyps ~raw_ev ~ty in
  E.mkApp solvec args [g; new_goals]

let embed_goal ~depth state k =
  let calldepth = depth in
  let env = get_env state in
  let sigma = get_sigma state in
  let state, elpi_goal_evar = F.Elpi.make ~lvl:0 state in
  let state, elpi_raw_goal_evar = F.Elpi.make ~lvl:0 state in
  let state, evar_decls = in_elpi_fresh_evar ~calldepth k elpi_raw_goal_evar elpi_goal_evar state in
  let evar_concl, goal_ctx, goal_env =
    info_of_evar ~env ~sigma ~section:(section_ids env) k in
  let goal_name = Evd.evar_ident k sigma in
  in_elpi_ctx ~calldepth state goal_ctx
     ~mk_ctx_item:(fun _ t -> E.mkApp nablac (E.mkLam t) [])
     (fun (ctx, ctx_len) coq2lp_ctx ~depth state ->
          let state, hyps, raw_ev, _, goal_ty, gls =
            in_elpi_evar_concl evar_concl elpi_raw_goal_evar elpi_goal_evar
              (ctx, ctx_len) ~scope:ctx_len coq2lp_ctx ~calldepth ~depth state in
         state, in_elpi_goal ?goal_name ~hyps ~raw_ev ~ty:goal_ty, gls)

let goal2query env sigma goal loc ?main args ~in_elpi_arg ~depth:calldepth state =
  if not (Evd.is_undefined sigma goal) then
    err Pp.(str (Printf.sprintf "Evar %d is not a goal" (Evar.repr goal)));

  let state = S.set command_mode state false in (* tactic mode *)

  let state = S.set engine state (empty_from_env_sigma env sigma) in

  let state, elpi_goal_evar = F.Elpi.make ~lvl:0 state in
  let state, elpi_raw_goal_evar = F.Elpi.make ~lvl:0 state in
  let state, evar_decls = in_elpi_fresh_evar ~calldepth goal elpi_raw_goal_evar elpi_goal_evar state in


  let evar_concl, goal_ctx, goal_env =
    info_of_evar ~env ~sigma ~section:(section_ids env) goal in
  let goal_name = Evd.evar_ident goal sigma in

  let state, query, gls =
    in_elpi_ctx ~calldepth state goal_ctx
     ~mk_ctx_item:(fun _ t -> E.mkApp E.Constants.pic (E.mkLam t) [])
     (fun (ctx, ctx_len) coq2lp_ctx ~depth state ->
      match main with
      | None ->
          let state, hyps, raw_ev, _, goal_ty, gls =
            in_elpi_evar_concl evar_concl elpi_raw_goal_evar elpi_goal_evar
              (ctx, ctx_len) ~scope:ctx_len coq2lp_ctx ~calldepth ~depth state in

          let state, ek = F.Elpi.make ~name:"NewGoals" ~lvl:calldepth state in

          let new_goals = E.mkUnifVar ek ~args:(CList.init ctx_len E.mkConst) state in
            
          let state, args =
            CList.fold_left_map (in_elpi_arg ~depth goal_env coq2lp_ctx sigma) state args in
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
         let _ctx, _raw_ev, ev, _ty = find_evar ev syntactic_constraints in
         Some (UVMap.host ev (S.get UVMap.uvmap state))
       with Not_found ->
              CErrors.anomaly Pp.(str(pp2string (P.term depth) g) ++ str " not part of elpi2coq")
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
  | E.Discard | E.UnifVar _ -> true
  | _ -> false

let rec skip_lams ~depth d t = match E.look ~depth t with
  | E.Lam t -> skip_lams ~depth:(depth+1) (d+1) t
  | x -> x, d

let show_engine state =
  show_coq_engine (S.get engine state) ^ "\nCoq-Elpi mapping: " ^
  UVMap.show (S.get UVMap.uvmap state)

let elpi_solution_to_coq_solution syntactic_constraints state =
  let { sigma; env } as e = S.get engine state in
  
  if debug () then
    Feedback.msg_debug Pp.(str"engine in:\n" ++ str (show_coq_engine e));

  let state, unassigned, changed, extra_gls =
    UVMap.fold (fun k elpi_evk solution (state, unassigned, changed, extra) ->
      match solution with
      | None -> (state, Evar.Set.add k unassigned, changed, extra)
      | Some (depth,t) ->
(* TODO: return a boolean to know if something changed *)
       let _, ctx, _ = info_of_evar ~env ~sigma ~section:(section_ids env) k in

       let names, n_names = 
         Context.Named.fold_inside
           (fun (acc,n) x ->
              Name (Context.Named.Declaration.get_id x) :: acc, n+1)
           ~init:([],0) ctx in

      if debug () then
        Feedback.msg_debug Pp.(str"solution for "++ Evar.print k ++ str" in ctx=" ++
          pr_sequence Name.print names ++ str" at depth=" ++ int n_names ++ str"<-"++ int depth ++
          str " id term=" ++ str(pp2string (P.term depth) t));

       let t = eat_n_lambdas ~depth t n_names state in
      if debug () then
        Feedback.msg_debug Pp.(str"lambda-less solution for "++ Evar.print k ++ str" in ctx=" ++
          pr_sequence Name.print names ++ str" at depth=" ++ int n_names ++
          str " is term=" ++ str(pp2string (P.term n_names) t));

       let state, t, gls =
         lp2constr ~tolerate_undef_evar:false
           syntactic_constraints (names, n_names) ~depth:n_names state t in

       let { sigma; env } as e = S.get engine state in
       
       if debug () then
         Feedback.msg_debug Pp.(str"solution for "++ Evar.print k ++ str" is constr=" ++
           Printer.pr_econstr_env env sigma t);

       let sigma = Evd.define k t sigma in

       let unassigned = Evar.Set.union unassigned (Evarutil.undefined_evars_of_term sigma t) in
       (* since the order in which we add is not topological*)
       let unassigned = Evar.Set.remove k unassigned in

       S.set engine state { e with sigma }, unassigned, true, gls :: extra) (S.get UVMap.uvmap state) 
     (state, Evar.Set.empty, false, [])
  in
    
  let state = S.update UVMap.uvmap state (UVMap.filter (fun k _ -> Evar.Set.mem k unassigned)) in

  if debug () then
    Feedback.msg_debug Pp.(str"engine out:\n" ++ str (show_engine state));

  state, unassigned, changed, List.(concat (rev extra_gls))
  

let get_declared_goals all_goals syntactic_constraints state assignments =
   match API.Data.StrMap.find "NewGoals" assignments with
   | exception Not_found -> all_goals , []
   | r ->
       let l, depth = skip_lams ~depth:0 0 (r) in
       if no_list_given l then all_goals, []
       else
         let l = U.lp_list_to_list ~depth (E.kool l) in
         let declared = List.map (fun x ->
           match get_goal_ref ~depth syntactic_constraints state x with
           | Some g -> g
           | None -> err Pp.(str"Not a goal " ++ str(pp2string (P.term depth) x))) l in
         let declared_set =
           List.fold_right Evar.Set.add declared Evar.Set.empty in
         declared,
         List.filter (fun x -> not(Evar.Set.mem x declared_set)) all_goals
   (*i
   let sigma = (cs_get_engine state).sigma in
   (* Purge *)
   let state = cs_set_engine state (empty_from_env_sigma env sigma) in
   declared_goals, shelved_goals
*)

let tclSOLUTION2EVD { API.Data.constraints; assignments; state } =
  let state, undefined_evars, _, _gls = elpi_solution_to_coq_solution constraints state in
  let declared_goals, shelved_goals =
    get_declared_goals (Evar.Set.elements undefined_evars) (E.constraints constraints) state assignments in
  let open Proofview.Unsafe in
  let open Tacticals.New in
  tclTHENLIST [
    tclEVARS (S.get engine state).sigma;
    tclSETGOALS @@ List.map Proofview.with_empty_state declared_goals;
    Proofview.shelve_goals shelved_goals
  ]

let set_current_sigma ~depth state sigma =
  let state = set_sigma state sigma in
  let state, assignments, decls, to_remove =
    UVMap.fold (fun k elpi_evk solution (state, assignments, decls, to_remove as acc) ->
      let info = Evd.find sigma k in
      let ctx = Evd.evar_filtered_context info in
      let ctx_len = List.length ctx in
      let proof_names = List.map (fun x -> Name.Name (Context.Named.Declaration.get_id x)) ctx, ctx_len in 
      match Evd.evar_body info with
      | Evd.Evar_empty -> acc
      | Evd.Evar_defined c ->
          let state, t, dec =
            constr2lp proof_names ~calldepth:depth ~depth state c in
          let ass = E.mkAppSL "=" [E.mkUnifVar elpi_evk ~args:(CList.init ctx_len E.mkBound) state; t] in
          state, ass :: assignments, dec :: decls, k :: to_remove
      ) (S.get UVMap.uvmap state) (state,[],[],[]) in
  let state = S.update UVMap.uvmap state (List.fold_right UVMap.remove_host to_remove) in
  state, List.concat decls @ assignments

let get_goal_ref ~depth cst s t = get_goal_ref ~depth (E.constraints cst) s t

(* {{{ elpi -> Entries.mutual_inductive_entry **************************** *)

(* documentation of the Coq API
 
  Coq < Inductive foo (A : Type) (a : A) : A -> Prop := K : foo A a a.

  {Entries.mind_entry_record = None; mind_entry_finite = Decl_kinds.Finite;
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

  {Entries.mind_entry_record = None; mind_entry_finite = Decl_kinds.Finite;
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
*
*)

let parameterc = E.Constants.from_stringc "parameter"
let constructorc = E.Constants.from_stringc "constructor"
let inductivec = E.Constants.from_stringc "inductive"
let coinductivec = E.Constants.from_stringc "coinductive"
let recordc = E.Constants.from_stringc "record"
let fieldc = E.Constants.from_stringc "field"
let end_recordc = E.Constants.from_stringc "end-record"

type record_field_spec = { name : string; is_coercion : bool }

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

let lp2inductive_entry ~depth _hyps constraints state t =
  let hyps = [] in

  let lp2constr ~tolerate_undef_evar ~depth state t =
    lp2constr ~tolerate_undef_evar constraints ([],0) ~depth state t in

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

  let aux_construtors depth params nupno arity itname finiteness sol ks =

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
              let state, ty, gls = lp2constr ~tolerate_undef_evar:false ~depth state ty in
              (state, gls :: extra), (name, ty)
            | _ -> err Pp.(str"@gref expected: "  ++
                 str (pp2string P.(term depth) name))
            end
        | _ -> err Pp.(str"constructor expected: "  ++
                 str (pp2string P.(term depth) t)))
      (sol,[]) ks in
    let knames, ktypes = List.split names_ktypes in 

    let env, sigma = get_global_env_sigma state in

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

    let sol = minimize_universes sol in
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
    
    let oe = {
      mind_entry_typename = itname;
      mind_entry_arity = arity;
      mind_entry_template = false;
      mind_entry_consnames = knames;
      mind_entry_lc = ktypes } in
    sol, {
      mind_entry_record = None;
      mind_entry_finite = finiteness;
      mind_entry_params = params;
      mind_entry_inds = [oe];
      mind_entry_universes =
        Monomorphic_entry (Evd.universe_context_set sigma);
      mind_entry_variance = None;
      mind_entry_private = None; }, List.(concat (rev gls_rev))
  in

  let rec aux_fields depth ind fields =
    match E.look ~depth fields with
    | E.App(c,coercion,[n; ty; fields]) when c == fieldc ->
      begin match E.look ~depth n, E.look ~depth fields with
      | E.CData name, E.Lam fields when CD.is_string name ->
        (* HACK for tt, we should not use = but rather [unspec bool] that is
           not in this file ... *)
        let _, tt, _ = Elpi.Builtin.bool.API.Conversion.embed ~depth hyps constraints state true in
        let fs, tf = aux_fields (depth+1) ind fields in
        let name = CD.to_string name in
        { name; is_coercion = coercion = tt } :: fs,
          in_elpi_prod (in_coq_name ~depth n) ty tf
      | _ -> err Pp.(str"field/end-record expected: "++
                   str (pp2string P.(term depth) fields))
      end
    | E.Const c when c == end_recordc -> [], ind
    | _ ->  err Pp.(str"field/end-record expected: "++ 
                 str (pp2string P.(term depth) fields))
  in

  let rec aux_decl depth params state extra t =
    match E.look ~depth t with
    | E.App(c,name,[ty;decl]) when is_coq_name ~depth name && c == parameterc ->
        let name = in_coq_annot ~depth name in
        let state, ty, gls = lp2constr ~tolerate_undef_evar:false ~depth state ty in
        let open Context.Rel.Declaration in
        aux_lam depth (LocalAssum(name,ty) :: params) state (gls :: extra) decl
    | E.App(c,name,[nupno;arity;ks])
      when (c == inductivec || c == coinductivec) ->
      begin match E.look ~depth name, E.look ~depth nupno  with
      | E.CData name,E.CData nupno when CD.is_string name && CD.is_int nupno ->
        let name = Id.of_string (CD.to_string name) in
        let nupno = CD.to_int nupno in
        let fin =
          if c == inductivec then Declarations.Finite
          else Declarations.CoFinite in
        let state, arity, gl1 = lp2constr ~tolerate_undef_evar:false ~depth state arity in
        begin match E.look ~depth ks with
        | E.Lam t -> 
            let ks = U.lp_list_to_list ~depth:(depth+1) t in
            let sol, idecl, gl2 = 
              aux_construtors (depth+1) params nupno arity name fin
                state ks in
            state, (idecl, None), List.(concat (rev (gl2 :: gl1 :: extra)))
        | _ -> err Pp.(str"lambda expected: "  ++
                 str (pp2string P.(term depth) ks))
        end
      | _ -> err Pp.(str"@id and int expected, got: "++ 
                 str (pp2string P.(term depth) name) ++ str " " ++
                 str (pp2string P.(term depth) nupno))
      end
    | E.App(c,name,[arity;kn;fields]) when c == recordc ->
      begin match E.look ~depth name, E.look ~depth kn with
      | E.CData name, E.CData kname when CD.is_string name && CD.is_string kname ->
        let state, arity, gl1 = lp2constr ~tolerate_undef_evar:false ~depth state arity in
        let name = Id.of_string (CD.to_string name) in
        let fields = U.move ~from:depth ~to_:(depth+1) fields in
        (* We simulate the missing binders for the inductive *)
        let ind = E.mkConst depth in
        let depth = depth + 1 in
        let fields_names_coercions, kty = aux_fields depth ind fields in
        let k = [E.mkApp constructorc kn [kty]] in
        let sol, idecl, gl2 =
          aux_construtors depth params 0 arity name Declarations.Finite
            state k in
        state, (idecl, Some fields_names_coercions), List.(concat (rev (gl2 :: gl1 :: extra)))
      | _ -> err Pp.(str"@id expected, got: "++ 
                 str (pp2string P.(term depth) name))
      end
    | _ -> err Pp.(str"(co)inductive/record expected: "++ 
                 str (pp2string P.(term depth) t))
  and aux_lam depth params sol extra t =
    match E.look ~depth t with
    | E.Lam t -> aux_decl (depth+1) params sol extra t
    | _ -> err Pp.(str"lambda expected: "  ++
                 str (pp2string P.(term depth) t))
                    
  in
    aux_decl depth [] state [] t

(* ********************************* }}} ********************************** *)
(* ****************************** API ********************************** *)

let get_current_env_sigma ~depth hyps constraints state =
(* TODO: cahe longer env in coq_engine for later reuse, use == on hyps+depth? *)
  let state, _, changed, gl1 = elpi_solution_to_coq_solution constraints state in
(* TODO  let state = in_coq_solution solution in *)
  let state, named_ctx, proof_context, _to_restrict, gl2 =
    of_elpi_ctx constraints depth (E.of_hyps hyps) state in

  let { env; sigma } = S.get engine state in
(*
  Feedback.msg_debug Pp.(str "ctx: " ++
    Printer.pr_named_context env sigma (Obj.magic named_ctx));
*)

  let env = EC.push_named_context named_ctx env in
(*
  let state = CS.set engine lp2c_state.state { state with env } in
  let env, sigma = get_global_env_sigma state in
*)
  state, env, sigma, proof_context, gl1 @ gl2
;;

let constr2lp ~depth hyps constraints state t =
  let state, _, coq_proof_ctx_names, _, gl1 =
    of_elpi_ctx constraints depth (E.of_hyps hyps) state in
  let state, t, gl2 = constr2lp coq_proof_ctx_names ~calldepth:depth ~depth state t in
  state, t, gl1 @ gl2

let lp2constr ~tolerate_undef_evar ~depth hyps constraints state t =
  let state, _, _, coq_proof_ctx_names, gl1 = get_current_env_sigma ~depth hyps constraints state in
  let state, t, gl2 = lp2constr ~tolerate_undef_evar constraints coq_proof_ctx_names ~depth state t in
  state, t, gl1 @ gl2

(* {{{  Declarations.module_body -> elpi ********************************** *)

let rec in_elpi_module_item ~depth path state (name, item) = match item with
  | Declarations.SFBconst _ ->
      [Globnames.ConstRef (Constant.make2 path name)]
  | Declarations.SFBmind { Declarations.mind_packets = [| _ |] } ->
      [Globnames.IndRef (MutInd.make2 path name, 0)]
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
