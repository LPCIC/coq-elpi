(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module E = API.RawData
module State = API.State
module P = API.RawPp
module Conv = API.Conversion
module CConv = API.ContextualConversion
module B = struct
  include API.BuiltInData
  include Elpi.Builtin
  let ioarg = API.BuiltInPredicate.ioarg
  let ioarg_any = API.BuiltInPredicate.ioarg_any
  let ioargC = API.BuiltInPredicate.ioargC
  let ioargC_flex = API.BuiltInPredicate.ioargC_flex
  let ioarg_flex = API.BuiltInPredicate.ioarg_flex
  let ioarg_poly s = { ioarg_any with API.Conversion.ty = API.Conversion.TyName s }
end
module Pred = API.BuiltInPredicate
module U = API.Utils

module CNotation = Notation

open Names

open Coq_elpi_utils
open Coq_elpi_HOAS

let string_of_ppcmds options pp =
  let b = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer b in
  Format.pp_set_margin fmt options.ppwidth;
  Format.fprintf fmt "@[%a@]" Pp.pp_with pp;
  Format.pp_print_flush fmt ();
  Buffer.contents b

let with_pp_options o f =
  let raw_print = !Flags.raw_print in
  let print_universes = !Constrextern.print_universes in
  let print_no_symbol = !Constrextern.print_no_symbol in
  (* 8.14 let print_primitive_token = !Constrextern.print_primitive_token in*)
  let print_implicits = !Constrextern.print_implicits in
  let print_coercions = !Constrextern.print_coercions in
  let print_parentheses = !Constrextern.print_parentheses in
  let print_projections = !Constrextern.print_projections in
  let print_evar_arguments = !Detyping.print_evar_arguments in
  let f =
    match o with
    | All ->
        Flags.raw_print := true;
        f
    | Most ->
        Flags.raw_print := false;
        Constrextern.print_universes := false;
        Constrextern.print_no_symbol := true;
        (* 8.14 Constrextern.print_primitive_token := true; *)
        Constrextern.print_implicits := true;
        Constrextern.print_coercions := true;
        Constrextern.print_parentheses := true;
        Constrextern.print_projections := false;
        Detyping.print_evar_arguments := false;
        Constrextern.with_meta_as_hole f
    | Normal ->
        (* If no preference is given, we print using Coq's current value *)
        f
  in
  try
    let rc = f () in
    Flags.raw_print := raw_print;
    Constrextern.print_universes := print_universes;
    Constrextern.print_no_symbol := print_no_symbol;
    (* 8.14 Constrextern.print_primitive_token := print_primitive_token; *)
    Constrextern.print_implicits := print_implicits;
    Constrextern.print_coercions := print_coercions;
    Constrextern.print_parentheses := print_parentheses;
    Constrextern.print_projections := print_projections;
    Detyping.print_evar_arguments := print_evar_arguments;
    rc
  with reraise ->
    Flags.raw_print := raw_print;
    Constrextern.print_universes := print_universes;
    Constrextern.print_no_symbol := print_no_symbol;
    (* 8.14 Constrextern.print_primitive_token := print_primitive_token; *)
    Constrextern.print_implicits := print_implicits;
    Constrextern.print_coercions := print_coercions;
    Constrextern.print_parentheses := print_parentheses;
    Constrextern.print_projections := print_projections;
    Detyping.print_evar_arguments := print_evar_arguments;
    raise reraise

let pr_econstr_env options env sigma t =
  with_pp_options options.pp (fun () ->
    let expr = Constrextern.extern_constr env sigma t in
    let expr =
      let rec aux () ({ CAst.v } as orig) = match v with
      | Constrexpr.CEvar _ -> CAst.make @@ Constrexpr.CHole(None,Namegen.IntroAnonymous)
      | _ -> Constrexpr_ops.map_constr_expr_with_binders (fun _ () -> ()) aux () orig in
      if options.hoas_holes = Some Heuristic then aux () expr else expr in
    Ppconstr.pr_constr_expr_n env sigma options.pplevel expr)

let tactic_mode = State.declare ~name:"coq-elpi:tactic-mode"
  ~pp:(fun fmt x -> Format.fprintf fmt "%b" x)
  ~init:(fun () -> false)
  ~start:(fun x -> x)
let invocation_site_loc = State.declare ~name:"coq-elpi:invocation-site-loc"
  ~pp:(fun fmt x -> Format.fprintf fmt "%a" API.Ast.Loc.pp x)
  ~init:(fun () -> API.Ast.Loc.initial "(should-not-happen)")
  ~start:(fun x -> x)

let abstract__grab_global_env_keep_sigma api thunk = (); (fun state ->
  let state, result, gls = thunk state in
  Coq_elpi_HOAS.grab_global_env state, result, gls)

let grab_global_env__drop_sigma_univs_if_option_is_set options api thunk = (); (fun state ->
  if State.get tactic_mode state then
    Coq_elpi_utils.err Pp.(strbrk ("API " ^ api ^ " cannot be used in tactics"));
  let state, result, gls = thunk state in
  match options with
  | { keepunivs = Some false } -> Coq_elpi_HOAS.grab_global_env_drop_univs_and_sigma state, result, gls
  | _ -> Coq_elpi_HOAS.grab_global_env state, result, gls)

let grab_global_env api thunk = (); (fun state ->
  if State.get tactic_mode state then
    Coq_elpi_utils.err Pp.(strbrk ("API " ^ api ^ " cannot be used in tactics"));
  let state, result, gls = thunk state in
  Coq_elpi_HOAS.grab_global_env state, result, gls)

(* This is for stuff that is not monotonic in the env, eg section closing *)
let grab_global_env_drop_sigma api thunk = (); (fun state ->
  if State.get tactic_mode state then
    Coq_elpi_utils.err Pp.(strbrk ("API " ^ api ^ " cannot be used in tactics"));
  let state, result, gls = thunk state in
  Coq_elpi_HOAS.grab_global_env_drop_sigma state, result, gls)

let err_if_contains_alg_univ ~depth t =
  let global_univs = UGraph.domain (Environ.universes (Global.env ())) in
  let is_global u = 
    match Univ.Universe.level u with
    | None -> true
    | Some l -> Univ.Level.Set.mem l global_univs in
  let rec aux ~depth acc t =
    match E.look ~depth t with
    | E.CData c when isuniv c ->
        let u = univout c in
        if is_global u then acc
        else
          begin match Univ.Universe.level u with
          | None ->
            err Pp.(strbrk "The hypothetical clause contains terms of type univ which are not global, you should abstract them out or replace them by global ones: " ++
              Univ.Universe.pr UnivNames.pr_with_global_universes u)
          | _ -> Univ.Universe.Set.add u acc
          end
    | x -> Coq_elpi_utils.fold_elpi_term aux acc ~depth x
  in
  let univs = aux ~depth Univ.Universe.Set.empty t in
  univs
;;

let bool = B.bool
let int = B.int
let list = B.list
let pair = B.pair
let option = B.option

let mk_algebraic_super x = Sorts.super x

(* I don't want the user to even know that algebraic universes exist *)

let univ_super state u v =
  let state, u = match u with
  | Sorts.Set | Sorts.Prop | Sorts.SProp -> state, u
  | Sorts.Type ul | Sorts.QSort (_, ul) ->
    if Univ.Universe.is_level ul then state, u
    else
      let state, (_,w) = new_univ_level_variable state in
      let w = Sorts.sort_of_univ w in
      add_universe_constraint state (constraint_leq u w), w in
    add_universe_constraint state (constraint_leq (mk_algebraic_super u) v)

let univ_product state s1 s2 =
  let s = Typeops.sort_of_product (get_global_env state) s1 s2 in
  let state, (_,v) = new_univ_level_variable state in
  let v = Sorts.sort_of_univ v in
  let state = add_universe_constraint state (constraint_leq s v) in
  state, v

let constr2lp ~depth hyps constraints state t =
  constr2lp ~depth hyps constraints state t

let constr2lp_closed ~depth hyps constraints state t =
  constr2lp_closed ~depth hyps constraints state t

let constr2lp_closed_ground ~depth hyps constraints state t =
  constr2lp_closed_ground ~depth hyps constraints state t

let clauses_for_later =
  State.declare ~name:"coq-elpi:clauses_for_later"
    ~init:(fun () -> [])
    ~start:(fun x -> x)
    ~pp:(fun fmt l ->
       List.iter (fun (dbname, code,vars,scope) ->
         Format.fprintf fmt "db:%s code:%a scope:%a\n"
              (String.concat "." dbname)
            Elpi.API.Pp.Ast.program code Coq_elpi_utils.pp_scope scope) l)
;;

let term = {
  CConv.ty = Conv.TyName "term";
  pp_doc = (fun fmt () -> Format.fprintf fmt "A Coq term containing evars");
  pp = (fun fmt t -> Format.fprintf fmt "@[%a@]" Pp.pp_with ( (Printer.pr_econstr_env (Global.env()) Evd.empty t)));
  readback = lp2constr;
  embed = constr2lp;
}
let failsafe_term = {
  CConv.ty = Conv.TyName "term";
  pp_doc = (fun fmt () -> Format.fprintf fmt "A Coq term containing evars");
  pp = (fun fmt t -> Format.fprintf fmt "@[%a@]" Pp.pp_with ( (Printer.pr_econstr_env (Global.env()) Evd.empty t)));
  readback = (fun ~depth coq_ctx csts s t -> lp2constr ~depth { coq_ctx with options = { coq_ctx.options with failsafe = true }} csts s t);
  embed = constr2lp;
}

let proof_context : (full coq_context, API.Data.constraints) CConv.ctx_readback =
  fun ~depth hyps constraints state ->
    let state, proof_context, _, gls = get_current_env_sigma ~depth hyps constraints state in
    state, proof_context, constraints, gls

let closed_term = {
  CConv.ty = Conv.TyName "term";
  pp_doc = (fun fmt () -> Format.fprintf fmt "A closed Coq term");
  pp = (fun fmt t -> Format.fprintf fmt "@[%a@]" Pp.pp_with ( (Printer.pr_econstr_env (Global.env()) Evd.empty t)));
  readback = lp2constr_closed;
  embed = constr2lp_closed
}
let global : (empty coq_context, API.Data.constraints) CConv.ctx_readback =
  fun ~depth hyps constraints state ->
    let state, proof_context, _, gls = get_global_env_current_sigma ~depth hyps constraints state in
    state, proof_context, constraints, gls

let closed_ground_term = {
  CConv.ty = Conv.TyName "term";
  pp_doc = (fun fmt () -> Format.fprintf fmt "A ground, closed, Coq term");
  pp = (fun fmt t -> Format.fprintf fmt "@[%a@]" Pp.pp_with ( (Printer.pr_econstr_env (Global.env()) Evd.empty t)));
  readback = lp2constr_closed_ground;
  embed = constr2lp_closed_ground
}

let term_skeleton =  {
  CConv.ty = Conv.TyName "term";
  pp_doc = (fun fmt () -> Format.fprintf fmt "A Coq term containing holes");
  pp = (fun fmt t ->
      let env = Global.env() in
      let sigma = Evd.from_env env in
      Format.fprintf fmt "@[%a@]" Pp.pp_with ( (Printer.pr_glob_constr_env env sigma t)));
  readback = lp2skeleton;
  embed = (fun ~depth _ _ _ _ -> assert false);
}

let prop = { B.any with Conv.ty = Conv.TyName "prop" }
let sealed_goal = {
  Conv.ty = Conv.TyName "sealed-goal";
  pp_doc = (fun fmt () -> ());
  pp = (fun fmt _ -> Format.fprintf fmt "TODO");
  embed = sealed_goal2lp;
  readback = (fun ~depth _ _ -> assert false);
}

let goal : ( (Coq_elpi_HOAS.full Coq_elpi_HOAS.coq_context * Evar.t * Coq_elpi_arg_HOAS.coq_arg list) , API.Data.hyps, API.Data.constraints) CConv.t = {
  CConv.ty = Conv.TyName "goal";
  pp_doc = (fun fmt () -> ());
  pp = (fun fmt _ -> Format.fprintf fmt "TODO");
  embed = (fun ~depth _ _ _ _ -> assert false);
  readback = (fun ~depth hyps csts state g ->
    let state, ctx, k, raw_args, gls1 = Coq_elpi_HOAS.lp2goal ~depth hyps csts state g in
    let state, args, gls2 = U.map_acc (Coq_elpi_arg_HOAS.in_coq_arg ~depth ctx csts) state raw_args in
    state, (ctx,k,args), gls1 @ gls2);
}

let tactic_arg : (Coq_elpi_arg_HOAS.coq_arg, Coq_elpi_HOAS.full Coq_elpi_HOAS.coq_context, API.Data.constraints) CConv.t = {
  CConv.ty = Conv.TyName "argument";
  pp_doc = (fun fmt () -> ());
  pp = (fun fmt _ -> Format.fprintf fmt "TODO");
  embed = (fun ~depth _ _ _ _ -> assert false);
  readback = Coq_elpi_arg_HOAS.in_coq_arg;
}

let id = { B.string with
  API.Conversion.ty = Conv.TyName "id";
  pp_doc = (fun fmt () ->
    Format.fprintf fmt "%% [id] is a name that matters, we piggy back on Elpi's strings.@\n";
    Format.fprintf fmt "%% Note: [name] is a name that does not matter.@\n";
    Format.fprintf fmt "typeabbrev id string.@\n@\n")
}


let flag name = { (B.unspec bool) with Conv.ty = Conv.TyName name }

(* Unfortunately the data type is not symmeteric *)
let indt_decl_in = {
  CConv.ty = Conv.TyName "indt-decl";
  pp_doc = (fun fmt () -> Format.fprintf fmt "Declaration of an inductive type");
  pp = (fun fmt _ -> Format.fprintf fmt "mutual_inductive_entry");
  readback = (fun ~depth ctx csts state t -> lp2inductive_entry ~depth ctx csts state t);
  embed = (fun ~depth ctx csts state t -> assert false);
}
let indt_decl_out = {
  CConv.ty = Conv.TyName "indt-decl";
  pp_doc = (fun fmt () -> Format.fprintf fmt "Declaration of an inductive type");
  pp = (fun fmt _ -> Format.fprintf fmt "mutual_inductive_entry");
  readback = (fun ~depth ctx csts state t -> assert false);
  embed = (fun ~depth ctx csts state t -> inductive_decl2lp ~depth ctx csts state t);
}

let is_ground sigma t = Evar.Set.is_empty (Evd.evars_of_term sigma t)
let is_ground_one_inductive_entry sigma { Entries.mind_entry_arity; mind_entry_lc } =
  is_ground sigma (EConstr.of_constr mind_entry_arity) &&
  List.for_all (is_ground sigma) @@ List.map EConstr.of_constr mind_entry_lc
let is_ground_rel_ctx_entry sigma rc =
  is_ground sigma @@ EConstr.of_constr @@ Context.Rel.Declaration.get_type rc &&
  Option.cata (fun x -> is_ground sigma @@ EConstr.of_constr x) true @@ Context.Rel.Declaration.get_value rc
let is_mutual_inductive_entry_ground { Entries.mind_entry_params; mind_entry_inds } sigma =
  List.for_all (is_ground_rel_ctx_entry sigma) mind_entry_params &&
  List.for_all (is_ground_one_inductive_entry sigma) mind_entry_inds

let handle_uinst_option_for_inductive ~depth options i state =
  match options.uinstance with
  | NoInstance ->
      let term, ctx = UnivGen.fresh_global_instance (get_global_env state) (GlobRef.IndRef i) in
      let state = update_sigma state (fun sigma -> Evd.merge_context_set UState.univ_flexible_alg sigma ctx) in
      snd @@ Constr.destInd term, state, []
  | ConcreteInstance i -> i, state, []
  | VarInstance (v_head, v_args, v_depth) ->
      let v' = U.move ~from:v_depth ~to_:depth (E.mkUnifVar v_head ~args:v_args state) in
      let term, ctx =
        UnivGen.fresh_global_instance (get_global_env state) (GlobRef.IndRef i) in
      let uinst = snd @@ Constr.destInd term in
      let state, lp_uinst, extra_goals = uinstance.Conv.embed ~depth state uinst in
      let state = update_sigma state (fun sigma -> Evd.merge_context_set UState.univ_flexible_alg sigma ctx) in
      uinst, state, API.Conversion.Unify (v', lp_uinst) :: extra_goals

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

(* FIXME PARTIAL API
 *
 * Record foo A1..Am := K { f1; .. fn }.   -- m params, n fields
 * Canonical c (x1 : b1)..(xk : bk) := K p1..pm t1..tn.
 *
 *   fi v1..vm ? rest1  ==  (ci w1..wr) rest2
 *
 *   ?i : bi
 *   vi =?= pi[xi/?i]
 *   wi =?= ui[xi/?i]
 *   ?  == c ?1 .. ?k
 *   rest1 == rest2
 *   ?j =<= (ci w1..wr)    -- default proj, ti = xj
 *   ci == gr
 *
 *   unif (const fi) [V1,..VM, C | R1] (const ci) [W1,..WR| R2] M U :-
 *     of (app[c, ?1,..?k]) _ CR, -- saturate
 *     hd-beta CR [] (indc _) [P1,..PM,T1,..TN],
 *     unify-list-U Vi Pi,
 *     Ti = app[const ci|U1,..,UN],
 *     unify-list-U Wi Ui,
 *     unify-eq C CR,
 *     unify-list-eq R1 R2.
 *
 *)



let cs_pattern =
  let open Conv in let open API.AlgebraicData in let open Structures.ValuePattern in declare {
  ty = TyName "cs-pattern";
  doc = "Pattern for canonical values";
  pp = (fun fmt -> function
    | Const_cs x -> Format.fprintf fmt "Const_cs %s" "<todo>"
    | Proj_cs x -> Format.fprintf fmt "Proj_cs %s" "<todo>"
    | Prod_cs -> Format.fprintf fmt "Prod_cs"
    | Sort_cs _ ->  Format.fprintf fmt "Sort_cs"
    | Default_cs -> Format.fprintf fmt "Default_cs");
  constructors = [
    K("cs-gref","",A(gref,N),
      B (function
          | GlobRef.ConstructRef _ | GlobRef.IndRef _ | GlobRef.VarRef _ as x -> Const_cs x
          | GlobRef.ConstRef cst as x ->
          match Structures.PrimitiveProjections.find_opt cst with
          | None -> Const_cs x
          | Some p -> Proj_cs p),
      M (fun ~ok ~ko -> function Const_cs x -> ok x | Proj_cs p -> ok (GlobRef.ConstRef (Projection.Repr.constant p)) | _ -> ko ()));
    K("cs-prod","",N,
      B Prod_cs,
      M (fun ~ok ~ko -> function Prod_cs -> ok | _ -> ko ()));
    K("cs-default","",N,
      B Default_cs,
      M (fun ~ok ~ko -> function Default_cs -> ok | _ -> ko ()));
    K("cs-sort","",A(sort,N),
      B (fun s -> Sort_cs (Sorts.family s)),
      MS (fun ~ok ~ko p state -> match p with
        | Sort_cs Sorts.InSet -> ok Sorts.set state
        | Sort_cs Sorts.InProp -> ok Sorts.prop state
        | Sort_cs Sorts.InType ->
              let state, (_,u) = new_univ_level_variable state in
              let u = Sorts.sort_of_univ u in
              ok u state
        | _ -> ko state))
  ]
} |> CConv.(!<)

let cs_instance = let open Conv in let open API.AlgebraicData in let open Structures.CSTable in declare {
  ty = TyName "cs-instance";
  doc = "Canonical Structure instances: (cs-instance Proj ValPat Inst)";
  pp = (fun fmt { solution } -> Format.fprintf fmt "@[%a@]" Pp.pp_with ((Printer.pr_global solution)));
  constructors = [
    K("cs-instance","",A(gref,A(cs_pattern,A(gref,N))),
      B (fun p v i -> assert false),
      M (fun ~ok ~ko { solution; value; projection } -> ok projection value solution))
  ]
} |> CConv.(!<)


type tc_priority = Computed of int | UserGiven of int

let tc_priority = let open Conv in let open API.AlgebraicData in declare {
  ty = TyName "tc-priority";
  doc = "Type class instance priority";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("tc-priority-given","User given priority",A(int,N),
      B (fun i -> UserGiven i),
      M (fun ~ok ~ko -> function UserGiven i -> ok i | _ -> ko ()));
    K("tc-priority-computed","Coq computed priority", A(int,N),
      B (fun i -> Computed i),
      M (fun ~ok ~ko -> function Computed i -> ok i | _ -> ko ()));
]} |> CConv.(!<)

type type_class_instance = {
  implementation : GlobRef.t;
  priority : tc_priority;
}

let tc_instance = let open Conv in let open API.AlgebraicData in declare {
  ty = TyName "tc-instance";
  doc = "Type class instance with priority";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("tc-instance","",A(gref,A(tc_priority,N)),
      B (fun implementation priority -> { implementation; priority }),
      M (fun ~ok ~ko { implementation; priority } -> ok implementation priority));
]} |> CConv.(!<)

let get_instance_prio gr env sigma (info : 'a Typeclasses.hint_info_gen) : tc_priority =
  match info.hint_priority with
  | Some p -> UserGiven p
  | None -> 
    let rec nb_hyp sigma c = match EConstr.kind sigma c with
    | Prod(_,_,c2) -> if EConstr.Vars.noccurn sigma 1 c2 then 1+(nb_hyp sigma c2) else nb_hyp sigma c2
    | _ -> 0 in
    let merge_context_set_opt sigma ctx = 
      match ctx with
      | None -> sigma
      | Some ctx -> Evd.merge_context_set Evd.univ_flexible sigma ctx
    in 
    let fresh_global_or_constr env sigma = 
        let (c, ctx) = UnivGen.fresh_global_instance env gr in
        let ctx = if Environ.is_polymorphic env gr then Some ctx else None in
        (EConstr.of_constr c, ctx) in
    let c, ctx = fresh_global_or_constr env sigma in
    let cty = Retyping.get_type_of env sigma c in
    let cty = Reductionops.nf_betaiota env sigma cty in
    let sigma' = merge_context_set_opt sigma ctx in
    let ce = Clenv.mk_clenv_from env sigma' (c,cty) in
    let miss = Clenv.clenv_missing ce in
    let nmiss = List.length miss in
    let hyps = nb_hyp sigma' cty in
    Computed (hyps + nmiss)

let get_instances (env: Environ.env) (emap: Evd.evar_map) tc : type_class_instance list = 
  let hint_db = Hints.searchtable_map "typeclass_instances" in 
  let secvars : Names.Id.Pred.t = Names.Id.Pred.full in 
  let full_hints = Hints.Hint_db.map_all ~secvars:secvars tc hint_db in 
  let hint_asts = List.map Hints.FullHint.repr full_hints in 
  let hints = List.filter_map (function
    | Hints.Res_pf a -> Some a 
    | ERes_pf a -> Some a
    | Extern (a, b) -> None 
    | Give_exact a -> Some a
    | Res_pf_THEN_trivial_fail e -> Some e
    | Unfold_nth e -> None) hint_asts in 
  let sigma, _ = 
    let env = Global.env () in Evd.(from_env env, env) in 
  let constrs = List.map (fun a -> Hints.hint_as_term a |> snd) hints in 
  (* Printer.pr_global tc |> Pp.string_of_ppcmds |> Printf.printf "%s\n"; *)
  let instances_grefs = List.filter_map (fun e ->
    match EConstr.kind sigma e with 
    | Constr.Ind (a, _) -> Some (Names.GlobRef.IndRef a)
    | Constr.Const (a, _) -> Some (Names.GlobRef.ConstRef a)
    | Constr.Construct (a, _) -> Some (Names.GlobRef.ConstructRef a)
    | _ -> None) constrs in 
  let inst_of_tc =
    Typeclasses.instances_exn env emap tc |>
    List.fold_left (fun m i -> GlobRef.Map.add i.Typeclasses.is_impl i m) GlobRef.Map.empty in
  let instances_grefs2istance x = 
    let open Typeclasses in 
    let inst = GlobRef.Map.find x inst_of_tc in
    let priority = get_instance_prio x env sigma inst.is_info in 
    { implementation = x; priority } in 
  List.map instances_grefs2istance instances_grefs

type scope = ExecutionSite | CurrentModule | Library

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
  doc = "Specify if the clause has to be grafted before or after a named clause";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("before","",A(id,N),
        B (fun x -> (`Before,x)),
        M (fun ~ok ~ko -> function (`Before,x) -> ok x | _ -> ko ()));
    K("after","",A(id,N),
        B (fun x -> (`After,x)),
        M (fun ~ok ~ko -> function (`After,x) -> ok x | _ -> ko ()));
  ]
} |> CConv.(!<)

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

let set_accumulate_to_db, get_accumulate_to_db =
  let f = ref (fun _ -> assert false) in
  (fun x -> f := x),
  (fun () -> !f)

let argument_mode = let open Conv in let open API.AlgebraicData in declare {
  ty = TyName "argument_mode";
  doc = "Specify if a predicate argument is in input or output mode";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("in","",N,
        B `Input,
        M (fun ~ok ~ko -> function `Input -> ok | _ -> ko ()));
    K("out","",N,
        B `Output,
        M (fun ~ok ~ko -> function `Output -> ok | _ -> ko ()));
  ]
} |> CConv.(!<)
  

let set_accumulate_text_to_db, get_accumulate_text_to_db =
  let f = ref (fun _ _ -> assert false) in
  (fun x -> f := x),
  (fun () -> !f)


let class_ = let open Conv in let open API.AlgebraicData in let open Coercionops in declare {
  ty = TyName "class";
  doc = "Node of the coercion graph";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
   K("funclass","",N,
     B CL_FUN,
     M (fun ~ok ~ko -> function Coercionops.CL_FUN -> ok | _ -> ko ()));
   K("sortclass","",N,
     B CL_SORT,
     M (fun ~ok ~ko -> function CL_SORT -> ok | _ -> ko ()));
   K("grefclass","",A(gref,N),
     B ComCoercion.class_of_global,
     M (fun ~ok ~ko -> function
     | CL_SECVAR v -> ok (GlobRef.VarRef v)
     | CL_CONST c -> ok (GlobRef.ConstRef c)
     | CL_IND i -> ok (GlobRef.IndRef i)
     | CL_PROJ p -> ok (GlobRef.ConstRef (Projection.Repr.constant p))
     | _ -> ko ()))
]
} |> CConv.(!<)

let src_class_of_class = function
  | (Coercionops.CL_FUN | Coercionops.CL_SORT) -> CErrors.anomaly Pp.(str "src_class_of_class on a non source coercion class")
  | Coercionops.CL_SECVAR v -> GlobRef.VarRef v
  | Coercionops.CL_CONST c -> GlobRef.ConstRef c
  | Coercionops.CL_IND i -> GlobRef.IndRef i
  | Coercionops.CL_PROJ p -> GlobRef.ConstRef (Projection.Repr.constant p)

let coercion = let open Conv in let open API.AlgebraicData in declare {
  ty = TyName "coercion";
  doc = "Edge of the coercion graph";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors =  [
    K("coercion","ref, nparams, src, tgt", A(gref,A(B.unspec int,A(B.unspec gref,A(B.unspec class_,N)))),
      B (fun t np src tgt -> t,np,src,tgt),
      M (fun ~ok ~ko:_ -> function (t,np,src,tgt) -> ok t np src tgt))
  ]
} |> CConv.(!<)

let implicit_kind : Glob_term.binding_kind Conv.t = let open Conv in let open API.AlgebraicData in let open Glob_term in declare {
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
} |> CConv.(!<)

let implicit_kind_of_status = function
  | None -> Glob_term.Explicit
  | Some (_,_,(maximal,_)) ->
      if maximal then Glob_term.MaxImplicit else Glob_term.NonMaxImplicit


let simplification_strategy = let open API.AlgebraicData in let open Reductionops.ReductionBehaviour in declare {
  ty = Conv.TyName "simplification_strategy";
  doc = "Strategy for simplification tactics";
  pp = (fun fmt (x : t) -> Format.fprintf fmt "TODO");
  constructors = [
    K ("never", "Arguments foo : simpl never",N,
      B NeverUnfold,
      M (fun ~ok ~ko -> function NeverUnfold -> ok | _ -> ko ()));
    K("when","Arguments foo .. / .. ! ..",A(B.list B.int, A(B.option B.int, N)),
      B (fun recargs nargs -> UnfoldWhen { recargs; nargs }),
      M (fun ~ok ~ko -> function UnfoldWhen { recargs; nargs } -> ok recargs nargs | _ -> ko ()));
    K("when-nomatch","Arguments foo .. / .. ! .. : simpl nomatch",A(B.list B.int, A(B.option B.int, N)),
      B (fun recargs nargs -> UnfoldWhenNoMatch { recargs; nargs }),
      M (fun ~ok ~ko -> function UnfoldWhenNoMatch { recargs; nargs } -> ok recargs nargs | _ -> ko ()));
  ]
} |> CConv.(!<)

let conversion_strategy = let open API.AlgebraicData in let open Conv_oracle in declare {
  ty = Conv.TyName "conversion_strategy";
  doc = "Strategy for conversion test\nexpand < ... < level -1 < level 0 < level 1 < ... < opaque";
  pp = (fun fmt (x : level) -> Pp.pp_with fmt (pr_level x));
  constructors = [
    K ("opaque", "",N,
      B Opaque,
      M (fun ~ok ~ko -> function Opaque -> ok | _ -> ko ()));
    K("expand","",N,
      B Expand,
      M (fun ~ok ~ko -> function Expand -> ok | _ -> ko ()));
    K("level","default is 0, aka transparent",A(B.int,N),
      B (fun x -> Level x),
      M (fun ~ok ~ko -> function Level x -> ok x | _ -> ko ()));
  ]
} |> CConv.(!<)

let reduction_kind = let open API.AlgebraicData in let open CClosure.RedFlags in declare {
  ty = Conv.TyName "coq.redflag";
  doc = "Flags for lazy, cbv, ... reductions";
  pp = (fun fmt (x : red_kind) -> Format.fprintf fmt "TODO");
  constructors = [
    K ("coq.redflags.beta", "",N,
      B fBETA,
      M (fun ~ok ~ko x -> if x = fBETA then ok else ko ()));
    K ("coq.redflags.delta", "if set then coq.redflags.const disables unfolding",N,
      B fDELTA,
      M (fun ~ok ~ko x -> if x = fDELTA then ok else ko ()));
    K ("coq.redflags.match", "",N,
      B fMATCH,
      M (fun ~ok ~ko x -> if x = fMATCH then ok else ko ()));
    K ("coq.redflags.fix", "",N,
      B fFIX,
      M (fun ~ok ~ko x -> if x = fFIX then ok else ko ()));
    K ("coq.redflags.cofix", "",N,
      B fCOFIX,
      M (fun ~ok ~ko x -> if x = fCOFIX then ok else ko ()));
    K ("coq.redflags.zeta", "",N,
      B fZETA,
      M (fun ~ok ~ko x -> if x = fZETA then ok else ko ()));
    K("coq.redflags.const","enable/disable unfolding",A(constant,N),
      B (function Constant x -> fCONST x | Variable x -> fVAR x),
      M (fun ~ok ~ko x -> nYI "readback for coq.redflags.const"));
  ]
} |> CConv.(!<)


let module_item = let open API.AlgebraicData in declare {
  ty = Conv.TyName "module-item";
  doc = "Contents of a module";
  pp = (fun fmt a -> Format.fprintf fmt "TODO");
  constructors = [
    K("submodule","",A(modpath,C(CConv.(!>>) B.list,N)),
      B (fun s l -> Module(s,l) ),
      M (fun ~ok ~ko -> function Module(s,l) -> ok s l | _ -> ko ()));
    K("module-type","",A(modtypath,N),
      B (fun s -> ModuleType s),
      M (fun ~ok ~ko -> function ModuleType s -> ok s | _ -> ko ()));
    K("gref","",A(gref,N),
      B (fun s -> Gref s),
      M (fun ~ok ~ko -> function Gref x -> ok x | _ -> ko ()));
    K("module-functor","",A(modpath,A(B.list modtypath,N)),
      B (fun s a -> Functor(s,a)),
      M (fun ~ok ~ko -> function Functor(s,a) -> ok s a | _ -> ko ()));
    K("module-type-functor","",A(modtypath,A(B.list modtypath,N)),
      B (fun s a -> FunctorType(s,a)),
      M (fun ~ok ~ko -> function FunctorType(s,a) -> ok s a | _ -> ko ()));
  ]
} |> CConv.(!<)
  
let attribute a = let open API.AlgebraicData in declare {
  ty = Conv.TyName "attribute";
  doc = "Generic attribute";
  pp = (fun fmt a -> Format.fprintf fmt "TODO");
  constructors = [
    K("attribute","",A(B.string,A(a,N)),
      B (fun s a -> s,a),
      M (fun ~ok ~ko -> function (s,a) -> ok s a));
  ]
} |> CConv.(!<)

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

let warning = CWarnings.create ~name:"lib" ~category:elpi_cat Pp.str

let keep x = (x = Pred.Keep)

let if_keep x f =
  match x with
  | Pred.Discard -> None
  | Pred.Keep -> Some (f ())

let _if_keep_acc x state f =
  match x with
  | Pred.Discard -> state, None
  | Pred.Keep ->
       let state, x = f state in
       state, Some x

let gr2id state gr =
  let open GlobRef in
  match gr with
  | VarRef v ->
      (Id.to_string v)
  | ConstRef c ->
      (Id.to_string (Label.to_id (Constant.label c)))
  | IndRef (i,j) ->
      let open Declarations in
      let env = get_global_env state in
      let { mind_packets } = Environ.lookup_mind i env in
      (Id.to_string (mind_packets.(j).mind_typename))
  | ConstructRef ((i,k),j) ->
      let open Declarations in
      let env = get_global_env state in
      let { mind_packets } = Environ.lookup_mind i env in
      (Id.to_string (mind_packets.(k).mind_consnames.(j-1)))
        
let ppbox = let open Conv in let open Pp in let open API.AlgebraicData in declare {
  ty = TyName "coq.pp.box";
  doc = {|Coq box types for pretty printing:
- Vertical block: each break leads to a new line
- Horizontal block: no line breaking
- Horizontal-vertical block: same as Vertical block, except if this block
  is small enough to fit on a single line in which case it is the same
  as a Horizontal block
- Horizontal or Vertical block: breaks lead to new line only when
  necessary to print the content of the block (the contents flow
  inside the box)|};
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("coq.pp.v","",A(B.int,N),
        B (fun i -> Pp_vbox i),
        M (fun ~ok ~ko -> function Pp_vbox i -> ok i | _ -> ko ()));
    K("coq.pp.h","",N,
        B Pp_hbox,
        M (fun ~ok ~ko -> function Pp_hbox -> ok | _ -> ko ()));
    K("coq.pp.hv","",A(B.int,N),
        B (fun i -> Pp_hvbox i),
        M (fun ~ok ~ko -> function Pp_hvbox i -> ok i | _ -> ko ()));
    K("coq.pp.hov","",A(B.int,N),
        B (fun i -> Pp_hovbox i),
        M (fun ~ok ~ko -> function Pp_hovbox i -> ok i | _ -> ko ()));
 ]
} |> CConv.(!<)

let ppboxes = let open Conv in let open Pp in let open API.AlgebraicData in declare {
  ty = TyName "coq.pp";
  doc = {|Coq box model for pretty printing. Items:
- empty
- spc: a spacem, also a breaking hint
- str: a non breakable string
- brk L I: a breaking hint of a given length L contributing I spaces to
  indentation when taken
- glue: puts things together
- box B: a box with automatic line breaking according to B
- comment: embedded \\n are turned into nl (see below)
- tag: ignored
- nl: break the line (should not be used)|};
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("coq.pp.empty","",N,
        B Ppcmd_empty,
        M (fun ~ok ~ko -> function Ppcmd_empty -> ok | _ -> ko ()));
    K("coq.pp.spc","",N,
        B (Ppcmd_print_break(1,0)),
        M (fun ~ok ~ko -> function Ppcmd_print_break(1,0) -> ok | _ -> ko ()));
    K("coq.pp.str","",A(B.string,N),
        B (fun s -> Ppcmd_string s),
        M (fun ~ok ~ko -> function Ppcmd_string s -> ok s | _ -> ko ()));
    K("coq.pp.brk","",A(B.int,A(B.int,N)),
        B (fun i j -> Ppcmd_print_break(i,j)),
        M (fun ~ok ~ko -> function Ppcmd_print_break(i,j) -> ok i j | _ -> ko ()));
    K("coq.pp.glue","",C((fun pp -> CConv.(!>>) B.list pp),N),
        B (fun l -> Ppcmd_glue (List.map Pp.unrepr l)),
        M (fun ~ok ~ko -> function Ppcmd_glue l -> ok (List.map Pp.repr l) | _ -> ko ()));
    K("coq.pp.box","",A(ppbox,C((fun pp -> CConv.(!>>) B.list pp),N)),
        B (fun b l -> Ppcmd_box(b,Pp.unrepr @@ Ppcmd_glue (List.map Pp.unrepr l))),
        M (fun ~ok ~ko -> function
          | Ppcmd_box(b,x) ->
            begin match Pp.repr x with
            | Ppcmd_glue l -> ok b (List.map Pp.repr l)
            | x -> ok b [x]
            end
          | _ -> ko ()));
    K("coq.pp.comment","",A(B.list B.string,N),
        B (fun l -> Ppcmd_comment l),
        M (fun ~ok ~ko -> function Ppcmd_comment l -> ok l | _ -> ko ()));
    K("coq.pp.tag","",A(B.string,S N),
        B (fun b x -> Ppcmd_tag(b,Pp.unrepr x)),
        M (fun ~ok ~ko -> function Ppcmd_tag(b,x) -> ok b (Pp.repr x) | _ -> ko ()));
    K("coq.pp.nl","",N,
        B Ppcmd_force_newline,
        M (fun ~ok ~ko -> function Ppcmd_force_newline -> ok | _ -> ko ()));
  ]
} |> CConv.(!<)

let warn_deprecated_add_axiom =
  CWarnings.create
    ~name:"elpi.add-const-for-axiom-or-sectionvar"
    ~category:elpi_depr_cat
    Pp.(fun () ->
         strbrk ("elpi: Using coq.env.add-const for declaring axioms or " ^
           "section variables is deprecated. Use coq.env.add-axiom or " ^
           "coq.env.add-section-variable instead"))

let add_axiom_or_variable api id ty local options state =
  let state, poly, cumul, udecl, _ = poly_cumul_udecl_variance_of_options state options in
  let used = universes_of_term state ty in
  let sigma = restricted_sigma_of used state in
  if cumul then
    err Pp.(str api ++ str": unsupported attribute @udecl-cumul! or @univpoly-cumul!");
  if poly && local then
    err Pp.(str api ++ str": section variables cannot be universe polymorphic");
  let uentry = UState.check_univ_decl (Evd.evar_universe_context sigma) udecl ~poly in
  let kind = Decls.Logical in
  let impargs = [] in
  let loc = to_coq_loc @@ State.get invocation_site_loc state in
  let variable = CAst.(make ~loc @@ Id.of_string id) in
  if not (is_ground sigma ty) then
    err Pp.(str"coq.env.add-const: the type must be ground. Did you forge to call coq.typecheck-indt-decl?");
  let gr, _ =
    if local then begin
      ComAssumption.declare_variable Vernacexpr.NoCoercion ~kind (EConstr.to_constr sigma ty) uentry impargs Glob_term.Explicit variable;
      Dumpglob.dump_definition variable true "var";
      GlobRef.VarRef(Id.of_string id), Univ.Instance.empty
    end else begin
      Dumpglob.dump_definition variable false "ax";
      ComAssumption.declare_axiom Vernacexpr.NoCoercion ~local:Locality.ImportDefaultBehavior ~poly:false ~kind (EConstr.to_constr sigma ty)
        uentry impargs options.inline
        variable
    end
  in
  gr
  ;;

type tac_abbrev = {
  abbrev_name : qualified_name;
  tac_name : qualified_name;
  tac_fixed_args : Coq_elpi_arg_HOAS.Tac.glob list;
}

type ('a,'d) gbpmp = Gbpmp : ('d, _, 'b, Loc.t -> 'd) Pcoq.Rule.t * ('a -> 'b) -> ('a,'d) gbpmp

let rec gbpmp f = function
  | [x] -> Gbpmp (Pcoq.Rule.next Pcoq.Rule.stop (Pcoq.Symbol.token (Tok.PIDENT(Some x))), (fun a _ -> f a))
  | x :: xs ->
      let Gbpmp (r, f) = gbpmp f xs in
      Gbpmp (Pcoq.Rule.next r (Pcoq.Symbol.token (Tok.PFIELD (Some x))), (fun a _ -> f a))
  | [] -> assert false

let cache_abbrev_for_tac { abbrev_name; tac_name = tacname; tac_fixed_args = more_args } =
  let action args loc =
  let open Ltac_plugin in
  let tac =
    let open Tacexpr in
    let elpi_tac = {
      mltac_plugin = "coq-elpi.elpi";
      mltac_tactic = "elpi_tac"; } in
    let elpi_tac_entry = {
      mltac_name = elpi_tac;
      mltac_index = 0; } in
    let more_args = more_args |> List.map (function
      | Coq_elpi_arg_HOAS.Tac.Int _ as t -> t
      | Coq_elpi_arg_HOAS.Tac.String _ as t -> t
      | Coq_elpi_arg_HOAS.Tac.Term (t,_) ->
        let expr = Constrextern.extern_glob_constr Constrextern.empty_extern_env t in
        let rec aux () ({ CAst.v } as orig) = match v with
        | Constrexpr.CEvar _ -> CAst.make @@ Constrexpr.CHole(None,Namegen.IntroAnonymous)
        | _ -> Constrexpr_ops.map_constr_expr_with_binders (fun _ () -> ()) aux () orig in
        Coq_elpi_arg_HOAS.Tac.Term (aux () expr)
      | _ -> assert false)  in
    let tacname = loc, tacname in
    let tacname = Genarg.in_gen (Genarg.rawwit Coq_elpi_arg_syntax.wit_qualified_name) tacname in
    let args = args |> List.map (fun (arg,_) -> Coq_elpi_arg_HOAS.Tac.Term(arg)) in
    let args = Genarg.in_gen (Genarg.rawwit (Genarg.wit_list Coq_elpi_arg_syntax.wit_elpi_tactic_arg)) (more_args @ args) in
    (TacML (elpi_tac_entry, [TacGeneric(None, tacname); TacGeneric(None, args)])) in
  CAst.make @@ Constrexpr.CGenarg (Genarg.in_gen (Genarg.rawwit Tacarg.wit_tactic) (CAst.make tac)) in
  let Gbpmp (rule, action) = gbpmp action (List.rev abbrev_name) in
  Pcoq.grammar_extend Pcoq.Constr.term (Pcoq.Fresh
    (Gramlib.Gramext.Before "10",
     [ (None, None, [ Pcoq.Production.make
      (Pcoq.Rule.next rule (Pcoq.Symbol.list0 (Pcoq.Symbol.nterm Pcoq.Constr.arg)))
      action
    ])]))

let subst_abbrev_for_tac (subst, { abbrev_name; tac_name; tac_fixed_args }) = {
  abbrev_name;
  tac_name;
  tac_fixed_args = List.map (Coq_elpi_arg_HOAS.Tac.subst subst) tac_fixed_args
}

let inAbbreviationForTactic : tac_abbrev -> Libobject.obj =
  Libobject.declare_object @@ Libobject.global_object_nodischarge "ELPI-EXPORTED-TAC-ABBREV"
      ~cache:cache_abbrev_for_tac ~subst:(Some subst_abbrev_for_tac)

let cache_tac_abbrev qualid = cache_abbrev_for_tac {
  abbrev_name = qualid;
  tac_name = qualid;
  tac_fixed_args = [];
}


let cache_goption_declaration (depr,key,value) =
  let open Goptions in
  let depr = if depr then Some (Deprecation.make ~note:"elpi" ()) else None in
  match value with
  | BoolValue x ->
      let _ : bool Goptions.getter = Goptions.declare_bool_option_and_ref ~key ~value:x ?depr () in
      ()
  | IntValue x ->
    let _ : int option Goptions.getter = Goptions.declare_intopt_option_and_ref ~stage:Interp ~key ?depr ~value:x () in
    ()
  | StringOptValue x ->
    let _ : string option Goptions.getter = Goptions.declare_stringopt_option_and_ref ~stage:Interp ~key ?depr ~value:x () in
    ()
  | StringValue _ -> assert false

let subst_goption_declaration (_,x) = x

let inGoption : _ -> Libobject.obj =
  Libobject.declare_object @@ Libobject.superglobal_object_nodischarge "ELPI-EXPORTED-GOPTION"
      ~cache:cache_goption_declaration ~subst:(Some subst_goption_declaration)

let mode = let open API.AlgebraicData in let open Hints in declare {
  ty = Conv.TyName "hint-mode";
  doc = "Hint Mode";
  pp = (fun fmt (x : hint_mode) -> Pp.pp_with fmt (pp_hint_mode x));
  constructors = [
    K ("mode-ground", "No Evar",N,
      B ModeInput,
      M (fun ~ok ~ko -> function ModeInput -> ok | _ -> ko ()));
    K("mode-input","No Head Evar",N,
      B ModeNoHeadEvar,
      M (fun ~ok ~ko -> function ModeNoHeadEvar -> ok | _ -> ko ()));
    K("mode-output","Anything",N,
      B ModeOutput,
      M (fun ~ok ~ko -> function ModeOutput -> ok | _ -> ko ()));
  ]
} |> CConv.(!<)

module WMsg = Set.Make(struct
  type t = Loc.t option * string
  let compare = Stdlib.compare
end)

let coq_warning_cache : WMsg.t API.Data.StrMap.t ref =
  Summary.ref ~name:"elpi-warning-cache" API.Data.StrMap.empty
let coq_warning_cache category name loc txt =
  let key = category ^ " " ^ name in
  let msg = loc, txt in
  try
    let s = API.Data.StrMap.find key !coq_warning_cache in
    if WMsg.mem msg s then false
    else
      let s = WMsg.add msg s in
      coq_warning_cache := API.Data.StrMap.add key s !coq_warning_cache;
      true
  with
    Not_found ->
      coq_warning_cache := API.Data.StrMap.add key (WMsg.singleton msg) !coq_warning_cache;
      true

let pp_option_value fmt = function
  | Goptions.IntValue None | Goptions.StringOptValue None -> Format.fprintf fmt "unset"
  | Goptions.IntValue (Some x) -> Format.fprintf fmt "%d" x
  | Goptions.StringOptValue (Some x) -> Format.fprintf fmt "%s" x
  | Goptions.StringValue x -> Format.fprintf fmt "%s" x
  | Goptions.BoolValue x -> Format.fprintf fmt "%b" x

let goption = let open API.AlgebraicData in let open Goptions in declare {
  ty = Conv.TyName "coq.option";
  doc = "Coq option value";
  pp = pp_option_value;
  constructors = [
    K("coq.option.int", "none means unset",A(B.option B.int,N),
      B (fun x -> IntValue x),
      M (fun ~ok ~ko -> function IntValue x -> ok x | _ -> ko ()));
    K("coq.option.string","none means unset",A(B.option B.string,N),
      B (fun x -> StringOptValue x),
      M (fun ~ok ~ko -> function StringOptValue x -> ok x | StringValue x -> ok (Some x) | _ -> ko ()));
    K("coq.option.bool","",A(B.bool,N),
      B (fun x -> BoolValue x),
      M (fun ~ok ~ko -> function BoolValue x -> ok x | _ -> ko ()));
  ]
} |> CConv.(!<)

let module_ast_of_modpath x =
  let open Libnames in let open Nametab in
  qualid_of_dirpath (dirpath_of_module x)

let module_ast_of_modtypath x =
  let open Constrexpr in let open Libnames in let open Nametab in
  CAst.make @@ CMident (qualid_of_path (path_of_modtype x)),
  Declaremods.DefaultInline

let find_hint_db s =
  try
    Hints.searchtable_map s
  with Not_found ->
    err Pp.(str "Hint DB not found: " ++ str s)

let hint_db : (string * Hints.Hint_db.t) Conv.t = {
  Conv.ty = B.string.Conv.ty;
  Conv.pp_doc = B.string.Conv.pp_doc;
  Conv.pp = (fun fmt (s,_) -> B.string.Conv.pp fmt s);
  Conv.readback = (fun ~depth x state ->
    let state, x, _ = B.string.Conv.readback ~depth x state in
    state,(x, find_hint_db x),[]);
  embed = (fun ~depth _ _ -> assert false);
}

let hint_locality (options : options) =
  match options.local with
  | Some true -> Hints.Local
  | Some false -> Hints.SuperGlobal
  | None -> Hints.Export

let hint_locality_doc = {|
- @local! (default is export)
- @global! (discouraged, may become deprecated)|}

let unify_instances_gref gr ui1 ui2 diag env state cmp_constr_universes =
  let open Pred in
  let open Notation in
  let nargs, poly_ctx_size =
    let open Names.GlobRef in
    match gr with
    | VarRef _ -> 0, 0
    | ConstRef c ->
      let cb = Environ.lookup_constant c env in
      let univs = Declareops.constant_polymorphic_context cb in
      0, Univ.AbstractContext.size univs
    | IndRef ind ->
      let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
      let univs = Declareops.inductive_polymorphic_context mib in
      Conversion.inductive_cumulativity_arguments (mib,snd ind), Univ.AbstractContext.size univs
    | ConstructRef (ind,kno) ->
      let (mib,_ as specif) =
        Inductive.lookup_mind_specif env ind in
      let univs = Declareops.inductive_polymorphic_context mib in
      Conversion.constructor_cumulativity_arguments (mib,snd ind,kno), Univ.AbstractContext.size univs
  in
  let l1 = Univ.Instance.length ui1 in
  let l2 = Univ.Instance.length ui2 in
  if l1 <> l2 then
    state, !: (B.mkERROR "different universe instance lengths"), []
  else if l1 <> poly_ctx_size then
    let msg =
      Printf.sprintf "global reference %s expects instances of length %d, got %d"
        (Pp.string_of_ppcmds (Printer.pr_global gr)) poly_ctx_size l1 in
    state, !: (B.mkERROR msg), []
  else
    let t1 = EConstr.mkRef (gr, EConstr.EInstance.make ui1) in
    let t2 = EConstr.mkRef (gr, EConstr.EInstance.make ui2) in
    let sigma = get_sigma state in
    match cmp_constr_universes env sigma ?nargs:(Some nargs) t1 t2 with
    | None -> assert false
    | Some problem_set ->
      try
        let state = add_constraints state problem_set in
        state, !: B.mkOK, []
      with
      | Evd.UniversesDiffer | UState.UniversesDiffer ->
        state, !: (B.mkERROR "UniversesDiffer"), []
      | UGraph.UniverseInconsistency p ->
        match diag with
        | Data B.OK -> raise No_clause
        | _ ->
          let msg =
            UGraph.explain_universe_inconsistency
              UnivNames.pr_with_global_universes p in
          state, !: (B.mkERROR (Pp.string_of_ppcmds msg)), []

let gref_set, gref_set_decl = B.ocaml_set_conv ~name:"coq.gref.set" gref (module GRSet)


let grefs_of_term sigma t add_to_acc acc =
  let open GlobRef in
  let open Constr in
  let rec aux acc c =
    match EConstr.kind sigma c with
      | Var x -> add_to_acc (VarRef x) acc
      | Const (c,_) -> add_to_acc (ConstRef c) acc
      | Ind (i,_) -> add_to_acc (IndRef i) acc
      | Construct (k,_) -> add_to_acc (ConstructRef k) acc
      | _ -> EConstr.fold sigma aux acc c
  in
    aux acc t

let dep1 ?inside sigma gr =
  let open GlobRef in
  let modpath_of_gref = function
    | VarRef _ -> Safe_typing.current_modpath (Global.safe_env ())
    | IndRef (i,_) -> MutInd.modpath i
    | ConstructRef ((i,_),_) -> MutInd.modpath i
    | ConstRef c -> Constant.modpath c in
  let add_if_inside =
    match inside with
    | None -> GRSet.add
    | Some modpath -> fun x acc ->
        if ModPath.equal (modpath_of_gref x) modpath
        then GRSet.add x acc
        else acc in
  let add acc t = grefs_of_term sigma (EConstr.of_constr t) add_if_inside acc in
  GRSet.remove gr @@
  match gr with
  | VarRef id ->
      let decl = Environ.lookup_named id (Global.env()) in
      let ty = Context.Named.Declaration.get_type decl in
      let bo = Context.Named.Declaration.get_value decl in
      let l =
        match bo with
        | None -> [ty]
        | Some bo -> [ty; bo] in
      List.fold_left add GRSet.empty l
  | ConstRef cst ->
      let cb = Environ.lookup_constant cst (Global.env()) in
      let ty = cb.Declarations.const_type in
      let bo = Global.body_of_constant_body Library.indirect_accessor cb in
      let l =
        match bo with
        | Some (e,_,_) -> [ty; e]
        | None -> [ty] in
      List.fold_left add GRSet.empty l
  | IndRef i | ConstructRef (i,_) ->
      let _, indbody = Global.lookup_inductive i in
      let l = indbody.Declarations.mind_user_lc in
      CArray.fold_left add GRSet.empty l

let universe_level_set, universe_level_set_decl =
  B.ocaml_set_conv ~name:"coq.univ.variable.set" universe_level_variable (module UnivLevelSet)

let coq_print pp msg_f =
  (fun args ~depth _hyps _constraints state ->
     let pp = pp ~depth in
     msg_f Pp.(str (pp2string (P.list ~boxed:true pp " ") args));
     state, ())

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


(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)


let coq_builtins =
  let open API.BuiltIn in
  let open Pred in
  let open Notation in
  let open CConv in
  let pp ~depth = P.term depth in
  [LPCode
{|% Coq terms as the object language of elpi and basic API to access Coq
% license: GNU Lesser General Public License Version 2.1 or later
% -------------------------------------------------------------------------

% This file is automatically generated from
%  - coq-HOAS.elpi
%  - coq_elpi_builtin.ml
% and contains the description of the data type of Coq terms and the
% API to access Coq.

|};
  LPCode Coq_elpi_builtins_HOAS.code;
  MLData Coq_elpi_HOAS.record_field_att;
  MLData Coq_elpi_HOAS.coercion_status;
  LPCode {|
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% builtins %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% This section contains the API to access Coq
% The marker *E* means *experimental*, i.e. use at your own risk, it may change
% substantially or even disappear in future versions.
|};

  LPDoc "-- Misc ---------------------------------------------------------";

  MLCode(Pred("coq.info",
    VariadicIn(unit_ctx, !> B.any, "Prints an info message"),
    coq_print pp Feedback.msg_info
  ),
  DocAbove);

  MLCode(Pred("coq.notice",
    VariadicIn(unit_ctx, !> B.any, "Prints a notice message"),
    coq_print pp Feedback.msg_notice
  ),
  DocAbove);

  MLCode(Pred("coq.say",
    VariadicIn(unit_ctx, !> B.any, "Prints a notice message"),
    coq_print pp Feedback.msg_notice
  ),
  DocAbove);

  MLCode(Pred("coq.warn",
    VariadicIn(unit_ctx, !> B.any, "Prints a generic warning message"),
  (fun args ~depth _hyps _constraints state ->
     let pp = pp ~depth in
     let loc, args =
       if args = [] then None, args
       else
         let x, args = List.hd args, List.tl args in
         match E.look ~depth x with
         | E.CData loc when API.RawOpaqueData.is_loc loc ->
           Some (Coq_elpi_utils.to_coq_loc (API.RawOpaqueData.to_loc loc)), args
         | _ -> None, x :: args
     in
     warning ?loc (pp2string (P.list ~boxed:true pp " ") args);
     state, ()
     )),
  DocAbove);

  MLCode(Pred("coq.warning",
    In(B.string,"Category",
    In(B.string,"Name",
    VariadicIn(unit_ctx, !> B.any, {|
Prints a warning message with a Name and Category which can be used
to silence this warning or turn it into an error. See coqc -w command
line option|}))),
  (fun category_name name args ~depth _hyps _constraints state ->
     let category = match CWarnings.get_category category_name with
       | There c -> c
       | OtherType -> CErrors.anomaly Pp.(str category_name ++ str "is a warning, not a warning category.")
       | NotThere -> CWarnings.create_category ~from:[elpi_cat] ~name:category_name ()
     in
     let w = match CWarnings.get_warning name with
       | There w -> w
       | OtherType -> CErrors.anomaly Pp.(str name ++ str " is a warning category, not a warning.")
       | NotThere -> CWarnings.create_warning ~from:[category] ~name ()
     in
     let warning = CWarnings.create_in w Pp.str in
     let pp = pp ~depth in
     let loc, args =
       if args = [] then None, args
       else
         let x, args = List.hd args, List.tl args in
         match E.look ~depth x with
         | E.CData loc when API.RawOpaqueData.is_loc loc ->
           Some (Coq_elpi_utils.to_coq_loc (API.RawOpaqueData.to_loc loc)), args
         | _ -> None, x :: args
     in
     let txt = pp2string (P.list ~boxed:true pp " ") args in
     if coq_warning_cache category_name name loc txt then warning ?loc txt;
     state, ())),
  DocAbove);

  MLCode(Pred("coq.error",
    VariadicIn(unit_ctx, !> B.any, "Prints and *aborts* the program. It is a fatal error for Elpi and Ltac"),
  (fun args ~depth _hyps _constraints _state ->
     let pp = pp ~depth in
     err Pp.(str (pp2string (P.list ~boxed:true pp " ") args)))),
  DocAbove);

  MLCode(Pred("coq.version",
    Out(B.string, "VersionString",
    Out(int, "Major",
    Out(int, "Minor",
    Out(int, "Patch",
    Easy "Fetches the version of Coq, as a string and as 3 numbers")))),
    (fun _ _ _ _ ~depth:_ ->
      let version = Coq_config.version in
      let major, minor, patch = coq_version_parser version in
      !: version +! major +! minor +! patch)),
  DocAbove);
  LPCode {|
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% API for objects belonging to the logic
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%|};
  LPDoc "-- Environment: names -----------------------------------------------";
  LPDoc {|To make the API more precise we use different data types for the names of global objects.
Note: [ctype \"bla\"] is an opaque data type and by convention it is written [@bla].|};

  MLData constant;
  MLData inductive;
  MLData constructor;
  MLData gref;
  MLData id;
  MLData modpath;
  MLData modtypath;
  ] @

  [
  LPDoc "-- Environment: read ------------------------------------------------";
  LPDoc "Note: The type [term] is defined in coq-HOAS.elpi";

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
      match locate_qualid qualid with
      | Some (`Gref gr) -> add @@ LocGref gr
      | Some (`Abbrev sd) -> add @@ LocAbbreviation sd
      | None -> ()
    end;
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

  MLCode(Pred("coq.locate",
    In(id, "Name",
    Out(gref,  "GlobalReference",
    Easy {|locates a global definition, inductive type or constructor via its name.
It unfolds syntactic notations, e.g. "Notation old_name := new_name."
It undestands qualified names, e.g. "Nat.t".
It understands Coqlib Registered names using the "lib:" prefix,
eg "lib:core.bool.true".
It's a fatal error if Name cannot be located.|})),
  (fun s _ ~depth:_ -> !: (locate_gref s))),
  DocAbove);


  MLCode(Pred("coq.env.typeof",
    In(gref, "GR",
    COut(closed_ground_term, "Ty",
    Full(global, {|reads the type Ty of a global reference.
Supported attributes:
- @uinstance! I (default: fresh instance I)|}))),
  (fun gr _ ~depth { options } _ state ->
    let type_of_global' state term inst_opt =
      let state, (ty, inst) = type_of_global state term inst_opt in
      state, ty, Some inst
    in
    let state, ty, _, gls =
        compute_with_uinstance ~depth options state type_of_global' gr None in
    state, !: ty, gls)),
  DocAbove);

  MLCode(Pred("coq.env.global",
    InOut(B.ioarg (B.poly "gref"), "GR",
    InOut(B.ioarg (B.poly "term"), "T",
    Full(global, {|turns a global reference GR into a term, or viceversa.
T = (global GR) or, if GR points to a universe polymorphic term,
T = (pglobal GR I).
Supported attributes:
- @uinstance! I (default: fresh instance I)|}))),
  (fun gr t ~depth ({ options } as ctx) csts state ->
    let state, gr_in, _ =
      match gr with
      | NoData -> state, None, []
      | Data maybe_gr ->
          match E.look ~depth maybe_gr with
          | E.App(_,x,[]) ->
              begin match E.look ~depth x with
              | E.CData _ ->
                  let state, gr, gls = gref.Conv.readback ~depth state maybe_gr in
                  state, Some gr, gls
              | _ -> state, None, []
              end
          | _ -> state, None, []
    in
    let state, gr_out, ui_in =
      match t with
      | NoData -> state, None, None
      | Data maybe_t ->
          match is_global_or_pglobal ~depth maybe_t with
          | NotGlobal -> raise No_clause
          | Var -> state, None, None
          | (Global maybe_gr) -> state, maybe_gr, None
          | (PGlobal(maybe_gr,maybe_ui)) -> state, maybe_gr, maybe_ui
      in
    match gr_in, gr_out with
    | Some gr, _ ->
        let state, t, _, gls1 =
          compute_with_uinstance ~depth options state mk_global gr ui_in in
        let state, t, gls2 =
          closed_ground_term.CConv.embed ~depth ctx csts state t in
        state, ?: None +! t, gls1 @ gls2
    | None, Some maybe_gr ->
        let state, gr, gls = gref.Conv.readback ~depth state maybe_gr in
        let state, t, _, gls1 =
          compute_with_uinstance ~depth options state mk_global gr ui_in in
        let state, t, gls2 =
          closed_ground_term.CConv.embed ~depth ctx csts state t in
        state, !: maybe_gr +! t, gls @ gls1 @ gls2
    | None, None -> err Pp.(str "coq.env.global: no input, all arguments are variables"))),
  DocAbove);

  MLCode(Pred("coq.env.indt",
    In(inductive, "reference to the inductive type",
    Out(bool, "tt if the type is inductive (ff for co-inductive)",
    Out(int,  "number of parameters",
    Out(int,  "number of parameters that are uniform (<= parameters)",
    COut(closed_ground_term, "type of the inductive type constructor including parameters",
    Out(list constructor, "list of constructor names",
    COut(!>> B.list closed_ground_term, "list of the types of the constructors (type of KNames) including parameters",
    Full(global, {|reads the inductive type declaration for the environment.
% Supported attributes:
% - @uinstance! I (default: fresh instance I)|})))))))),
  (fun i _ _ _ arity knames ktypes ~depth { env ; options } _ state ->
    let open Declarations in
    let mind, indbo as ind = lookup_inductive env i in
    let co  = mind.mind_finite <> Declarations.CoFinite in
    let lno = mind.mind_nparams in
    let luno = mind.mind_nparams_rec in
    let uinst, state, extra_goals = handle_uinst_option_for_inductive ~depth options i state in    
    let arity = if_keep arity (fun () ->
      Inductive.type_of_inductive (ind,uinst)
      |> EConstr.of_constr) in
    let knames = if_keep knames (fun () ->
      CList.(init Declarations.(indbo.mind_nb_constant + indbo.mind_nb_args) (fun k -> i,k+1))) in
    let ktypes = if_keep ktypes (fun () ->
      Inductive.type_of_constructors (i,uinst) ind
      |> CArray.map_to_list EConstr.of_constr) in
    state, !: co +! lno +! luno +? arity +? knames +? ktypes, extra_goals)),

  DocNext);

  MLCode(Pred("coq.env.indt-decl",
    In(inductive, "reference to the inductive type",
    COut(indt_decl_out,"HOAS description of the inductive type",
    Full(global,{|reads the inductive type declaration for the environment.
% Supported attributes:
% - @uinstance! I (default: fresh instance I)|}))),
  (fun i _ ~depth { env; options } _ state  ->
     let mind, indbo = lookup_inductive env i in
     let uinst, state, extra_goals = handle_uinst_option_for_inductive ~depth options i state in    
     let knames = CList.(init Declarations.(indbo.mind_nb_constant + indbo.mind_nb_args) (fun k -> GlobRef.ConstructRef(i,k+1))) in
     let k_impls = List.map (fun x -> Impargs.extract_impargs_data (Impargs.implicits_of_global x)) knames in
     let hd x = match x with [] -> [] | (_,x) :: _ -> List.map implicit_kind_of_status x in
     let k_impls = List.map hd k_impls in
     let i_impls = Impargs.extract_impargs_data @@ Impargs.implicits_of_global (GlobRef.IndRef i) in
     let i_impls = hd i_impls in
     state, !: (fst i, uinst, (mind,indbo), (i_impls,k_impls)), extra_goals)),
  DocNext);

  MLCode(Pred("coq.env.indc->indt",
    In(constructor,"K",
    Out(inductive,"I",
    Out(int,"N",
    Easy {|finds the inductive I to which constructor K belongs and its position N among the other constructors|}))),
    (fun (i,n) _ _ ~depth -> !: i +! n)),
  DocAbove);

  MLCode(Pred("coq.env.indc",
    In(constructor, "GR",
    Out(int, "ParamNo",
    Out(int, "UnifParamNo",
    Out(int, "Kno",
    COut(closed_ground_term,"Ty",
    Full (global, {|reads the type Ty of an inductive constructor GR, as well as
the number of parameters ParamNo and uniform parameters
UnifParamNo and the number of the constructor Kno (0 based).
Supported attributes:
- @uinstance! I (default: fresh instance I)|})))))),
  (fun (i,k as kon) _ _ _ ty ~depth { env; options } _ state ->
    let open Declarations in
    let mind, indbo as ind = Inductive.lookup_mind_specif env i in
    let lno = mind.mind_nparams in
    let luno = mind.mind_nparams_rec in
    let uinst, state, extra_goals =
      match options.uinstance with
      | NoInstance ->
        if keep ty then
          let term, ctx =
            UnivGen.fresh_global_instance (get_global_env state) (GlobRef.ConstructRef kon) in
          snd @@ Constr.destConstruct term,
          update_sigma state
            (fun sigma -> Evd.merge_context_set UState.univ_flexible_alg sigma ctx),
          []
        else
          Univ.Instance.empty, state, []
      | ConcreteInstance i -> i, state, []
      | VarInstance (v_head, v_args, v_depth) ->
        let v' = U.move ~from:v_depth ~to_:depth (E.mkUnifVar v_head ~args:v_args state) in
        let term, ctx =
          UnivGen.fresh_global_instance (get_global_env state) (GlobRef.ConstructRef kon) in
        let uinst = snd @@ Constr.destConstruct term in
        let state, lp_uinst, extra_goals = uinstance.Conv.embed ~depth state uinst in
        uinst,
        update_sigma state
          (fun sigma -> Evd.merge_context_set UState.univ_flexible_alg sigma ctx),
        API.Conversion.Unify (v', lp_uinst) :: extra_goals
    in
    let ty = if_keep ty (fun () ->
      Inductive.type_of_constructor (kon, uinst) ind
      |> EConstr.of_constr) in
    state, !: lno +! luno +! (k-1) +? ty, extra_goals)),
  DocAbove);

  MLCode(Pred("coq.env.informative?",
    In(inductive, "Ind",
    Read(global, {|Checks if Ind is informative, that is, if
it can be eliminated to build a Type. Inductive types in Type are
informative, as well a singleton types in Prop (which are
regarded as not non-informative).|})),
  (fun i ~depth {env} _ state ->
      let _, indbo = Inductive.lookup_mind_specif env i in
      match indbo.Declarations.mind_kelim with
      | (Sorts.InSProp | Sorts.InProp) -> raise No_clause
      | Sorts.InSet when Environ.is_impredicative_set env -> raise No_clause
      | (Sorts.InSet | Sorts.InType | Sorts.InQSort) -> ()
    )),
  DocAbove);

  MLCode(Pred("coq.env.record?",
    In(inductive, "Ind",
    Out(bool,"PrimProjs",
    Read(global, "checks if Ind is a record (PrimProjs = tt if Ind has primitive projections)"))),
  (fun i _ ~depth {env} _ state ->
      let mind, indbo = Inductive.lookup_mind_specif env i in
      match mind.Declarations.mind_record with
      | Declarations.PrimRecord _ -> !: true
      | Declarations.FakeRecord -> !: false
      | _ -> raise No_clause
    )),
  DocAbove);

  MLCode(Pred("coq.env.recursive?",
    In(inductive, "Ind",
    Read(global, "checks if Ind is recursive")),
  (fun i ~depth {env} _ state ->
      let mind, indbo = Inductive.lookup_mind_specif env i in
      match mind.Declarations.mind_packets with
      | [| { Declarations.mind_recargs } |] ->
           if Rtree.is_infinite Declareops.eq_recarg mind_recargs then ()
           else raise No_clause
      | _ -> assert false
    )),
  DocAbove);

  MLCode(Pred("coq.env.opaque?",
    In(constant, "GR",
    Read(global, "checks if GR is an opaque constant")),
  (fun c ~depth {env} _ state ->
    match c with
    | Constant c ->
        let open Declareops in
        let cb = Environ.lookup_constant c env in
        if is_opaque cb || not(constant_has_body cb) then ()
        else raise Pred.No_clause
    | Variable v ->
        match Environ.lookup_named v env with
        | Context.Named.Declaration.LocalDef _ -> raise Pred.No_clause
        | Context.Named.Declaration.LocalAssum _ -> ())),
  DocAbove);

  MLCode(Pred("coq.env.univpoly?",
  In(gref, "GR",
  Out(B.int, "PolyArity",
  Read(global, "checks if GR is universe polymorphic and if so returns the number of universe variables"))),
    (fun gr _ ~depth {env} _ _ ->
      if Environ.is_polymorphic env gr then
        let open Univ.AbstractContext in let open Declareops in let open Environ in
        match gr with
        | GlobRef.ConstRef c -> !: (size (constant_polymorphic_context (lookup_constant c env)))
        | GlobRef.ConstructRef ((i,_),_)
        | GlobRef.IndRef (i,_) -> !: (size (inductive_polymorphic_context (lookup_mind i env)))
        | GlobRef.VarRef _ -> assert false
      else raise No_clause)),
  DocAbove);
  
  MLCode(Pred("coq.env.const",
    In(constant,  "GR",
    COut(!>> option closed_ground_term, "Bo",
    COut(closed_ground_term, "Ty",
    Full (global, {|reads the type Ty and the body Bo of constant GR.
Opaque constants have Bo = none.
Supported attributes:
- @uinstance! I (default: fresh instance I)|})))),
  (fun c bo ty ~depth { env ; options } _ state ->
    let type_of_global' state term inst_opt =
      let state, (ty, inst) = type_of_global state term inst_opt in
      state, ty, Some inst
    in
    match c with
    | Constant c ->
      let state, ty_opt, uinst_opt, gl_opt1 =
        if keep ty then
          let state, ty, uinst_opt, gls =
            compute_with_uinstance ~depth options state type_of_global' (GlobRef.ConstRef c) None in
          state, Some ty, uinst_opt, gls
        else
          let uinst_opt =
            match options.uinstance with
            | ConcreteInstance i -> Some i
            | _ -> None
          in
          state, None, uinst_opt, []
      in
      let state, bo_opt, gl_opt2 =
        if keep bo then
          if Declareops.is_opaque (Environ.lookup_constant c env) then
            state, Some None, []
          else
            let state, bo, _, gls2 =
              compute_with_uinstance ~depth options state body_of_constant c uinst_opt in
            state, Some bo, gls2
        else
          state, None, []
      in
      state, ?: bo_opt +? ty_opt, gl_opt1 @ gl_opt2
    | Variable v ->
      let state, ty, gls =
        if keep ty then
          let state, ty, _, gls =
            compute_with_uinstance ~depth options state type_of_global' (GlobRef.VarRef v) None in
          state, Some ty, gls
        else
          state, None, []
      in
      let bo = if_keep bo (fun () ->
        match Environ.lookup_named v env with
        | Context.Named.Declaration.LocalDef(_,bo,_) -> Some (bo |> EConstr.of_constr)
        | Context.Named.Declaration.LocalAssum _ -> None) in
      state, ?: bo +? ty, gls)),
  DocAbove);

  MLCode(Pred("coq.env.const-body",
    In(constant,  "GR",
    COut(!>> option closed_ground_term, "Bo",
    Full (global, {|reads the body of a constant, even if it is opaque.
If such body is none, then the constant is a true axiom.
Supported attributes:
- @uinstance! I (default: fresh instance I)|}))),
  (fun c _ ~depth { env ; options } _ state ->
    match c with
    | Constant c ->
      let state, bo, gls =
        let state, bo, _, gls =
          compute_with_uinstance ~depth options state body_of_constant c None in
        state, bo, gls
      in
      state, !: bo, gls
    | Variable v ->
         state, !: begin
         match Environ.lookup_named v env with
         | Context.Named.Declaration.LocalDef(_,bo,_) -> Some (bo |> EConstr.of_constr)
         | Context.Named.Declaration.LocalAssum _ -> None
         end, [])),
  DocAbove);

  MLCode(Pred("coq.env.primitive?",
    In(constant,  "GR",
    Read (global,"tests if GR is a primitive constant (like uin63 addition) or a primitive type (like uint63)")),
  (fun c ~depth {env} _ state ->
    match c with
    | Constant c ->
        if Environ.is_primitive env c || Environ.is_primitive_type env c then ()
        else raise No_clause
    | Variable v -> raise No_clause)),
  DocAbove);

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
  DocAbove);

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
  DocAbove);

  MLData module_item;

  MLCode(Pred("coq.env.module",
    In(modpath, "MP",
    Out(list module_item, "Contents",
    Read(global, "lists the contents of a module (recurses on submodules) *E*"))),
  (fun mp _ ~depth {env} _ state ->
    let t = in_elpi_module ~depth state (Environ.lookup_module mp env) in
    !: t)),
  DocAbove);

  MLCode(Pred("coq.env.module-type",
    In(modtypath, "MTP",
    Out(list id,  "Entries",
    Read (global, "lists the items made visible by module type "^
          "(does not recurse on submodules) *E*"))),
  (fun mp _ ~depth {env} _ state ->
    !: (in_elpi_module_type (Environ.lookup_modtype mp env)))),
  DocAbove);

  MLCode(Pred("coq.env.section",
    Out(list constant, "GlobalObjects",
    Read(unit_ctx, "lists the global objects that are marked as to be abstracted at the end of the enclosing sections")),
  (fun _ ~depth _ _ state ->
     let { section } = mk_coq_context ~options:(default_options ()) state in
     !: (section |> List.map (fun x -> Variable x)) )),
  DocAbove);

  MLCode(Pred("coq.env.dependencies",
    In(gref, "GR",
    In(B.unspec modpath, "MP",
    Out(gref_set, "Deps",
    Read(unit_ctx, "Computes the direct dependencies of GR. If MP is given, Deps only contains grefs from that module")))),
  (fun root inside _ ~depth _ _ state ->
    let inside = unspec2opt inside in
     !: (dep1 ?inside (get_sigma state) root))),
  DocAbove);

  MLCode(Pred("coq.env.transitive-dependencies",
    In(gref, "GR",
    In(B.unspec modpath, "MP",
    Out(gref_set, "Deps",
    Read(unit_ctx, "Computes the transitive dependencies of GR. If MP is given, Deps only contains grefs from that module")))),
  (fun root inside _ ~depth _ _ state ->
     let inside = unspec2opt inside in
     let sigma = get_sigma state in
     let rec aux seen = function
       | [] -> seen
       | s :: xs when GRSet.is_empty s -> aux seen xs
       | s :: rest ->
          let x = GRSet.min_elt s in
          let s = GRSet.remove x s in
          if GRSet.mem x seen then aux seen (s :: rest)
          else
            let deps = dep1 ?inside sigma x in
            let seen = GRSet.add x seen in
            aux seen (deps :: s :: rest)
     in
     !: (GRSet.remove root @@ aux GRSet.empty [dep1 ?inside sigma root]))),
  DocAbove);

  MLCode(Pred("coq.env.term-dependencies",
    CIn(failsafe_term,"T",
    Out(gref_set, "S",
    Full(proof_context, {|Computes all the grefs S occurring in the term T|}))),
  (fun t _ ~depth proof_context constraints state ->
     let sigma = get_sigma state in
     let s = grefs_of_term sigma t GRSet.add GRSet.empty in
     state, !: s, [])),
  DocAbove);

  MLCode(Pred("coq.env.current-path",
    Out(list B.string, "Path",
    Read(unit_ctx, "lists the current module path")),
  (fun _ ~depth _ _ state -> !: (mp2path (Safe_typing.current_modpath (Global.safe_env ()))))),
  DocAbove);

  MLCode(Pred("coq.env.current-section-path",
    Out(list B.string, "Path",
    Read(unit_ctx, "lists the current section path")),
  (fun _ ~depth _ _ state ->
       let base = Lib.current_dirpath false in
       let base_w_sections = Lib.current_dirpath true in
       let sections = Libnames.drop_dirpath_prefix base base_w_sections in
       !: (mp2path (Names.ModPath.MPfile sections)))),
  DocAbove);

  LPCode {|% Deprecated, use coq.env.opaque?
  pred coq.env.const-opaque? i:constant.
  coq.env.const-opaque? C :-
    coq.warning "elpi.deprecated" "elpi.const-opaque" "use coq.env.opaque? in place of coq.env.const-opaque?",
    coq.env.opaque? C.
  |};
 
  LPCode {|% Deprecated, use coq.env.primitive?
  pred coq.env.const-primitive? i:constant.
  coq.env.const-primitive? C :-
    coq.warning "elpi.deprecated" "elpi.const-primitive" "use coq.env.primitive? in place of coq.env.const-primitive?",
    coq.env.primitive? C.
  |};
 
  LPDoc "-- Environment: write -----------------------------------------------";

  LPDoc ("Note: (monomorphic) universe constraints are taken from ELPI's constraints "^
         "store. Use coq.univ-* in order to add constraints (or any higher "^
         "level facility as coq.typecheck). Load in the context attributes such as "^
         "@univpoly!, @univpoly-cumul!, @udecl! or @udecl-cumul! in order to declare "^
         "universe polymorphic constants or inductives."
         );

  MLCode(Pred("coq.env.add-const",
    In(id,   "Name",
    CIn(B.unspecC closed_ground_term, "Bo",
    CIn(B.unspecC closed_ground_term, "Ty",
    In(flag "opaque?", "Opaque",
    Out(constant, "C",
    Full (global, {|Declare a new constant: C gets a constant derived from Name
and the current module; Ty can be left unspecified and in that case the
inferred one is taken (as in writing Definition x := t); Bo can be left
unspecified and in that case an axiom is added (or a section variable,
if a section is open and @local! is used). Omitting the body and the type is
an error. Note: using this API for declaring an axiom or a section variable is
deprecated, use coq.env.add-axiom or coq.env.add-section-variable instead.
Supported attributes:
- @local! (default: false)
- @using! (default: section variables actually used)
- @univpoly! (default unset)
- @udecl! (default unset)
- @dropunivs! (default: false, drops all universe constraints from the store after the definition)
|})))))),
  (fun id body types opaque _ ~depth {options} _ -> grab_global_env__drop_sigma_univs_if_option_is_set options "coq.env.add-const" (fun state ->
    let local = options.local = Some true in
    let state = minimize_universes state in
    (* Maybe: UState.nf_universes on body and type *)
     match body with
     | B.Unspec -> (* axiom *)
       begin match types with
       | B.Unspec ->
         err Pp.(str "coq.env.add-const: both Type and Body are unspecified")
       | B.Given ty ->
       warn_deprecated_add_axiom ();
       let gr = add_axiom_or_variable "coq.env.add-const" id ty local options state in
       state, !: (global_constant_of_globref gr), []
     end
    | B.Given body ->
       let sigma = get_sigma state in
       if not (is_ground sigma body) then
         err Pp.(str"coq.env.add-const: the body must be ground. Did you forge to call coq.typecheck-indt-decl?");
       let opaque = opaque = B.Given true in
       let types =
         match types, opaque with
         | B.Unspec, false -> None
         | B.Unspec, true -> (* Coq does not accept opaque definitions with no body *)
            begin try Some (Retyping.get_type_of (get_global_env state) sigma body)
            with
            | Retyping.RetypeError _ -> err Pp.(str"coq.env.add-const: illtyped opaque")
            | e when CErrors.is_anomaly e -> err Pp.(str"coq.env.add-const: illtyped opaque") end
         | B.Given ty, _ ->
            if not (is_ground sigma ty) then
              err Pp.(str"coq.env.add-const: the type must be ground. Did you forge to call coq.typecheck-indt-decl?");
             Some ty in
       let state, poly, cumul, udecl, _ = poly_cumul_udecl_variance_of_options state options in
       if cumul then err Pp.(str"coq.env.add-const: unsupported attribute @udecl-cumul! or @univpoly-cumul!");
       let kind = Decls.(IsDefinition Definition) in
       let scope = if local
        then Locality.Discharge
        else Locality.(Global ImportDefaultBehavior) in
       let using = Option.map  Proof_using.(fun s ->
          let sigma = get_sigma state in
          let types = Option.List.cons types [] in
          let using = using_from_string s in
          definition_using (get_global_env state) sigma ~using ~terms:types)
         options.using in
       let cinfo = Declare.CInfo.make ?using ~name:(Id.of_string id) ~typ:types ~impargs:[] () in
       let info = Declare.Info.make ~scope ~kind ~poly ~udecl () in

       let used =
         Univ.Level.Set.union
           (universes_of_term state body)
           (Option.default (EConstr.mkRel 1) types |> universes_of_term state) in
       let used = Univ.Level.Set.union used (universes_of_udecl state udecl) in
       let sigma = restricted_sigma_of used state in
   
       let gr = Declare.declare_definition ~cinfo ~info ~opaque ~body sigma in
       let () =
        let lid = CAst.make ~loc:(to_coq_loc @@ State.get invocation_site_loc state) (Id.of_string id) in
        match scope with
        | Locality.Discharge -> Dumpglob.dump_definition lid true "var"
        | Locality.Global _ -> Dumpglob.dump_definition lid false "def"
       in
       state, !: (global_constant_of_globref gr), []))),
  DocAbove);

  MLCode(Pred("coq.env.add-axiom",
    In(id,   "Name",
    CIn(closed_ground_term, "Ty",
    Out(constant, "C",
    Full (global, {|Declare a new axiom: C gets a constant derived from Name
and the current module.
Supported attributes:
- @local! (default: false)
- @univpoly! (default unset)
- @using! (default: section variables actually used)
- @inline! (default: no inlining)
- @inline-at! N (default: no inlining)|})))),
  (fun id ty _ ~depth {options} _ -> grab_global_env "coq.env.add-axiom" (fun state ->
     let gr = add_axiom_or_variable "coq.env.add-axiom" id ty false options state in
     state, !: (global_constant_of_globref gr), []))),
  DocAbove);

  MLCode(Pred("coq.env.add-section-variable",
    In(id,   "Name",
    CIn(closed_ground_term, "Ty",
    Out(constant, "C",
    Full (global, {|Declare a new section variable: C gets a constant derived from Name
and the current module|})))),
  (fun id ty _ ~depth {options} _ -> grab_global_env_drop_sigma "coq.env.add-section-variable" (fun state ->
     let gr = add_axiom_or_variable "coq.env.add-section-variable" id ty true options state in
     state, !: (global_constant_of_globref gr), []))),
  DocAbove);

  MLCode(Pred("coq.env.add-indt",
    CIn(indt_decl_in, "Decl",
    Out(inductive, "I",
    Full(global, {|Declares an inductive type.
Supported attributes:
- @dropunivs! (default: false, drops all universe constraints from the store after the definition)
- @primitive! (default: false, makes records primitive)|}))),
  (fun (me, uctx, univ_binders, record_info, ind_impls) _ ~depth {options} _ -> grab_global_env__drop_sigma_univs_if_option_is_set options "coq.env.add-indt" (fun state ->
     let sigma = get_sigma state in
     if not (is_mutual_inductive_entry_ground me sigma) then
       err Pp.(str"coq.env.add-indt: the inductive type declaration must be ground. Did you forget to call coq.typecheck-indt-decl?");
     let primitive_expected = match record_info with Some(p, _) -> p | _ -> false in
     let (uentry, uentry', ubinders) = 
       let open Entries in
       match me.mind_entry_universes with
       | Monomorphic_ind_entry -> (Monomorphic_entry, UState.Monomorphic_entry uctx, univ_binders)
       | Template_ind_entry _ -> nYI "template polymorphic inductives"
       | Polymorphic_ind_entry uctx ->
          (Polymorphic_entry uctx, UState.Polymorphic_entry uctx, univ_binders)
       in
     let () = DeclareUctx.declare_universe_context ~poly:false uctx in
     let mind =
       DeclareInd.declare_mutual_inductive_with_eliminations ~primitive_expected me (uentry', ubinders) ind_impls in
     let ind = mind, 0 in
     let id, cids = match me.Entries.mind_entry_inds with
       | [ { Entries.mind_entry_typename = id; mind_entry_consnames = cids }] -> id, cids
       | _ -> assert false
       in
     let lid_of id = CAst.make ~loc:(to_coq_loc @@ State.get invocation_site_loc state) id in
     begin match record_info with
     | None -> (* regular inductive *)
        Dumpglob.dump_definition (lid_of id) false "ind";
        List.iter (fun x -> Dumpglob.dump_definition (lid_of x) false "constr") cids
     | Some (primitive,field_specs) -> (* record: projection... *)
         let names, flags =
           List.(split (map (fun { name; is_coercion; is_canonical } -> name,
               { Record.Internal.pf_coercion = is_coercion <> Off ;
                 pf_reversible = is_coercion = Reversible ;
                 pf_canonical = is_canonical;
                 pf_instance = false;
                 pf_priority = None;
                 pf_locality = OptDefault })
             field_specs)) in
         let is_implicit = List.map (fun _ -> []) names in
         let open Entries in
         let k_ty = List.(hd (hd me.mind_entry_inds).mind_entry_lc) in
         let fields_as_relctx = Term.prod_decls k_ty in
         let projections =
           Record.Internal.declare_projections ind ~kind:Decls.Definition
             (uentry, ubinders)
             (Names.Id.of_string "record")
             flags is_implicit fields_as_relctx
         in
         let struc = Structures.Structure.make (Global.env()) ind projections in
         Record.Internal.declare_structure_entry struc;
         Dumpglob.dump_definition (lid_of id) false "rec";
         List.iter (function
           | Names.Name id -> Dumpglob.dump_definition (lid_of id) false "proj"
           | Names.Anonymous -> ()) names;
      end;
     state, !: ind, []))),
  DocAbove);

  LPDoc "Interactive module construction";

  MLData module_inline_default;

  MLCode(Pred("coq.env.fresh-global-id",
    In(id,"ID",
    Out(id,"FID",
    Easy {|Generates an id FID which is fresh in
the current module and looks similar to ID, i.e. it is ID concatenated
with a number, starting from 1.
[coq.env.fresh-global-id X X] can be used to check if X is taken|})),
    (fun id _ ~depth ->
      let l = Names.Label.of_id (Names.Id.of_string_soft id) in
      if not (Safe_typing.exists_objlabel l (Global.safe_env ())) then !: id
      else
        let rec fresh n =
          let id = id ^ string_of_int n in
          let l = Names.Label.of_id (Names.Id.of_string_soft id) in
          if not (Safe_typing.exists_objlabel l (Global.safe_env ())) then !: id
          else fresh (n+1)
        in
          fresh 1
      )),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.begin-module-functor",
    In(id, "The name of the functor",
    In(option modtypath, "Its module type",
    In(list (pair id modtypath), "Parameters of the functor",
    Full(unit_ctx, "Starts a functor *E*")))),
  (fun name mp binders_ast ~depth _ _ -> grab_global_env "coq.env.begin-module-functor" (fun state ->
     if Global.sections_are_opened () then
       err Pp.(str"This elpi code cannot be run within a section since it opens a module");
     let ty =
       match mp with
       | None -> Declaremods.Check []
       | Some mp -> Declaremods.(Enforce (module_ast_of_modtypath mp)) in
     let id = Id.of_string name in
     let binders_ast =
       List.map (fun (id, mty) ->
         [CAst.make (Id.of_string id)], (module_ast_of_modtypath mty))
         binders_ast in
     let mp = Declaremods.start_module None id binders_ast ty in
     let loc = to_coq_loc @@ State.get invocation_site_loc state in
     Dumpglob.dump_moddef ~loc mp "mod";
   
     state, (), []))),
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
  (fun _ ~depth _ _ -> grab_global_env_drop_sigma "coq.env.end-module" (fun state ->
     let mp = Declaremods.end_module () in
     state, !: mp, []))),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.begin-module-type-functor",
    In(id, "The name of the functor",
    In(list (pair id modtypath), "The parameters of the functor",
    Full(unit_ctx,"Starts a module type functor *E*"))),
  (fun id binders_ast ~depth _ _ -> grab_global_env "coq.env.begin-module-type-functor" (fun state ->
     if Global.sections_are_opened () then
       err Pp.(str"This elpi code cannot be run within a section since it opens a module");
     let id = Id.of_string id in
     let binders_ast =
       List.map (fun (id, mty) ->
         [CAst.make (Id.of_string id)], (module_ast_of_modtypath mty))
         binders_ast in
     let mp = Declaremods.start_modtype id binders_ast [] in
     let loc = to_coq_loc @@ State.get invocation_site_loc state in
     Dumpglob.dump_moddef ~loc mp "modtype";

      state, (), []))),
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
  (fun _ ~depth _ _ -> grab_global_env_drop_sigma "coq.env.end-module-type" (fun state ->
     let mp = Declaremods.end_modtype () in
     state, !: mp, []))),
  DocAbove);

  MLCode(Pred("coq.env.apply-module-functor",
    In(id, "The name of the new module",
    In(option modtypath, "Its module type",
    In(modpath, "The functor being applied",
    In(list modpath, "Its arguments",
    In(module_inline_default, "Arguments inlining",
    Out(modpath, "The modpath of the new module",
    Full(unit_ctx, "Applies a functor *E*"))))))),
  (fun name mp f arguments inline _ ~depth _ _ -> grab_global_env "coq.env.apply-module-functor" (fun state ->
     if Global.sections_are_opened () then
       err Pp.(str"This elpi code cannot be run within a section since it defines a module");
     let ty =
       match mp with
       | None -> Declaremods.Check []
       | Some mp -> Declaremods.(Enforce (module_ast_of_modtypath mp)) in
     let id = Id.of_string name in
     let f = CAst.make (Constrexpr.CMident (module_ast_of_modpath f)) in
     let mexpr_ast_args = List.map module_ast_of_modpath arguments in
      let mexpr_ast =
         List.fold_left (fun hd arg -> CAst.make (Constrexpr.CMapply(hd,arg))) f mexpr_ast_args in
      let mp = Declaremods.declare_module id [] ty [mexpr_ast,inline] in
      let loc = to_coq_loc @@ State.get invocation_site_loc state in
      Dumpglob.dump_moddef ~loc mp "mod";
      state, !: mp, []))),
  DocNext);
  
  MLCode(Pred("coq.env.apply-module-type-functor",
    In(id, "The name of the new module type",
    In(modtypath, "The functor",
    In(list modpath, "Its arguments",
    In(module_inline_default, "Arguments inlining",
    Out(modtypath, "The modtypath of the new module type",
    Full(unit_ctx, "Applies a type functor *E*")))))),
  (fun name f arguments inline _ ~depth _ _ -> grab_global_env "coq.env.apply-module-type-functor" (fun state ->
     if Global.sections_are_opened () then
       err Pp.(str"This elpi code cannot be run within a section since it defines a module");
     let id = Id.of_string name in
     let f,_ = module_ast_of_modtypath f in
     let mexpr_ast_args = List.map module_ast_of_modpath arguments in
     let mexpr_ast =
        List.fold_left (fun hd arg -> CAst.make (Constrexpr.CMapply(hd,arg))) f mexpr_ast_args in
     let mp = Declaremods.declare_modtype id [] [] [mexpr_ast,inline] in
     let loc = to_coq_loc @@ State.get invocation_site_loc state in
     Dumpglob.dump_moddef ~loc mp "modtype";
     state, !: mp, []))),
  DocNext);

  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.include-module",
    In(modpath, "ModPath",
    In(module_inline_default, "Inline",
    Full(unit_ctx, "is like the vernacular Include, Inline can be omitted *E*"))),
  (fun mp inline ~depth _ _ -> grab_global_env "coq.env.include-module" (fun state ->
     let fpath = match mp with
       | ModPath.MPdot(mp,l) ->
           Libnames.make_path (ModPath.dp mp) (Label.to_id l)
       | _ -> nYI "functors" in
     let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
     let i = CAst.make tname, inline in
     Declaremods.declare_include [i];
     state, (), []))),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.include-module-type",
    In(modtypath, "ModTyPath",
    In(module_inline_default, "Inline",
    Full(unit_ctx, "is like the vernacular Include Type, Inline can be omitted  *E*"))),
  (fun mp inline  ~depth _ _ -> grab_global_env "coq.env.include-module-type" (fun state ->
     let fpath = Nametab.path_of_modtype mp in
     let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
     let i = CAst.make tname, inline in
     Declaremods.declare_include [i];
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.env.import-module",
    In(modpath, "ModPath",
    Full(unit_ctx, "is like the vernacular Import *E*")),
  (fun mp ~depth _ _ -> grab_global_env "coq.env.import-module" (fun state ->
     Declaremods.import_module ~export:Lib.Import Libobject.unfiltered mp;
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.env.export-module",
    In(modpath, "ModPath",
    Full(unit_ctx, "is like the vernacular Export *E*")),
  (fun mp ~depth _ _ -> grab_global_env "coq.env.export-module" (fun state ->
     Declaremods.import_module ~export:Lib.Export Libobject.unfiltered mp;
     state, (), []))),
  DocAbove);

  LPDoc
{|Support for sections is limited, in particular sections and
Coq quotations may interact in surprising ways. For example
  Section Test.
  Variable x : nat.
  Elpi Query lp:{{ coq.say {{ x }} }}.
works since x is a global Coq term while
  Elpi Query lp:{{
    coq.env.begin-section "Test",
    coq.env.add-const "x" _ {{ nat }} _ @local! GRX,
    coq.say {{ x }}
  }}.
may work in a surprising way or may not work at all since
x is resolved before the section is started hence it cannot
denote the same x as before.|};

  MLCode(Pred("coq.env.begin-section",
    In(id, "Name",
    Full(unit_ctx, "starts a section named Name *E*")),
  (fun id ~depth _ _ -> grab_global_env "coq.env.begin-section" (fun state ->
     let id = Id.of_string id in
     let lid = CAst.make ~loc:(to_coq_loc @@ State.get invocation_site_loc state) id in
     Dumpglob.dump_definition lid true "sec";
     Lib.open_section id;
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.env.end-section",
    Full(unit_ctx, "end the current section *E*"),
  (fun ~depth _ _ -> grab_global_env_drop_sigma "coq.env.end-section" (fun state ->
     let loc = to_coq_loc @@ State.get invocation_site_loc state in
     Dumpglob.dump_reference ~loc
       (DirPath.to_string (Lib.current_dirpath true)) "<>" "sec";
     Lib.close_section ();
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.env.projections",
    In(inductive, "StructureName",
    Out(list (option constant), "Projections",
    Easy "given a record StructureName lists all projections")),
  (fun i _ ~depth ->
    !: (Structures.Structure.find_projections i |>
      CList.map (Option.map (fun x -> Constant x))))),
  DocAbove);

  MLCode(Pred("coq.env.primitive-projections",
    In(inductive, "StructureName",
    Out(list (option (pair projection int)), "Projections",
    Easy "given a record StructureName lists all primitive projections")),
  (fun i _ ~depth ->
      !: (Structures.Structure.find_projections i |>
        CList.map (fun o -> Option.bind o (fun x ->
          Option.bind (Structures.PrimitiveProjections.find_opt x) (fun c ->
            let c = Names.Projection.make c false in
            let np = Names.Projection.npars c in
            let na = Names.Projection.arg c in
            Some (c, np + na))))))),
  DocAbove);

  LPDoc "-- Sorts (and their universe level, if applicable) ----------------";
  LPDoc {|Warning: universe polymorphism has to be considered experimental *E* as
a feature, not just as a set of APIs. Unfortunately some of the
current complexity is exposed to the programmer, bare with us.

The big bang is that in Coq one has terms, types and sorts (which are
the types of types). Some sorts (as of today only Type) some with
a universe level, on paper Type_i for some i. At the sort level
Coq features some form of subtyping: a function expecting a function
to Type, e.g. nat -> Type, can receive a function to Prop, since
Prop <= Type. So far, so good. But what are these levels i exactly?

Universe levels are said to be "algebraic", they are made of
variables (see the next section) and the two operators +1 and max.
This is a sort of internal optimization that leaks to the
user/programmer. Indeed these universe levels cannot be (directly) used
in all APIs morally expecting a universe level "i", in particular
the current constraint engine cannot handle constraint with an
algebraic level on the right, e.g. i <= j+1. Since some APIs only
accept universe variables, we provide the coq.univ.variable API
which is able to craft a universe variable which is roughly
equivalent to an algebraic universe, e.g. k such that j+1 = k.

Coq-Elpi systematically purges algebraic universes from terms (and
types and sorts) when one reads them from the environment. This
makes the embedding of terms less precise than what it could be.
The different data types stay, since Coq will eventually become
able to handle algebraic universes consistently, making this purging
phase unnecessary.|};
  MLData univ;
  MLData sort;

  MLCode(Pred("coq.sort.leq",
    InOut(B.ioarg_flex sort, "S1",
    InOut(B.ioarg_flex sort, "S2",
    Full(unit_ctx, "constrains S1 <= S2"))),
  (fun u1 u2 ~depth _ _ state ->
    match u1, u2 with
    | Data u1, Data u2 ->
        if Sorts.equal u1 u2 then state, !: u1 +! u2,[]
        else
          let state, u2 = purge_algebraic_univs_sort state (EConstr.ESorts.make u2) in
          add_universe_constraint state (constraint_leq u1 u2), !: u1 +! u2,[]
    | _ -> err Pp.(str"coq.sort.leq: called with _ as argument"))),
  DocAbove);

  MLCode(Pred("coq.sort.eq",
    InOut(B.ioarg_flex sort, "S1",
    InOut(B.ioarg_flex sort, "S2",
    Full(unit_ctx, "constrains S1 = S2"))),
  (fun u1 u2 ~depth _ _ state ->
    match u1, u2 with
    | Data u1, Data u2 ->
      if Sorts.equal u1 u2 then state, !: u1 +! u2,[]
      else
        let state, u2 = purge_algebraic_univs_sort state (EConstr.ESorts.make u2) in
        add_universe_constraint state (constraint_eq u1 u2), !: u1 +! u2, []
    | _ -> err Pp.(str"coq.sort.eq: called with _ as argument"))),
  DocAbove);

  MLCode(Pred("coq.sort.sup",
    InOut(B.ioarg_flex sort, "S1",
    InOut(B.ioarg_flex sort, "S2",
    Full(unit_ctx,  "constrains S2 = S1 + 1"))),
  (fun u1 u2 ~depth _ _ state ->
    match u1, u2 with
    | Data u1, Data u2 -> univ_super state u1 u2, !: u1 +! u2, []
    | _ -> err Pp.(str"coq.sort.sup: called with _ as argument"))),
  DocAbove);

  MLCode(Pred("coq.sort.pts-triple",
    InOut(B.ioarg_flex sort, "S1",
    InOut(B.ioarg_flex sort, "S2",
    Out(sort, "S3",
    Full(unit_ctx,  "constrains S3 = sort of product with domain in S1 and codomain in S2")))),
  (fun u1 u2 _ ~depth _ _ state ->
    match u1, u2 with
    | Data u1, Data u2 -> let state, u3 = univ_product state u1 u2 in state, !: u1 +! u2 +! u3, []
    | _ -> err Pp.(str"coq.sort.pts-triple: called with _ as argument"))),
    DocAbove);

  MLCode(Pred("coq.univ.print",
    Read(unit_ctx,  "prints the set of universe constraints"),
  (fun ~depth _ _ state ->
    let sigma = get_sigma state in
    let uc = Evd.evar_universe_context sigma in
    let uc = Termops.pr_evar_universe_context uc in
    Feedback.msg_notice Pp.(str "Universe constraints: " ++ uc);
    ())),
  DocAbove);

  MLCode(Pred("coq.univ.new",
    Out(univ, "U",
    Full(unit_ctx, "A fresh universe.")),
  (fun _ ~depth _ _ state ->
     let state, (_,u) = new_univ_level_variable state in
     state, !: u, [])),
  DocAbove);

  MLCode(Pred("coq.univ",
    InOut(B.ioarg id, "Name",
    InOut(B.ioarg univ, "U",
    Read(unit_ctx, "Finds a named unvierse. Can fail."))),
  (fun nl u ~depth _ _ state ->
     match nl, u with
     | Data nl, _ ->
         begin try ?: None +! (Univ.Universe.make @@ Evd.universe_of_name (get_sigma state) (Id.of_string_soft nl))
         with Not_found -> raise No_clause end
     | _, Data u ->
         begin match Univ.Universe.level u with
         | None -> raise Not_found
         | Some u ->
            let l = Id.Map.bindings @@ Evd.universe_binders (get_sigma state) in
            begin try !: (Id.to_string @@ fst @@ List.find (fun (_,u') -> Univ.Level.equal u u') l) +? None
            with Not_found -> raise No_clause end end
     | NoData, NoData -> err Pp.(str "coq.univ: both argument were omitted"))),
  DocAbove);

  MLCode(Pred("coq.univ.global?",
    In(univ, "U",
    Easy "succeeds if U is a global universe"),
  (fun u ~depth ->
    let global_univs = UGraph.domain (Environ.universes (Global.env ())) in
    match Univ.Universe.level u with
    | Some l when Univ.Level.Set.mem l global_univs -> ()
    | _ -> raise No_clause (* err Pp.(Univ.Universe.pr u ++ str " is not global") *)
  )),
  DocAbove);

  MLCode(Pred("coq.univ.constraints",
    Out(B.list universe_constraint, "CL",
    Full(unit_ctx,  "gives the list of constraints, see also coq.univ.variable.constraints")),
   (fun _ ~depth _ _ state ->
      let sigma = get_sigma state in
      let ustate = Evd.evar_universe_context sigma in
      let constraints = UState.constraints ustate in
      state, !: (Univ.Constraints.elements constraints), []
    )),
  DocAbove);

  LPDoc "-- Universe variables ------";

  MLData universe_level_variable;

  MLCode(Pred("coq.univ.variable",
    InOut(B.ioarg univ,"U",
    InOut(B.ioarg universe_level_variable,"L",
    Full(unit_ctx,  "relates a univ.variable L to a univ U"))),
  (fun u l ~depth _ _ state ->
    match u, l with
    | Data u, NoData ->
        let state, l, _, _ = force_level_of_universe state u in
        state, ?: None +! l, []
    | NoData, Data l ->
        state, !: (Univ.Universe.make l) +? None, []
    | NoData, NoData ->
        let state, (l,u) = new_univ_level_variable state in
        state, !: u +! l, []
    | Data u, Data l ->
      let w = Sorts.sort_of_univ (Univ.Universe.make l) in
      let state = add_universe_constraint state (constraint_leq (Sorts.sort_of_univ u) w) in
      state, ?: None +? None, [])),
  DocAbove);

  MLCode(Pred("coq.univ.variable.constraints",
    In(universe_level_variable, "L",
    Out(B.list universe_constraint, "CL",
    Full(unit_ctx,  "gives the list of constraints on L. Can be used to craft a strict upoly-decl"))),
   (fun v _ ~depth _ _ state ->
      let sigma = get_sigma state in
      let ustate = Evd.evar_universe_context sigma in
      let constraints = UState.constraints ustate in
      let v_constraints = Univ.Constraints.filter (fun (l1,_,l2) -> Univ.Level.(equal v l1 || equal v l2)) constraints in
      state, !: (Univ.Constraints.elements v_constraints), []
    )),
  DocAbove);

  MLCode(Pred("coq.univ.variable.of-term",
    CIn(term,"T",
    Out(universe_level_set,"S",
    Full (proof_context,"collects all univ.variables occurring in T"))),
    (fun t _ ~depth coq_ctx _ state ->
      let s = universes_of_term state t in
      let s = Univ.Level.Set.fold UnivLevelSet.add s UnivLevelSet.empty in
      state, !: s, [])),
  DocAbove);
 
  LPDoc "-- Universe instance (for universe polymorphic global terms) ------";

  LPDoc {|As of today a universe polymorphic constant can only be instantiated
with universe level variables. That is f@{Prop} is not valid, nor
is f@{u+1}. One can only write f@{u} for any u.

A univ-instance is morally a list of universe level variables,
but its list syntax is hidden in the terms. If you really need to
craft or inspect one of these, the following APIs can help you.

Most of the time the user is expected to use coq.env.global which
crafts a fresh, appropriate, universe instance and possibly unify that
term (of the instance it contains) with another one.|};

  MLData uinstance;

  MLCode(Pred("coq.univ-instance",
    InOut(B.ioarg uinstance, "UI",
    InOut(B.ioarg (list B.(ioarg_poly "univ.variable")), "UL",
    Full(global, "relates a univ-instance UI and a list of universe level variables UL"))),
  (fun uinst_arg univs_arg ~depth { env ; options } _ state ->
    match uinst_arg, univs_arg with
    | Data uinst, _ ->
      let elpi_term_of_level state l =
        let state, t, gls = universe_level_variable.Conv.embed ~depth state l in
        assert (gls = []);
        state, mkData t
      in
      let state, univs =
        CArray.fold_left_map elpi_term_of_level state (Univ.Instance.to_array uinst) in
      state, ?: None +! Array.to_list univs, []
    | NoData, Data univs ->
      let readback_or_new state = function
        | NoData -> let state, (l,_) = new_univ_level_variable state in state, l, []
        | Data t -> universe_level_variable.Conv.readback ~depth state t in
      let state, levels, gls = U.map_acc readback_or_new state univs in
      state, !: (Univ.Instance.of_array (Array.of_list levels)) +? None, gls
    | NoData, NoData ->
      err (Pp.str "coq.univ-instance called with no input argument")
  )),
  DocAbove);

  MLCode(Pred("coq.univ-instance.unify-eq",
    In(gref, "GR",
    In(uinstance, "UI1",
    In(uinstance, "UI2",
    InOut(B.ioarg B.diagnostic, "Diagnostic",
    Full(global, "unifies the two universe instances for the same gref"))))),
  (fun gr ui1 ui2 diag ~depth { env } _ state ->
    unify_instances_gref gr ui1 ui2 diag env state EConstr.eq_constr_universes)),
  DocAbove);

  MLCode(Pred("coq.univ-instance.unify-leq",
    In(gref, "GR",
    In(uinstance, "UI1",
    In(uinstance, "UI2",
    InOut(B.ioarg B.diagnostic, "Diagnostic",
    Full(global, "unifies the two universe instances for the same gref. Note: if the GR is not *cumulative* (see Cumulative or #[universes(cumulative)]) then this API imposes an equality constraint."))))),
  (fun gr ui1 ui2 diag ~depth { env } _ state ->
    unify_instances_gref gr ui1 ui2 diag env state EConstr.leq_constr_universes)),
  DocAbove);

  LPDoc "-- Declaration of universe polymorphic global terms -----------";

  LPDoc {|These are the data types used to declare how constants
and inductive types should be declared (see also the @udecl! and
@udecl-cumul! macros). Note that only inductive types can be
declared as cumulative.|};

  MLData universe_constraint;
  MLData universe_variance;
  MLData universe_decl;
  MLData universe_decl_cumul;

  LPDoc "-- Primitive --------------------------------------------------------";

  MLData Coq_elpi_utils.uint63;
  MLData Coq_elpi_utils.float64;
  MLData Coq_elpi_utils.projection;
  MLData primitive_value;

  MLCode(Pred("coq.uint63->int",
    In(Coq_elpi_utils.uint63,"U",
    Out(B.int,"I",
    Easy "Transforms a primitive unsigned integer U into an elpi integer I. Fails if it does not fit.")),
    (fun u _ ~depth:_ ->
       if Uint63.le u (Uint63.of_int max_int) then
         let _, l = Uint63.to_int2 u in
         !: l
       else raise No_clause)),
  DocAbove);

  MLCode(Pred("coq.int->uint63",
    In(B.int,"I",
    Out(Coq_elpi_utils.uint63,"U",
    Easy "Transforms an elpi integer I into a primitive unsigned integer U. Fails if I is negative.")),
    (fun i _ ~depth:_ ->
       if i >= 0 then !: (Uint63.of_int i) else raise No_clause)),
  DocAbove);

  MLCode(Pred("coq.float64->float",
    In(Coq_elpi_utils.float64,"F64",
    Out(B.float,"F",
    Easy "Transforms a primitive float on 64 bits to an elpi one. Currently, it should not fail.")),
    (fun f _ ~depth:_ ->
       let s = Float64.to_hex_string f in
       try !: (float_of_string s)
       with Failure _ -> raise No_clause)),
  DocAbove);

  MLCode(Pred("coq.float->float64",
    In(B.float,"F",
    Out(Coq_elpi_utils.float64,"F64",
    Easy "Transforms an elpi float F to a primitive float on 64 bits. Currently, it should not fail.")),
    (fun f _ ~depth:_ ->
       !: (Float64.of_float f))),
  DocAbove);

  LPCode {|
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% API for extra logical objects
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%|};

  LPDoc "-- Databases (TC, CS, Coercions) ------------------------------------";

  MLData cs_pattern;
  MLData cs_instance;

  MLCode(Pred("coq.CS.declare-instance",
    In(gref, "GR",
    Full(global, {|Declares GR as a canonical structure instance.
Supported attributes:
- @local! (default: false)|})),
  (fun gr ~depth { options } _ -> grab_global_env "coq.CS.declare-instance" (fun state ->
     Canonical.declare_canonical_structure ?local:options.local gr;
    state, (), []))),
  DocAbove);

  MLCode(Pred("coq.CS.db",
    Out(list cs_instance, "Db",
    Read(global,"reads all instances")),
  (fun _ ~depth _ _ _ ->
     !: (Structures.CSTable.(entries ())))),
  DocAbove);

  MLCode(Pred("coq.CS.db-for",
    In(B.unspec gref, "Proj",
    In(B.unspec cs_pattern, "Value",
    Out(list cs_instance, "Db",
    Read(global,"reads all instances for a given Projection or canonical Value, or both")))),
  (fun proj value _ ~depth _ _ state ->
    let env = get_global_env state in
    let sigma = get_sigma state in
    let open Structures in
    (* This comes from recordops, it should be exported *)
     match proj, value with
     | B.Unspec, B.Unspec -> !: (CSTable.entries ())
     | B.Given p, B.Unspec ->
         !: (CSTable.entries_for ~projection:p)
     | B.Unspec, B.Given v ->
         !: (CSTable.entries () |> List.filter (fun { CSTable.value = v1 } -> ValuePattern.equal env v v1))
     | B.Given p, B.Given v ->
         try
           let _, { CanonicalSolution.constant } = CanonicalSolution.find env sigma (p,v) in
           !: [{ CSTable.projection = p; value = v; solution = fst @@ EConstr.destRef sigma constant }]
         with Not_found -> !: [])),
  DocAbove);

  MLCode(Pred("coq.TC.declare-class",
    In(gref, "GR",
    Full(global, {|Declare GR as a type class|})),
  (fun gr ~depth { options } _ -> grab_global_env "coq.TC.declare-class" (fun state ->
     Record.declare_existing_class gr;
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.elpi.toposort",
    In(B.list (pair (B.poly "A") (B.list (B.poly "A"))), "Graph",
    Out(B.list (B.poly "A"), "Nodes in toposort order",
    Read(global,"takes a graph and returns the nodes in topological order"))),
  (fun graph _ ~depth { options } _ _ -> 
    let graph = Coq_elpi_graph.Graph.build graph in 
    let topo_sort = Coq_elpi_graph.Graph.topo_sort graph in 
    (* Coq_elpi_graph.Graph.print string_of_int graph; *)
    !: topo_sort)),
  DocAbove);

  MLData tc_priority;
  MLData tc_instance;
 
  MLCode(Pred("coq.TC.declare-instance",
    In(gref, "GR",
    In(int,  "Priority",
    Full(global, {|Declare GR as a Global type class instance with Priority.
Supported attributes:
- @global! (default: true)|}))),
  (fun gr priority ~depth { options } _ -> grab_global_env "coq.TC.declare-instance" (fun state ->
     let global = if options.local = Some false then Hints.SuperGlobal else Hints.Local in
     let hint_priority = Some priority in
     Classes.existing_instance global gr
          (Some { Hints.empty_hint_info with Typeclasses.hint_priority });
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.TC.db",
    Out(list tc_instance, "Instances",
    Read(global, "reads all type class instances")),
  (fun _ ~depth { env } _ state ->
    let sigma = get_sigma state in
    let x = Typeclasses.typeclasses () in 
    let classes = List.map (fun x -> x.Typeclasses.cl_impl) x in
    !: (classes |> List.map (get_instances env sigma) |> List.concat))),
  DocAbove);

  MLCode(Pred("coq.TC.db-tc",
    Out(list gref, "TypeClasses",
    Easy "reads all type classes"),
  (fun _ ~depth -> !: (
    let x = Typeclasses.typeclasses () in 
    let l = List.map (fun x -> x.Typeclasses.cl_impl) x in 
    l))),
  DocAbove);

  MLCode(Pred("coq.TC.db-for", 
    In(gref, "GR",
    Out(list tc_instance,  "InstanceList",
    Read (global, "reads all instances of the given class GR. Instances are in their precedence order."))),
  (fun gr _ ~depth { env } _ state -> !: (get_instances env (get_sigma state) gr))),
  DocAbove);

  MLCode(Pred("coq.TC.class?",
    In(gref, "GR",
    Easy "checks if GR is a class"),
  (fun gr ~depth ->
     if Typeclasses.is_class gr then () else raise Pred.No_clause)),
  DocAbove);

  MLData class_;
  MLData coercion;

  MLCode(Pred("coq.coercion.declare",
    In(coercion, "C",
    Full (global,{|Declares C = (coercion GR NParams From To) as a coercion From >-> To.
NParams can always be omitted, since it is inferred.
|}^ (* , but if passed it will be checked to be the correct value. TODO needs https://github.com/coq/coq/pull/13902 Coq 8.14 *)
{|If From or To is unspecified, then the endpoints are inferred.
|}^ (* , but if one of the two it is passed it will be checked to be the correct value. TODO needs https://github.com/coq/coq/pull/13902 Coq 8.14 *)
{|Supported attributes:
- @global! (default: false)
- @nonuniform! (default: false)
- @reversible! (default: false)|})),
  (fun (gr, _, source, target) ~depth { options } _ -> grab_global_env "coq.coercion.declare" (fun state ->
     let local = options.local <> Some false in
     let poly = false in
     let reversible = options.reversible = Some true in
     begin match source, target with
     | B.Given source, B.Given target ->
        let source = ComCoercion.class_of_global source in
        ComCoercion.try_add_new_coercion_with_target gr ~local ~poly
          ~reversible ~source ~target
     | _, _ ->
        ComCoercion.try_add_new_coercion gr ~local ~poly ~reversible
     end;
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.coercion.db",
    Out(list coercion, "L",
    Easy ("reads all declared coercions")),
  (fun _ ~depth ->
    (* TODO: fix API in Coq *)
     let pats = Coercionops.inheritance_graph () in
     let coercions = pats |> CList.map_filter (function
       | (source,target),[c] ->
           Some(c.Coercionops.coe_value,
                B.Given c.Coercionops.coe_param,
                B.Given (src_class_of_class source),
                B.Given target)
       | _ -> None) in
     !: coercions)),
  DocAbove);

  MLCode(Pred("coq.coercion.db-for",
    In(class_,"From",
    In(class_,"To",
    Out(list (pair gref int), "L",
    Easy ("L is a path From -> To")))),
  (fun source target _ ~depth ->
    try
      let path = Coercionops.lookup_path_between_class (source,target) in
      let coercions = path |> List.map (fun c ->
        c.Coercionops.coe_value, c.Coercionops.coe_param) in
      !: coercions
    with Not_found -> !: [])),
  DocAbove);

  LPCode {|% Deprecated, use coq.env.projections
pred coq.CS.canonical-projections i:inductive, o:list (option constant).
coq.CS.canonical-projections I L :-
  coq.warning "elpi.deprecated" "elpi.canonical-projections" "use coq.env.projections in place of coq.CS.canonical-projections",
  coq.env.projections I L.
|};

  LPDoc "-- Coq's Hint DB -------------------------------------";
  LPDoc {|Locality of hints is a delicate matter since the Coq default
is, in some cases, to make an hint active even if the module it belongs
to is not imported (just merely required, which can happen transitively).
Coq is aiming at changing the default to #[export], that makes an
hint active only when its enclosing module is imported. See:
https://coq.discourse.group/t/change-of-default-locality-for-hint-commands-in-coq-8-13/1140

This old behavior is available via the @global! flag, but is discouraged.
|};

  MLData mode;

  MLCode(Pred("coq.hints.add-mode",
    In(gref, "GR",
    In(hint_db, "DB",
    In(B.list mode, "Mode",
    Full(global, {|Adds a mode declaration to DB about GR.
Supported attributes:|} ^ hint_locality_doc)))),
  (fun gr (db,_) mode ~depth:_ {options} _ -> grab_global_env "coq.hints.add-mode" (fun state ->
     let locality = hint_locality options in
     Hints.add_hints ~locality [db] (Hints.HintsModeEntry(gr,mode));
     state, (), []
    ))),
  DocAbove);

  MLCode(Pred("coq.hints.modes",
    In(gref, "GR",
    In(hint_db, "DB",
    Out(B.list (B.list mode), "Modes",
    Easy {|Gets all the mode declarations in DB about GR|}))),
  (fun gr (_,db) _ ~depth:_ ->
     try
       let modes = Hints.Hint_db.modes db in
       !: (List.map (fun a -> Array.to_list a) @@ GlobRef.Map.find gr modes)
     with Not_found ->
       !: []
    )),
  DocAbove);

  MLCode(Pred("coq.hints.set-opaque",
    In(constant, "C",
    In(hint_db, "DB",
    In(B.bool, "Opaque",
    Full(global,{|Like Hint Opaque C : DB (or Hint Transparent, if the boolean is ff).
Supported attributes:|} ^ hint_locality_doc)))),
  (fun c (db,_) opaque ~depth:_ {options} _ -> grab_global_env "coq.hints.set-opaque" (fun state ->
    let locality = hint_locality options in
    let transparent = not opaque in
    let r = match c with
       | Variable v -> Tacred.EvalVarRef v
       | Constant c -> Tacred.EvalConstRef c in
     Hints.add_hints ~locality [db] Hints.(HintsTransparencyEntry(HintsReferences [r],transparent));
     state, (), []
    ))),
  DocAbove);

  MLCode(Pred("coq.hints.opaque",
    In(constant, "C",
    In(hint_db, "DB",
    Out(B.bool, "Opaque",
    Easy {|Reads if constant C is opaque (tt) or transparent (ff) in DB|}))),
  (fun c (_,db) _ ~depth:_ ->
     let tr = Hints.Hint_db.transparent_state db in
     match c with
     | Variable v -> !: (not @@ TransparentState.is_transparent_variable tr v)
     | Constant c -> !: (not @@ TransparentState.is_transparent_constant tr c))),
  DocAbove);

  MLCode(Pred("coq.hints.add-resolve",
  In(gref, "GR",
  In(hint_db, "DB",
  In(B.unspec B.int, "Priority",
  CIn(B.unspecC closed_term, "Pattern",
  Full(global,{|Like Hint Resolve GR | Priority Pattern : DB.
Supported attributes:|} ^ hint_locality_doc))))),
(fun gr (db,_) priority pattern ~depth:_ {env;options} _ -> grab_global_env "coq.hints.add-resolve" (fun state ->
  let locality = hint_locality options in
  let hint_priority = unspec2opt priority in
  let sigma = get_sigma state in
  let hint_pattern = unspec2opt pattern |> Option.map (fun x -> x |>
    Coq_elpi_utils.detype env sigma |>
    Patternops.pattern_of_glob_constr) in
  let info = { Typeclasses.hint_priority; hint_pattern } in
   Hints.add_hints ~locality [db] Hints.(Hints.HintsResolveEntry[info,true,PathHints [gr], hint_globref gr]);
   state, (), []
  ))),
DocAbove);


  LPDoc "-- Coq's notational mechanisms -------------------------------------";

  MLData implicit_kind;

  MLCode(Pred("coq.arguments.implicit",
    In(gref,"GR",
    Out(list (list implicit_kind),"Imps",
    Easy "reads the implicit arguments declarations associated to a global reference. See also the [] and {} flags for the Arguments command.")),
  (fun gref _ ~depth ->
    !: (List.map (fun (_,x) -> List.map implicit_kind_of_status x)
          (Impargs.extract_impargs_data (Impargs.implicits_of_global gref))))),
  DocAbove);

  MLCode(Pred("coq.arguments.set-implicit",
    In(gref,"GR",
    In(list (list (B.unspec implicit_kind)),"Imps",
    Full(global,
{|sets the implicit arguments declarations associated to a global reference.
Unspecified means explicit.
See also the [] and {} flags for the Arguments command.
Supported attributes:
- @global! (default: false)|}))),
  (fun gref imps ~depth {options} _ -> grab_global_env "coq.arguments.set-implicit" (fun state ->
     let local = options.local <> Some false in
     let imps = imps |> List.(map (map (function
       | B.Unspec -> Anonymous, Glob_term.Explicit
       | B.Given x -> Anonymous, x))) in
     Impargs.set_implicits local gref imps;
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.arguments.set-default-implicit",
    In(gref,"GR",
    Full(global,
{|sets the default implicit arguments declarations associated to a global reference.
See also the "default implicits" flag to the Arguments command.
Supported attributes:
- @global! (default: false)|})),
  (fun gref ~depth { options } _ -> grab_global_env "coq.arguments.set-default-implicit" (fun state ->
     let local = options.local <> Some false in
     Impargs.declare_implicits local gref;
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.arguments.name",
    In(gref,"GR",
    Out(list (option id),"Names",
    Easy "reads the Names of the arguments of a global reference. See also the (f (A := v)) syntax.")),
  (fun gref _ ~depth ->
    let open Name in
    !: (try Arguments_renaming.arguments_names gref
            |> List.map (function Name x -> Some (Id.to_string x) | _ -> None)
        with Not_found -> []))),
  DocAbove);

  MLCode(Pred("coq.arguments.set-name",
    In(gref,"GR",
    In(list (option id),"Names",
    Full(global,
{|sets the Names of the arguments of a global reference.
See also the :rename flag to the Arguments command.
Supported attributes:
- @global! (default: false)|}))),
  (fun gref names ~depth { options } _ -> grab_global_env "coq.arguments.set-name" (fun state ->
     let local = options.local <> Some false in
     let names = names |> List.map (function
       | None -> Names.Name.Anonymous
       | Some x -> Names.(Name.Name (Id.of_string x))) in
     Arguments_renaming.rename_arguments local gref names;
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.arguments.scope",
    In(gref,"GR",
    Out(list (list id),"Scopes",
    Easy "reads the notation scope of the arguments of a global reference. See also the %scope modifier for the Arguments command")),
  (fun gref _ ~depth -> !: (CNotation.find_arguments_scope gref))),
  DocAbove);

  MLCode(Pred("coq.arguments.set-scope",
    In(gref,"GR",
    In(list (list id),"Scopes",
    Full(global,
{|sets the notation scope of the arguments of a global reference.
Scope can be a scope name or its delimiter.
See also the %scope modifier for the Arguments command.
Supported attributes:
- @global! (default: false)|}))),
  (fun gref scopes ~depth { options } _ -> grab_global_env "coq.arguments.set-scope" (fun state ->
     let local = options.local <> Some false in
     let scopes = scopes |> List.map (List.map (fun k ->
        try ignore (CNotation.find_scope k); k
        with CErrors.UserError _ -> CNotation.find_delimiters_scope k)) in
     CNotation.declare_arguments_scope local gref scopes;
     state, (), []))),
  DocAbove);

  MLData simplification_strategy;

  MLCode(Pred("coq.arguments.simplification",
    In(gref,"GR",
    Out(option simplification_strategy,"Strategy",
    Easy "reads the behavior of the simplification tactics. Positions are 0 based. See also the ! and / modifiers for the Arguments command")),
  (fun gref _ ~depth ->
     !: (Reductionops.ReductionBehaviour.get gref))),
  DocAbove);

  MLCode(Pred("coq.arguments.set-simplification",
    In(gref,"GR",
    In(simplification_strategy, "Strategy",
    Full(global,
{|sets the behavior of the simplification tactics.
Positions are 0 based.
See also the ! and / modifiers for the Arguments command.
Supported attributes:
- @global! (default: false)|}))),
  (fun gref strategy ~depth { options } _ -> grab_global_env "coq.arguments.set-simplification" (fun state ->
     let local = options.local <> Some false in
     Reductionops.ReductionBehaviour.set ~local gref strategy;
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.locate-abbreviation",
    In(id, "Name",
    Out(abbreviation, "Abbreviation",
    Easy "locates an abbreviation.  It's a fatal error if Name cannot be located.")),
  (fun s _ ~depth ->
    let qualid = Libnames.qualid_of_string s in
    let sd =
      try Nametab.locate_abbreviation qualid
      with Not_found -> err Pp.(str "Abbreviation not found: " ++ Libnames.pr_qualid qualid) in
    !:sd)),
  DocAbove);

  MLData abbreviation;

  MLCode(Pred("coq.notation.add-abbreviation",
    In(id,"Name",
    In(int,"Nargs",
    CIn(closed_term,"Body",
    In(flag "bool","OnlyParsing",
    Out(abbreviation, "Abbreviation",
    Full(global, {|Declares an abbreviation Name with Nargs arguments.
The term must begin with at least Nargs "fun" nodes whose domain is ignored, eg (fun _ _ x\ fun _ _ y\ app[global "add",x,y]).
Supported attributes:
- @deprecated! (default: not deprecated)
- @global! (default: false)|})))))),
  (fun name nargs term onlyparsing _ ~depth { env; options } _ -> grab_global_env "coq.notation.add-abbreviation" (fun state ->
       let sigma = get_sigma state in
       let strip_n_lambas nargs env term =
       let rec aux vars nenv env n t =
         if n = 0 then List.rev vars, nenv, env, t
         else match EConstr.kind sigma t with
         | Constr.Lambda(name,ty,t) ->
             let name, id =
                match name with
               | { Context.binder_name = Names.Name.Name id; _ } ->
                 let id = Id.of_string_soft (Printf.sprintf "_elpi_ctx_entry_%d_was_%s_" n (Id.to_string id)) in
                 { name with Context.binder_name = Names.Name.Name id }, id
               | _ ->
                 let id = Id.of_string_soft (Printf.sprintf "_elpi_ctx_entry_%d_" n) in
                 { name with Context.binder_name = Names.Name.Name id }, id
             in
             let nenv, vars =
               { nenv with Notation_term.ninterp_var_type =
                   Id.Map.add id (Notation_term.NtnInternTypeAny None)
                     nenv.Notation_term.ninterp_var_type },
               (id, ((Constrexpr.(InConstrEntry,(LevelSome,None)),([],[])),Notation_term.NtnTypeConstr)) :: vars in
             let env = EConstr.push_rel (Context.Rel.Declaration.LocalAssum(name,ty)) env in
             aux vars nenv env (n-1) t
         | _ ->
             U.type_error
               (Printf.sprintf "coq.notation.add-abbreviation: term with %d more lambdas expected" n)
         in
         let vars = [] in
         let nenv =
           {
              Notation_term.ninterp_var_type = Id.Map.empty;
              ninterp_rec_vars = Id.Map.empty;
           } in
         aux vars nenv env nargs term
     in
     let local = options.local <> Some false in
     let onlyparsing = (onlyparsing = B.Given true) in
     let name = Id.of_string name in
     let vars, nenv, env, body = strip_n_lambas nargs env term in
     let gbody = Coq_elpi_utils.detype env sigma body in
     let pat, _ = Notation_ops.notation_constr_of_glob_constr nenv gbody in
     Abbreviation.declare_abbreviation ~local ~onlyparsing options.deprecation name (vars,pat);
     let qname = Libnames.qualid_of_string (Id.to_string name) in
     match Nametab.locate_extended qname with
     | Globnames.TrueGlobal _ -> assert false
     | Globnames.Abbrev sd -> state, !: sd, []))),
  DocAbove);

  MLCode(Pred("coq.notation.abbreviation",
    In(abbreviation,"Abbreviation",
    In(B.list (B.poly "term"),"Args",
    Out(B.poly "term","Body",
    Full(global, "Unfolds an abbreviation")))),
  (fun sd arglist _ ~depth {env} _ state ->
    let args, _ = Abbreviation.search_abbreviation sd in
    let nargs = List.length args in
    let argno = List.length arglist in
    if nargs > argno then
      err Pp.(str"coq.notation.abbreviation: abbreviation " ++
        Names.Label.print (Names.KerName.label sd) ++ str " expects " ++
        int nargs ++ str " arguments but was given " ++ int argno);
    let open Constrexpr in
    let binders, vars = List.split (CList.init nargs (fun i ->
      let name = Coq_elpi_glob_quotation.mk_restricted_name i in
      let lname = CAst.make @@ Name.Name (Id.of_string name) in
      CLocalAssum([lname],Default Glob_term.Explicit, CAst.make @@ CHole(None,Namegen.IntroAnonymous)),
      (CAst.make @@ CRef(Libnames.qualid_of_string name,None), None))) in
    let eta = CAst.(make @@ CLambdaN(binders,make @@ CApp(make @@ CRef(Libnames.qualid_of_string (KerName.to_string sd),None),vars))) in
    let sigma = get_sigma state in
    let geta = Constrintern.intern_constr env sigma eta in
    let state, teta = Coq_elpi_glob_quotation.gterm2lp ~depth state geta in
    let t =
      let rec aux ~depth n t =
        if n = 0 then t
        else match Coq_elpi_HOAS.is_lam ~depth t with
        | Some(_,bo) -> E.mkLam (aux ~depth:(depth+1) (n-1) bo)
        | None -> CErrors.anomaly Pp.(str"coq.notation.abbreviation")
      in
        aux ~depth nargs teta in
    state, !: (U.beta ~depth t arglist), []
  )),
  DocAbove);

  MLCode(Pred("coq.notation.abbreviation-body",
    In(abbreviation,"Abbreviation",
    Out(B.int,"Nargs",
    Out(B.poly "term","Body",
    Full(global, "Retrieves the body of an abbreviation")))),
  (fun sd _ _ ~depth {env} _ state ->
    let args, _ = Abbreviation.search_abbreviation sd in
    let nargs = List.length args in
    let open Constrexpr in
    let binders, vars = List.split (CList.init nargs (fun i ->
      let name = Coq_elpi_glob_quotation.mk_restricted_name i in
      let lname = CAst.make @@ Name.Name (Id.of_string name) in
      CLocalAssum([lname],Default Glob_term.Explicit, CAst.make @@ CHole(None,Namegen.IntroAnonymous)),
      (CAst.make @@ CRef(Libnames.qualid_of_string name,None), None))) in
    let eta = CAst.(make @@ CLambdaN(binders,make @@ CApp(make @@ CRef(Libnames.qualid_of_string (KerName.to_string sd),None),vars))) in
    let sigma = get_sigma state in
    let geta = Constrintern.intern_constr env sigma eta in
    let state, teta = Coq_elpi_glob_quotation.gterm2lp ~depth state geta in
    state, !: nargs +! teta, []
  )),
  DocAbove);

  MLCode(Pred("coq.notation.add-abbreviation-for-tactic",
    In(B.string,"Name",
    In(B.string,"TacticName",
    CIn(CConv.(!>>) B.list tactic_arg,"FixedArgs",
    Full(proof_context, {|Declares a parsing rule similar to
  Notation Name X1..Xn := ltac:(elpi TacticName FixedArgs (X1)..(Xn))
so that Name can be used in the middle of a term to invoke an
elpi tactic. While FixedArgs can contain str, int, and trm all
other arguments will necessarily be terms, and their number is
not fixed (the user can pass as many as he likes).
The tactic receives as the elpi.loc attribute the precise location
at which the term is written (unlike if a regular abbreviation was
declared by hand).
A call to coq.notation.add-abbreviation-for-tactic TacName TacName []
is equivalent to Elpi Export TacName.|})))),
    (fun name tacname more_args ~depth { options} _ -> grab_global_env "coq.notation.add-abbreviation-for-tactic" (fun state ->
      let sigma = get_sigma state in
      let env = get_global_env state in
      let tac_fixed_args = more_args |> List.map (function
        | Coq_elpi_arg_HOAS.Cint n -> Coq_elpi_arg_HOAS.Tac.Int n
        | Coq_elpi_arg_HOAS.Cstr s -> Coq_elpi_arg_HOAS.Tac.String s
        | Coq_elpi_arg_HOAS.Ctrm t -> Coq_elpi_arg_HOAS.Tac.Term (Coq_elpi_utils.detype env sigma t,None)
        | Coq_elpi_arg_HOAS.CLtac1 _ -> nYI "tactic notation with LTac1 argument") in
      let abbrev_name = Coq_elpi_utils.string_split_on_char '.' name in
      let tac_name = Coq_elpi_utils.string_split_on_char '.' tacname in
      Lib.add_leaf @@ inAbbreviationForTactic { abbrev_name; tac_name; tac_fixed_args};
      state, (), []))),
    DocAbove);

  MLData attribute_value;
  MLData attribute;

  LPCode {|
% see coq-lib.elpi for coq.parse-attributes generating the options below
type get-option string -> A -> prop.
|};

  LPDoc "-- Coq's pretyper ---------------------------------------------------";

  MLCode(Pred("coq.sigma.print",
    Read(raw_ctx, "Prints Coq's Evarmap and the mapping to/from Elpi's unification variables"),
    (fun ~depth hyps constraints state ->
      let state, _, _, _ = get_current_env_sigma ~depth hyps constraints state in
      Feedback.msg_notice Pp.(
        str (Format.asprintf "%a" API.RawPp.constraints constraints));
      Feedback.msg_notice Pp.(str (show_coq_engine ~with_univs:false state));
      Feedback.msg_notice Pp.(str (show_coq_elpi_engine_mapping state));
      ())),
  DocAbove);

  MLCode(Pred("coq.typecheck",
    CIn(term,  "T",
    CInOut(B.ioargC term, "Ty",
    InOut(B.ioarg B.diagnostic, "Diagnostic",
    Full (proof_context,
{|typchecks a term T returning its type Ty. If Ty is provided, then
the inferred type is unified (see unify-leq) with it.
Universe constraints are put in the constraint store.|})))),
  (fun t ety diag ~depth proof_context _ state ->
     try
       let sigma = get_sigma state in
       let sigma, ty = Typing.type_of proof_context.env sigma t in
       match ety with
       | Data ety ->
           let sigma = Evarconv.unify proof_context.env sigma ~with_ho:true Conversion.CUMUL ty ety in
           let state, assignments = set_current_sigma ~depth state sigma in
           state, ?: None +! B.mkOK, assignments
       | NoData ->
           let flags = Evarconv.default_flags_of TransparentState.full in
           let sigma = Evarconv.solve_unif_constraints_with_heuristics ~flags ~with_ho:true proof_context.env sigma in
           let state, assignments = set_current_sigma ~depth state sigma in
           state, !: ty +! B.mkOK, assignments
     with Pretype_errors.PretypeError (env, sigma, err) ->
       match diag with
       | Data B.OK ->
          (* optimization: don't print the error if caller wants OK *)
          raise No_clause
       | _ ->
          let error = string_of_ppcmds proof_context.options @@ Himsg.explain_pretype_error env sigma err in
          state, ?: None +! B.mkERROR error, [])),
  DocAbove);

  MLCode(Pred("coq.typecheck-ty",
    CIn(term,  "Ty",
    InOut(B.ioarg sort, "U",
    InOut(B.ioarg B.diagnostic, "Diagnostic",
    Full (proof_context,
{|typchecks a type Ty returning its universe U. If U is provided, then
the inferred universe is unified (see unify-leq) with it.
Universe constraints are put in the constraint store.|})))),
  (fun ty es diag ~depth proof_context _ state ->
     try
       let sigma = get_sigma state in
       let sigma, s = Typing.sort_of proof_context.env sigma ty in
       match es with
       | Data es ->
           let sigma = Evarconv.unify proof_context.env sigma ~with_ho:true Conversion.CUMUL (EConstr.mkSort s) (EConstr.mkSort (EConstr.ESorts.make es)) in
           let state, assignments = set_current_sigma ~depth state sigma in
           state, !: es +! B.mkOK, assignments
       | NoData ->
           let flags = Evarconv.default_flags_of TransparentState.full in
           let sigma = Evarconv.solve_unif_constraints_with_heuristics ~flags ~with_ho:true proof_context.env sigma in
           let state, assignments = set_current_sigma ~depth state sigma in
           state, !: (EConstr.ESorts.kind sigma s) +! B.mkOK, assignments
     with Pretype_errors.PretypeError (env, sigma, err) ->
       match diag with
       | Data B.OK ->
          (* optimization: don't print the error if caller wants OK *)
          raise No_clause
       | _ ->
          let error = string_of_ppcmds proof_context.options @@ Himsg.explain_pretype_error env sigma err in
          state, ?: None +! B.mkERROR error, [])),
  DocAbove);

  MLCode(Pred("coq.unify-eq",
    CIn(term, "A",
    CIn(term, "B",
    InOut(B.ioarg B.diagnostic, "Diagnostic",
    Full (proof_context, "unifies the two terms")))),
  (fun a b diag ~depth proof_context _ state ->
     let sigma = get_sigma state in
     try
       let sigma = Evarconv.unify proof_context.env sigma ~with_ho:true Conversion.CONV a b in
       let state, assignments = set_current_sigma ~depth state sigma in
       state, !: B.mkOK, assignments
     with Pretype_errors.PretypeError (env, sigma, err) ->
       match diag with
       | Data B.OK ->
          (* optimization: don't print the error if caller wants OK *)
          raise No_clause
       | _ ->
          let error = string_of_ppcmds proof_context.options @@ Himsg.explain_pretype_error env sigma err in
          state, !: (B.mkERROR error), [])),
  DocAbove);

  MLCode(Pred("coq.unify-leq",
    CIn(term, "A",
    CIn(term, "B",
    InOut(B.ioarg B.diagnostic, "Diagnostic",
    Full (proof_context, "unifies the two terms (with cumulativity, if they are types)")))),
  (fun a b diag ~depth proof_context _ state ->
     let sigma = get_sigma state in
     try
       let sigma = Evarconv.unify proof_context.env sigma ~with_ho:true Conversion.CUMUL a b in
       let state, assignments = set_current_sigma ~depth state sigma in
       state, !: B.mkOK, assignments
     with Pretype_errors.PretypeError (env, sigma, err) ->
       match diag with
       | Data B.OK ->
          (* optimization: don't print the error if caller wants OK *)
          raise No_clause
       | _ ->
          let error = string_of_ppcmds proof_context.options @@ Himsg.explain_pretype_error env sigma err in
          state, !: (B.mkERROR error), [])),
  DocAbove);

   MLCode(Pred("coq.elaborate-skeleton",
     CIn(term_skeleton,  "T",
     CInOut(B.ioargC_flex term,  "ETy",
     COut(term,  "E",
     InOut(B.ioarg B.diagnostic, "Diagnostic",
     Full (proof_context,{|elabotares T against the expected type ETy.
T is allowed to contain holes (unification variables) but these are
not assigned even if the elaborated term has a term in place of the
hole. Similarly universe levels present in T are disregarded.
Supported attributes:
- @keepunivs! (default false, do not disregard universe levels)
- @no-tc! (default false, do not infer typeclasses) |}))))),
  (fun gt ety _ diag ~depth proof_context _ state ->
    let flags = if proof_context.options.no_tc = Some true then {(Pretyping.default_inference_flags false) with  use_typeclasses = NoUseTC} else Pretyping.default_inference_flags false in
    try
      let sigma = get_sigma state in
      let ety_given, expected_type =
        match ety with
        | NoData -> `No, Pretyping.WithoutTypeConstraint
        | Data ety ->
            match EConstr.kind sigma ety with
            | Constr.Evar _ -> `NoUnify ety, Pretyping.WithoutTypeConstraint
            | _ -> `Yes, Pretyping.OfType ety
      in
      let sigma, uj_val, uj_type =
        Pretyping.understand_tcc_ty ~flags proof_context.env sigma ~expected_type gt in
      match ety_given with
      | `No ->
          let state, assignments = set_current_sigma ~depth state sigma in
          state, !: uj_type +! uj_val +! B.mkOK, assignments
      | `Yes ->
          let state, assignments = set_current_sigma ~depth state sigma in
          state, ?: None +! uj_val +! B.mkOK, assignments
      | `NoUnify ety ->
          let sigma = Evarconv.unify proof_context.env sigma ~with_ho:true Conversion.CUMUL uj_type ety in
          let state, assignments = set_current_sigma ~depth state sigma in
          state, ?: None +! uj_val +! B.mkOK, assignments
    with Pretype_errors.PretypeError (env, sigma, err) ->
       match diag with
       | Data B.OK ->
          (* optimization: don't print the error if caller wants OK *)
          raise No_clause
       | _ ->
          let error = string_of_ppcmds proof_context.options @@ Himsg.explain_pretype_error env sigma err in
          state, ?: None +? None +! B.mkERROR error, [])),
  DocAbove);

   MLCode(Pred("coq.elaborate-ty-skeleton",
     CIn(term_skeleton,  "T",
     Out(sort, "U",
     COut(term,  "E",
     InOut(B.ioarg B.diagnostic, "Diagnostic",
     Full (proof_context,{|elabotares T expecting it to be a type of sort U.
T is allowed to contain holes (unification variables) but these are
not assigned even if the elaborated term has a term in place of the
hole. Similarly universe levels present in T are disregarded.
Supported attributes:
- @keepunivs! (default false, do not disregard universe levels)
- @no-tc! (default false, do not infer typeclasses)|}))))),
  (fun gt es _ diag ~depth proof_context _ state ->
    try
      let sigma = get_sigma state in
      let flags = if proof_context.options.no_tc = Some true then {(Pretyping.default_inference_flags false) with  use_typeclasses = NoUseTC} else Pretyping.default_inference_flags false in
      let expected_type = Pretyping.IsType in
      let sigma, uj_val, uj_type =
        Pretyping.understand_tcc_ty ~flags proof_context.env sigma ~expected_type gt in
      let sort = EConstr.ESorts.kind sigma @@ EConstr.destSort sigma uj_type in
      let state, assignments = set_current_sigma ~depth state sigma in
      state, !: sort +! uj_val +! B.mkOK, assignments
    with Pretype_errors.PretypeError (env, sigma, err) ->
       match diag with
       | Data B.OK ->
          (* optimization: don't print the error if caller wants OK *)
          raise No_clause
       | _ ->
          let error = string_of_ppcmds proof_context.options @@ Himsg.explain_pretype_error env sigma err in
          state, ?: None +? None +! B.mkERROR error, [])),
  DocAbove);

  LPDoc "-- Coq's reduction flags    ------------------------------------";

  MLData reduction_kind;
  MLData reduction_flags;

  MLCode(Pred("coq.redflags.add",
    In(reduction_flags,"Flags",
    In(B.list reduction_kind,"Options",
    Out(reduction_flags,"NewFlags",
    Easy "Updates reduction Flags by adding Options"))),
    (fun f l _ ~depth ->
       let open CClosure in
       let f = List.fold_left RedFlags.red_add f l in
       !: f)),
  DocAbove);

  MLCode(Pred("coq.redflags.sub",
    In(reduction_flags,"Flags",
    In(B.list reduction_kind,"Options",
    Out(reduction_flags,"NewFlags",
    Easy "Updates reduction Flags by removing Options"))),
    (fun f l _ ~depth ->
       let open CClosure in
       let f = List.fold_left RedFlags.red_sub f l in
       !: f)),
  DocAbove);

  LPDoc "-- Coq's reduction machines ------------------------------------";

  MLCode(Pred("coq.reduction.lazy.whd",
    CIn(term,"T",
    COut(term,"Tred",
    Read(proof_context, {|Puts T in weak head normal form.
Supported attributes:
- @redflags! (default coq.redflags.all)|}))),
    (fun t _ ~depth proof_context constraints state ->
       let sigma = get_sigma state in
       let flags = Option.default CClosure.all proof_context.options.redflags in
       let t = Reductionops.clos_whd_flags flags proof_context.env sigma t in
       !: t)),
  DocAbove);

  MLCode(Pred("coq.reduction.lazy.norm",
    CIn(term,"T",
    COut(term,"Tred",
    Read(proof_context, {|Puts T in normal form.
Supported attributes:
- @redflags! (default coq.redflags.all)|}))),
    (fun t _ ~depth proof_context constraints state ->
       let sigma = get_sigma state in
       let flags = Option.default CClosure.all proof_context.options.redflags in
       let t = Reductionops.clos_norm_flags flags proof_context.env sigma t in
       !: t)),
  DocAbove);

  MLCode(Pred("coq.reduction.lazy.bi-norm",
    CIn(term,"T",
    COut(term,"Tred",
    Read(proof_context, "Puts T in normal form only reducing beta and iota redexes"))),
    (fun t _ ~depth proof_context constraints state ->
       let sigma = get_sigma state in
       let t = Reductionops.nf_betaiota proof_context.env sigma t in
       !: t)),
  DocAbove);

  MLCode(Pred("coq.reduction.cbv.norm",
    CIn(term,"T",
    COut(term,"Tred",
    Read(proof_context, {|Puts T in normal form using the call by value strategy.
Supported attributes:
- @redflags! (default coq.redflags.all)|}))),
    (fun t _ ~depth proof_context constraints state ->
       let sigma = get_sigma state in
       let flags = Option.default CClosure.all proof_context.options.redflags in
       let t = Tacred.cbv_norm_flags flags proof_context.env sigma t in
       !: t)),
  DocAbove);

  MLCode(Pred("coq.reduction.vm.norm",
    CIn(term,"T",
    CIn(B.unspecC term,"Ty",
    COut(term,"Tred",
    Read(proof_context, "Puts T in normal form using [vm_compute]'s machinery. Its type Ty can be omitted (but is recomputed)")))),
    (fun t ty _ ~depth proof_context constraints state ->
       let sigma = get_sigma state in
       let sigma, ty =
         match ty with
         | B.Given ty -> sigma, ty
         | B.Unspec -> Typing.type_of proof_context.env sigma t in
       let t = Vnorm.cbv_vm proof_context.env sigma t ty in
       !: t)),
  DocAbove);

  MLCode(Pred("coq.reduction.native.norm",
    CIn(term,"T",
    CIn(B.unspecC term,"Ty",
    COut(term,"Tred",
    Read(proof_context, "Puts T in normal form using [native_compute]'s machinery. Its type Ty can be omitted (but is recomputed). Falls back to vm.norm if native compilation is not available.")))),
    (fun t ty _ ~depth proof_context constraints state ->
       let sigma = get_sigma state in
       let sigma, ty =
         match ty with
         | B.Given ty -> sigma, ty
         | B.Unspec -> Typing.type_of proof_context.env sigma t in
       let t =
         if (Environ.typing_flags proof_context.env).enable_native_compiler then
           Nativenorm.native_norm proof_context.env sigma t ty
         else
           Vnorm.cbv_vm proof_context.env sigma t ty in
       !: t)),
  DocAbove);

  MLCode(Pred("coq.reduction.native.available?",
    Easy "Is native compilation available on this system/configuration?",
    (fun ~depth:_ -> if not ((Global.typing_flags ()).enable_native_compiler) then raise No_clause)),
  DocAbove);

  LPCode {|% Deprecated, use coq.reduction.cbv.norm
pred coq.reduction.cbv.whd_all i:term, o:term.
coq.reduction.cbv.whd_all T R :-
  coq.warning "elpi.deprecated" "elpi.cbv-whd-all" "use coq.reduction.cbv.norm in place of coq.reduction.cbv.whd_all",
  coq.reduction.cbv.norm T R.
|};

  LPCode {|% Deprecated, use coq.reduction.vm.norm
pred coq.reduction.vm.whd_all i:term, i:term, o:term.
coq.reduction.vm.whd_all T TY R :-
  coq.warning "elpi.deprecated" "elpi.vm-whd-all" "use coq.reduction.vm.norm in place of coq.reduction.vm.whd_all",
  coq.reduction.vm.norm T TY R.
|};

  LPCode {|
pred coq.reduction.lazy.whd_all i:term, o:term.
coq.reduction.lazy.whd_all X Y :-
  @redflags! coq.redflags.all => coq.reduction.lazy.whd X Y.
|};

  MLCode(Pred("coq.reduction.eta-contract",
  CIn(term,"T",
  COut(term,"Tred",
  Read(proof_context, {|Removes all eta expansions from T|}))),
  (fun t _ ~depth proof_context constraints state ->
     let sigma = get_sigma state in
     let t = eta_contract proof_context.env sigma t in
     !: t)),
  DocAbove);

  LPDoc "-- Coq's conversion strategy tweaks --------------------------";

  MLData conversion_strategy;

  MLCode(Pred("coq.strategy.set",
    In(B.list constant, "CL",
    In(conversion_strategy, "Level",
    Full(global,"Sets the unfolding priority for all the constants in the list CL. See the command Strategy."))),
    (fun csts level ~depth:_ ctx _ -> grab_global_env "coq.strategy.set" (fun state ->
       let local = ctx.options.local = Some true in
       let csts = csts |> List.map (function
         | Constant c -> Tacred.EvalConstRef c
         | Variable v -> Tacred.EvalVarRef v) in
       Redexpr.set_strategy local [level, csts];
       state, (), []))),
  DocAbove);

  MLCode(Pred("coq.strategy.get",
    In(constant, "C",
    Out(conversion_strategy, "Level",
    Read(global, "Gets the unfolding priority for C"))),
    (fun c _ ~depth:_ _ _ state ->
       let env = get_global_env state in
       let oracle = Environ.oracle env in
       let k = match c with
         | Constant c -> Names.ConstKey c
         | Variable v -> Names.VarKey v in
       !: (Conv_oracle.get_strategy oracle k))),
  DocAbove);

  LPDoc "-- Coq's tactics --------------------------------------------";

  MLData Coq_elpi_arg_HOAS.tac;

  MLCode(Pred("coq.ltac.fail",
    In(B.unspec B.int,"Level",
    VariadicIn(unit_ctx, !> B.any, "Interrupts the Elpi program and calls Ltac's fail Level Msg, where Msg is the printing of the remaining arguments. Level can be left unspecified and defaults to 0")),
   (fun level args ~depth _hyps _constraints _state ->
     let pp = pp ~depth in
     let level = match level with B.Given x -> x | B.Unspec -> 0 in
     let msg =
       if args = [] then Pp.mt ()
       else Pp.(str (pp2string (P.list ~boxed:true pp " ") args)) in
     ltac_fail_err level msg)),
  DocAbove);

  MLCode(Pred("coq.ltac.collect-goals",
    CIn(failsafe_term, "T",
    Out(list sealed_goal, "Goals",
    Out(list sealed_goal, "ShelvedGoals",
    Full(proof_context, {|
Turns the holes in T into Goals.
Goals are closed with nablas.
ShelvedGoals are goals which can be solved by side effect (they occur
in the type of the other goals).
The order of Goals is given by the traversal order of EConstr.fold (a
fold_left over the terms, letin body comes before the type).
|})))),
    (fun proof _ shelved ~depth proof_context constraints state ->
      let sigma = get_sigma state in
      let evars_of_term evd c =
        let rec evrec (acc_set,acc_rev_l as acc) c =
          let c = EConstr.whd_evar evd c in
          match EConstr.kind sigma c with
          | Constr.Evar (n, l) ->
              if Evar.Set.mem n acc_set then SList.Skip.fold evrec acc l
              else
                let acc = Evar.Set.add n acc_set, n :: acc_rev_l in
                SList.Skip.fold evrec acc l
          | _ -> EConstr.fold sigma evrec acc c
        in
        let _, rev_l = evrec (Evar.Set.empty, []) c in
        List.rev rev_l in
      let subgoals = evars_of_term sigma proof in
      let free_evars =
        let cache = Evarutil.create_undefined_evars_cache () in
        let map ev =
          let EvarInfo evi = Evd.find sigma ev in
          let fevs = lazy (Evarutil.filtered_undefined_evars_of_evar_info ~cache sigma evi) in
          (ev, fevs)
        in
        List.map map subgoals in
      let shelved_subgoals, subgoals =
        CList.partition
          (fun g ->
             CList.exists (fun (tgt, lazy evs) -> not (Evar.equal g tgt) && Evar.Set.mem g evs) free_evars)
          subgoals in
      let shelved =
        match shelved with
        | Keep -> Some shelved_subgoals
        | Discard -> None in
      state, !: subgoals +? shelved, []
    )),
    DocAbove);

  MLCode(Pred("coq.ltac.call-ltac1",
    In(B.any, "Tac",
    CIn(goal, "G",
    Out(list sealed_goal,"GL",
    Full(raw_ctx, {|Calls Ltac1 tactic Tac on goal G (passing the arguments of G, see coq.ltac.call for a handy wrapper).
Tac can either be a string (the tactic name), or a value
of type ltac1-tactic, see the tac argument constructor
and the ltac_tactic:(...) syntax to pass arguments to
an elpi tactic.|})))),
    (fun tac (proof_context,goal,tac_args) _ ~depth _ _ -> abstract__grab_global_env_keep_sigma "coq.ltac.call-ltac1" (fun state ->
      let open Ltac_plugin in
      let sigma = get_sigma state in
       let tac_args = tac_args |> List.map (function
         | Coq_elpi_arg_HOAS.Ctrm t -> Tacinterp.Value.of_constr t
         | Coq_elpi_arg_HOAS.Cstr s -> Geninterp.(Val.inject (val_tag (Genarg.topwit Stdarg.wit_string))) s
         | Coq_elpi_arg_HOAS.Cint i -> Tacinterp.Value.of_int i
         | Coq_elpi_arg_HOAS.CLtac1 x -> x) in
       let tactic =
         let tac =
          match E.look ~depth tac with
          | E.CData s when API.RawOpaqueData.is_string s ->
              let tac_name = API.RawOpaqueData.to_string s in
              let tac_name =
                let q = Libnames.qualid_of_string tac_name in
                try Tacenv.locate_tactic q
                with Not_found ->
                  match Tacenv.locate_extended_all_tactic q with
                  | [x] -> x
                  | _::_::_ -> err Pp.(str"Ltac1 tactic " ++ str tac_name ++ str" is ambiguous, qualify the name")
                  | [] -> err Pp.(str"Ltac1 tactic " ++ str tac_name ++ str" not found") in
              let tacref = Locus.ArgArg (Loc.tag @@ tac_name) in
              let tacexpr = Tacexpr.(CAst.make @@ TacArg (TacCall (CAst.make @@ (tacref, [])))) in
              Tacinterp.Value.of_closure (Tacinterp.default_ist ()) tacexpr
          | E.CData t when Coq_elpi_arg_HOAS.is_ltac_tactic t ->
              Coq_elpi_arg_HOAS.to_ltac_tactic t
          | _ -> U.type_error ("coq.ltac.call-ltac1: string or ltac1-tactic are expected as the tactic to call")
         in
         Tacinterp.Value.apply tac tac_args in
       let subgoals, sigma =
         let open Proofview in let open Notations in
         let focused_tac =
           Unsafe.tclSETGOALS [with_empty_state goal] <*> tactic in
         let _, pv = init sigma [] in
         let (), pv, _, _ =
           let vernac_state = Vernacstate.freeze_full_state () in
           try
             let rc = apply ~name:(Id.of_string "elpi") ~poly:false proof_context.env focused_tac pv in
             let pstate = Vernacstate.Stm.pstate (Vernacstate.freeze_full_state ()) in
             let vernac_state = Vernacstate.Stm.set_pstate vernac_state pstate in
             Vernacstate.unfreeze_full_state vernac_state;
             rc
           with e when CErrors.noncritical e ->
             Vernacstate.unfreeze_full_state vernac_state;
             Feedback.msg_debug (CErrors.print e);
             raise Pred.No_clause
         in
           proofview pv in

       Declare.Internal.export_side_effects (Evd.eval_side_effects sigma);
       
       let state, assignments = set_current_sigma ~depth state sigma in
       state, !: subgoals, assignments
      ))),
  DocAbove);

  MLCode(Pred("coq.ltac.id-free?",
  In(id, "ID",
  CIn(goal, "G",
  Read(raw_ctx, {|
    Fails if ID is already used in G. Note that ids which are taken are renamed
    on the fly (since in the HOAS of terms, names are just pretty printing
    hints), but for the ergonomy of a tactic it may help to know if an
    hypothesis name is already taken.
|}))),
  (fun id (proof_context,_,_) ~depth _ _ _ ->
     if not @@ Id.Set.mem (Names.Id.of_string_soft id) proof_context.names then ()
     else raise No_clause)),
  DocAbove);

  LPDoc "-- Coq's options system --------------------------------------------";

  MLData goption;

  MLCode(Pred("coq.option.get",
    In(B.list B.string,"Option",
    Out(goption,"Value",
    Easy "reads Option. Reading a non existing option is a fatal error.")),
  (fun name _ ~depth ->
    let table = Goptions.get_tables () in
    match Goptions.OptionMap.find_opt name table with
    | Some { Goptions.opt_value = x; _ }  -> !: x
    | None -> err Pp.(str "option " ++ str (String.concat " " name) ++ str" does not exist"))),
  DocAbove);

  MLCode(Pred("coq.option.set",
    In(B.list B.string,"Option",
    In(goption,"Value",
    Easy "writes Option. Writing a non existing option is a fatal error.")),
  (fun name value ~depth ->
    let open Goptions in
    match value with
    | BoolValue x -> Goptions.set_bool_option_value name x
    | IntValue x -> Goptions.set_int_option_value name x
    | StringOptValue None -> Goptions.unset_option_value_gen name
    | StringOptValue (Some x) -> Goptions.set_string_option_value name x
    | StringValue _ -> assert false)),
  DocAbove);

  MLCode(Pred("coq.option.available?",
    In(B.list B.string,"Option",
    Out(B.bool,"Deprecated",
    Easy "checks if Option exists and tells if is deprecated (tt) or not (ff)")),
  (fun name _ ~depth ->
    let table = Goptions.get_tables () in
    match Goptions.OptionMap.find_opt name table with
    | Some { Goptions.opt_depr = x; _ }  -> !: (Option.has_some x)
    | None -> raise No_clause)),
  DocAbove);

  MLCode(Pred("coq.option.add",
    In(B.list B.string,"Option",
    In(goption,"Value",
    In(B.unspec B.bool,"Deprecated",
    Easy {|
adds a new option to Coq setting its current value (and type).
Deprecated can be left unspecified and defaults to ff.
This call cannot be undone in a Coq interactive session, use it once
and for all in a .v file which your clients will load. Eg.

  Elpi Query lp:{{ coq.option.add ... }}.
  
|}))),
  (fun key value depr ~depth ->
    let depr = Option.default false @@ unspec2opt depr in
    Lib.add_leaf @@ inGoption (depr,key,value))),
  DocAbove);

  LPDoc "-- Datatypes conversions --------------------------------------------";

  MLData name;

  MLCode(Pred("coq.name-suffix",
    In(name, "Name",
    In(B.any,  "Suffix",
    Out(name,"NameSuffix",
    Easy "suffixes a Name with a string or an int or another name"))),
  (fun n suffix _ ~depth ->
     match E.look ~depth suffix with
     | E.CData i when API.RawOpaqueData.(is_string i || is_int i || isname i) ->
         let s = Pp.string_of_ppcmds (Name.print n) in
         let suffix =
           if API.RawOpaqueData.is_string i then API.RawOpaqueData.to_string i
           else if API.RawOpaqueData.is_int i then string_of_int (API.RawOpaqueData.to_int i)
           else Pp.string_of_ppcmds (Name.print (nameout i)) in
         let s = s ^ suffix in
         !: (Name.mk_name (Id.of_string s))
     | _ -> err Pp.(str "coq.name-suffix: suffix is not int, nor string nor name"))),
  DocAbove);

  MLCode(Pred("coq.string->name",
    In(B.string, "Hint",
    Out(name,  "Name",
    Easy "creates a name hint")),
  (fun s _ ~depth -> !: (Name.mk_name (Id.of_string s)))),
  DocAbove);

  LPCode {|
pred coq.id->name i:id, o:name.
coq.id->name S N :- coq.string->name S N.
  |};

  MLCode(Pred("coq.name->id",
    In(name, "Name",
    Out(id,  "Id",
    Easy "tuns a pretty printing hint into a string. This API is for internal use, no guarantee on its behavior.")),
  (fun n _ ~depth ->
     match n with
     | Name.Anonymous -> !: "_"
     | Name.Name s -> !: (Id.to_string s))),
  DocAbove);

  MLCode(Pred("coq.gref->id",
    In(gref, "GR",
    Out(id, "Id",
    Read (unit_ctx, "extracts the label (last component of a full kernel name)"))),
  (fun gr _ ~depth _ _ state ->
    !: (gr2id state gr))),
   DocAbove);

  MLCode(Pred("coq.gref->string",
    In(gref, "GR",
    Out(B.string, "FullPath",
    Read(unit_ctx, "extract the full kernel name"))),
  (fun gr _ ~depth h c state ->
    let path = gr2path gr in
    let id = gr2id state gr in
    !: (String.concat "." (path @ [id])))),
  DocAbove);

  MLCode(Pred("coq.gref->path",
    In(gref, "GR",
    Out(B.list B.string, "FullPath",
    Read(unit_ctx, "extract the full path (kernel name without final id), each component is a separate list item"))),
  (fun gr _ ~depth h c state -> !: (gr2path gr))),
  DocAbove);

  MLCode(Pred("coq.modpath->path",
    In(modpath, "MP",
    Out(B.list B.string, "FullPath",
    Read(unit_ctx, "extract the full kernel name, each component is a separate list item"))),
  (fun mp _ ~depth h c state -> !: (mp2path mp))),
  DocAbove);

  MLCode(Pred("coq.modtypath->path",
    In(modtypath, "MTP",
    Out(B.list B.string, "FullPath",
    Read(unit_ctx, "extract the full kernel name, each component is a separate list item"))),
  (fun mtyp _ ~depth h c state -> !: (mp2path mtyp))),
  DocAbove);

  MLCode(Pred("coq.modpath->library",
    In(modpath, "MP",
    Out(modpath, "LibraryPath",
    Read(unit_ctx, "extract the enclosing module which can be Required"))),
  (fun mp _ ~depth h c state -> !: ModPath.(MPfile (dp mp)))),
  DocAbove);

  MLCode(Pred("coq.modtypath->library",
    In(modtypath, "MTP",
    Out(modpath, "LibraryPath",
    Read(unit_ctx, "extract the enclosing module which can be Required"))),
  (fun mtyp _ ~depth h c state -> !: ModPath.(MPfile (dp mtyp)))),
  DocAbove);

  MLCode(Pred("coq.term->string",
    CIn(failsafe_term,"T",
    Out(B.string, "S",
    Full(proof_context, {|prints a term T to a string S using Coq's pretty printer
Supported attributes:
- @ppwidth! N (default 80, max line length)
- @ppall! (default: false, prints all details)
- @ppmost! (default: false, prints most details)
- @pplevel! (default: _, prints parentheses to reach that level, 200 = off)
- @holes! (default: false, prints evars as _)|}))),
  (fun t _ ~depth proof_context constraints state ->
     let sigma = get_sigma state in
     let s = string_of_ppcmds proof_context.options (pr_econstr_env proof_context.options proof_context.env sigma t) in
     state, !: s, [])),
  DocAbove);

  MLCode(Pred("coq.term->pp",
    CIn(failsafe_term,"T",
    Out(ppboxes, "B",
    Full(proof_context, {|prints a term T to a pp.t B using Coq's pretty printer"
Supported attributes:
- @ppall! (default: false, prints all details)
- @ppmost! (default: false, prints most details)
- @pplevel! (default: _, prints parentheses to reach that level, 200 = off)
- @holes! (default: false, prints evars as _)|}))),
  (fun t _ ~depth proof_context constraints state ->
     let sigma = get_sigma state in
     let s = Pp.repr @@ pr_econstr_env proof_context.options proof_context.env sigma t in
     state, !: s, [])),
  DocAbove);

  LPDoc "-- Access to Elpi's data --------------------------------------------";

   (* Self modification *)
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
    Full (global, {|
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
A clause that mentions a section variable is automatically discarded
at the end of the section.
Clauses cannot be accumulated inside functors.
Supported attributes:
- @local! (default: false, discard at the end of section or module)
- @global! (default: false, always active, only if Scope is execution-site, discouraged)|} )))),
  (fun scope dbname clauses ~depth ctx _ state ->
     let loc = API.Ast.Loc.initial "(elpi.add_clause)" in
     let dbname = Coq_elpi_utils.string_split_on_char '.' dbname in
     let clauses scope =
      clauses |> CList.rev_map (fun (name,graft,clause) ->
        let levels_to_abstract = err_if_contains_alg_univ ~depth clause in
        let levels_to_abstract_no = Univ.Universe.Set.cardinal levels_to_abstract in
        let rec subst ~depth m t =
          match E.look ~depth t with
          | E.CData c when isuniv c ->
              begin try E.mkBound (Univ.Universe.Map.find (univout c) m)
              with Not_found -> t end
          | E.App(c,x,xs) ->
              E.mkApp c (subst ~depth m x) (List.map (subst ~depth m) xs)
          | E.Cons(x,xs) ->
              E.mkCons (subst ~depth m x) (subst ~depth m xs)
          | E.Lam x ->
              E.mkLam (subst ~depth:(depth+1) m x)
          | E.Builtin(c,xs) ->
              E.mkBuiltin c (List.map (subst ~depth m) xs)
          | E.UnifVar _ -> assert false
          | E.Const _ | E.Nil | E.CData _ -> t
          in
        let clause = 
          let rec bind d map = function
           | [] ->
               subst ~depth:d map
                 (API.Utils.move ~from:depth ~to_:(depth + levels_to_abstract_no) clause)
           | l :: ls ->
             E.mkApp E.Constants.pic (E.mkLam (*   pi x\  *)
                 (bind (d+1) (Univ.Universe.Map.add l d map) ls)) []
           in
             bind depth Univ.Universe.Map.empty
               (Univ.Universe.Set.elements levels_to_abstract)
        in
        let vars = collect_term_variables ~depth clause in
        let clause = U.clause_of_term ?name ?graft ~depth loc clause in
        (dbname,clause,vars,scope)) in
     let local = ctx.options.local = Some true in
     let super_global = ctx.options.local = Some false in
     match scope with
     | B.Unspec | B.Given ExecutionSite ->
         let scope = if super_global then SuperGlobal else if local then Local else Regular in
         State.update clauses_for_later state (fun l ->
           clauses scope @ l), (), []
     | B.Given Library ->
         if local then CErrors.user_err Pp.(str "coq.elpi.accumulate: library scope is incompatible with @local!");
         State.update clauses_for_later state (fun l ->
           clauses Coq_elpi_utils.Global @ l), (), []
     | B.Given CurrentModule ->
          let scope = if local then Local else Regular in
          let f = get_accumulate_to_db () in
          f (clauses scope);
          state, (), []
     )),
  DocAbove);

  MLData argument_mode;

  MLCode(Pred("coq.elpi.add-predicate",
    In(B.string,"Db",
    In(B.unspec B.string,"Indexing",
    In(B.string,"PredName",
    In(B.list (B.pair argument_mode B.string),"Spec",
    Full(global,"Declares a new predicate PredName in the data base Db. Indexing can be left unspecified. Spec gathers a mode and a type for each argument. CAVEAT: types and indexing are strings instead of proper data types; beware parsing errors are fatal"))))),
    (fun dbname indexing predname spec ~depth _ _ state ->
      let dbname = Coq_elpi_utils.string_split_on_char '.' dbname in
      let f = get_accumulate_text_to_db () in
      let indexing =
        match indexing with
        | B.Given str -> ":index ("^str^") "
        | B.Unspec -> "" in
      let spec = spec |> List.map (fun (mode,ty) ->
        let mode =
          match mode with
          | `Input -> "i:"
          | `Output -> "o:" in
        mode ^ "(" ^ ty ^ ")") in
      let spec = String.concat ", " spec in
      let text = indexing ^ "pred " ^ predname ^ " " ^ spec ^ "." in
      f dbname text;
      state, (), []
      )),
  DocAbove);

  MLCode(Pred("coq.elpi.predicate",
    In(B.string,"PredName",
    In(list B.any,"Args",
    Out(B.poly "prop","Pred",
    Full(global,"Pred is the application of PredName to Args")))),
    (fun name args _ ~depth _ _ state ->
      let state, p = Elpi.API.Quotation.term_at ~depth state name in
      match E.look ~depth p with
      | Const c -> state, !: (E.mkAppL c args), []
      | _ -> U.type_error ("predicate name expected, got " ^ name) 
      )),
  DocAbove);

  LPDoc "-- Utils ------------------------------------------------------------";
  ] @
  gref_set_decl @
  B.ocaml_map ~name:"coq.gref.map" gref (module GRMap) @
  B.ocaml_set ~name:"coq.univ.set" univ (module UnivSet) @
  B.ocaml_map ~name:"coq.univ.map" univ (module UnivMap) @
  universe_level_set_decl @
  B.ocaml_map ~name:"coq.univ.variable.map" universe_level_variable (module UnivLevelMap) @
  [
  MLData ppbox;
  MLData ppboxes;
  MLCode(Pred("coq.pp->string",
    In(ppboxes, "B",
    Out(B.string, "S",
    Read(global, {|Prints a pp.t box expression B to a string S
Supported attributes:
- @ppwidth! N (default 80, max line length)|}))),
  (fun box _ ~depth ctx _ _ ->
     !: (string_of_ppcmds ctx.options (Pp.unrepr box))
     )),
  DocAbove)

  ]

;;
