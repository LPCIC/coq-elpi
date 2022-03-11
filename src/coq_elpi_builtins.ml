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
  let ioargC = API.BuiltInPredicate.ioargC
  let ioargC_flex = API.BuiltInPredicate.ioargC_flex
end
module Pred = API.BuiltInPredicate

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
  let print_evar_arguments = !Constrextern.print_evar_arguments in
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
        Constrextern.print_evar_arguments := false;
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
    Constrextern.print_evar_arguments := print_evar_arguments;
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
    Constrextern.print_evar_arguments := print_evar_arguments;
    raise reraise

let pr_econstr_env options env sigma t =
  with_pp_options options.pp (fun () ->
    let expr = Constrextern.extern_constr env sigma t in
    let expr =
      let rec aux () ({ CAst.v } as orig) = match v with
      | Constrexpr.CEvar _ -> CAst.make @@ Constrexpr.CHole(None,Namegen.IntroAnonymous,None)
      | _ -> Constrexpr_ops.map_constr_expr_with_binders (fun _ () -> ()) aux () orig in
      if options.hoas_holes = Some Heuristic then aux () expr else expr in
    Ppconstr.pr_constr_expr_n env sigma options.pplevel expr)

let tactic_mode = ref false
let on_global_state api thunk = (); (fun state ->
  if !tactic_mode then
    Coq_elpi_utils.err Pp.(strbrk ("API " ^ api ^ " cannot be used in tactics"));
  let state, result, gls = thunk state in
  Coq_elpi_HOAS.grab_global_env state, result, gls)

(* This is for stuff that is not monotonic in the env, eg section closing *)
let on_global_state_does_rewind_env api thunk = (); (fun state ->
  if !tactic_mode then
    Coq_elpi_utils.err Pp.(strbrk ("API " ^ api ^ " cannot be used in tactics"));
  let state, result, gls = thunk state in
  Coq_elpi_HOAS.grab_global_env_drop_univs state, result, gls)

let warn_if_contains_univ_levels ~depth t =
  let global_univs = UGraph.domain (Environ.universes (Global.env ())) in
  let is_global u =
    match Univ.Universe.level u with
    | None -> true
    | Some l -> Univ.Level.Set.mem l global_univs in
  let rec aux ~depth acc t =
    match E.look ~depth t with
    | E.CData c when isuniv c -> let u = univout c in if is_global u then acc else u :: acc
    | x -> Coq_elpi_utils.fold_elpi_term aux acc ~depth x
  in
  let univs = aux ~depth [] t in
  if univs <> [] then
    err Pp.(strbrk "The hypothetical clause contains terms of type univ which are not global, you should abstract them out or replace them by global ones: " ++
            prlist_with_sep spc Univ.Universe.pr univs)
;;

let bool = B.bool
let int = B.int
let list = B.list
let pair = B.pair
let option = B.option

let constraint_leq u1 u2 =
  let open UnivProblem in
  ULe (u1, u2)

let constraint_eq u1 u2 =
  let open UnivProblem in
  ULe (u1, u2)

let add_universe_constraint state c =
  let open UnivProblem in
  try add_constraints state (Set.singleton c)
  with
  | Univ.UniverseInconsistency p ->
      Feedback.msg_debug
        (Univ.explain_universe_inconsistency
           UnivNames.(pr_with_global_universes empty_binders) p);
      raise Pred.No_clause
  | Evd.UniversesDiffer | UState.UniversesDiffer ->
      Feedback.msg_debug Pp.(str"UniversesDiffer");
      raise Pred.No_clause

let mk_fresh_univ state = new_univ state

let mk_algebraic_super x = Univ.super x
let mk_algebraic_max x y = Univ.Universe.sup x y

(* I don't want the user to even know that algebraic universes exist *)
let purge_1_algebraic_universe state u =
  if Univ.Universe.is_level u then state, u
  else
    let state, v = mk_fresh_univ state in
    add_universe_constraint state (constraint_leq u v), v

let purge_algebraic_univs state t =
  let sigma = get_sigma state in
  (* no map_fold iterator :-/ *)
  let state = ref state in
  let rec aux t =
    match EConstr.kind sigma t with
    | Constr.Sort s -> begin
        match EConstr.ESorts.kind sigma s with
        | Sorts.Type u ->
            let new_state, v = purge_1_algebraic_universe !state u in
            state := new_state;
            EConstr.mkType v
        | _ -> EConstr.map sigma aux t
        end
    | _ -> EConstr.map sigma aux t in
  let t = aux t in
  !state, t

let univ_super state u v =
  let state, u =
    if Univ.Universe.is_level u then state, u
    else
      let state, w = mk_fresh_univ state in
      add_universe_constraint state (constraint_leq u w), w in
    add_universe_constraint state (constraint_leq (mk_algebraic_super u) v)

let univ_max state u1 u2 =
  let state, v = mk_fresh_univ state in
  let state =
    add_universe_constraint state (constraint_leq (mk_algebraic_max u1 u2) v) in
  state, v

let constr2lp ~depth hyps constraints state t =
  let state, t = purge_algebraic_univs state t in
  constr2lp ~depth hyps constraints state t

let constr2lp_closed ~depth hyps constraints state t =
  let state, t = purge_algebraic_univs state t in
  constr2lp_closed ~depth hyps constraints state t

let constr2lp_closed_ground ~depth hyps constraints state t =
  let state, t = purge_algebraic_univs state t in
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

let univ = { univ with
  Conv.readback = (fun ~depth state x ->
    let state, u, gl = univ.Conv.readback ~depth state x in
    let state, u = purge_1_algebraic_universe state u in
    state, u, gl);
  embed = (fun ~depth state x ->
    let state, x = purge_1_algebraic_universe state x in
    let state, u, gl = univ.Conv.embed ~depth state x in
    state, u, gl);
}

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
    let state, args, gls2 = API.Utils.map_acc (Coq_elpi_arg_HOAS.in_coq_arg ~depth ctx csts) state raw_args in
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

type located =
  | LocGref of Names.GlobRef.t
  | LocModule of Names.ModPath.t
  | LocModuleType of Names.ModPath.t
  | LocAbbreviation of Globnames.syndef_name

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
    K("cs-sort","",A(universe,N),
      B (fun s -> Sort_cs (Sorts.family s)),
      MS (fun ~ok ~ko p state -> match p with
        | Sort_cs Sorts.InSet -> ok Sorts.set state
        | Sort_cs Sorts.InProp -> ok Sorts.prop state
        | Sort_cs Sorts.InType ->
              let state, u = mk_fresh_univ state in
              ok (Sorts.sort_of_univ u) state
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

let tc_instance = let open Conv in let open API.AlgebraicData in let open Typeclasses in declare {
  ty = TyName "tc-instance";
  doc = "Type class instance with priority";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("tc-instance","",A(gref,A(int,N)),
      B (fun g p -> nYI "lp2instance"),
      M (fun ~ok ~ko i ->
          ok (instance_impl i) (Option.default 0 (hint_priority i))));
]} |> CConv.(!<)

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
 clause _ "foo" (before "bar") (pi x y z\ foo x y :- bar x z, baz z y)
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
  let f = ref (fun _ _ _ ~scope:_ -> assert false) in
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

let warning = CWarnings.create ~name:"lib" ~category:"elpi" Pp.str

let if_keep x f =
  match x with
  | Pred.Discard -> None
  | Pred.Keep -> Some (f ())

let if_keep_acc x state f =
  match x with
  | Pred.Discard -> state, None
  | Pred.Keep ->
       let state, x = f state in
       state, Some x

let version_parser version =
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
  let rec mp2sl = function
    | MPfile dp -> CList.rev_map Id.to_string (DirPath.repr dp)
    | MPbound id ->
        let _,id,dp = MBId.repr id in
        mp2sl (MPfile dp) @ [ Id.to_string id ]
    | MPdot (mp,lbl) -> mp2sl mp @ [Label.to_string lbl] in
  mp2sl x

let gr2path gr =
  match gr with
  | Names.GlobRef.VarRef v -> mp2path (Safe_typing.current_modpath (Global.safe_env ()))
  | Names.GlobRef.ConstRef c -> mp2path @@ Constant.modpath c
  | Names.GlobRef.IndRef (i,0) -> mp2path @@ MutInd.modpath i
  | Names.GlobRef.ConstructRef ((i,0),j) -> mp2path @@ MutInd.modpath i
  | Names.GlobRef.IndRef _  | Names.GlobRef.ConstructRef _ ->
        nYI "mutual inductive (make-derived...)"

let gr2id state gr =
  let open GlobRef in
  match gr with
  | VarRef v ->
      (Id.to_string v)
  | ConstRef c ->
      (Id.to_string (Label.to_id (Constant.label c)))
  | IndRef (i,0) ->
      let open Declarations in
      let env = get_global_env state in
      let { mind_packets } = Environ.lookup_mind i env in
      (Id.to_string (mind_packets.(0).mind_typename))
  | ConstructRef ((i,0),j) ->
      let open Declarations in
      let env = get_global_env state in
      let { mind_packets } = Environ.lookup_mind i env in
      (Id.to_string (mind_packets.(0).mind_consnames.(j-1)))
  | IndRef _  | ConstructRef _ ->
        nYI "mutual inductive (make-derived...)"
        
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
    ~category:"elpi.deprecated"
    Pp.(fun () ->
         strbrk ("elpi: Using coq.env.add-const for declaring axioms or " ^
           "section variables is deprecated. Use coq.env.add-axiom or " ^
           "coq.env.add-section-variable instead"))

let add_axiom_or_variable api id sigma ty local inline =
  let used = EConstr.universes_of_constr sigma ty in
  let sigma = Evd.restrict_universe_context sigma used in
  let uentry = Evd.univ_entry ~poly:false sigma in
  let kind = Decls.Logical in
  let impargs = [] in
  let variable = CAst.(make @@ Id.of_string id) in
  if not (is_ground sigma ty) then
    err Pp.(str"coq.env.add-const: the type must be ground. Did you forge to call coq.typecheck-indt-decl?");
  let gr, _ =
    if local then begin
      ComAssumption.declare_variable false ~kind (EConstr.to_constr sigma ty) uentry impargs Glob_term.Explicit variable;
      GlobRef.VarRef(Id.of_string id), Univ.Instance.empty
    end else
      ComAssumption.declare_axiom false ~local:Locality.ImportDefaultBehavior ~poly:false ~kind (EConstr.to_constr sigma ty)
        uentry impargs inline
        variable
  in
  gr
  ;;

type tac_abbrev = {
  abbrev_name : qualified_name;
  tac_name : qualified_name;
  tac_fixed_args : Coq_elpi_arg_HOAS.Tac.glob list;
}


let rec gbpmp = fun f -> function
  | [x] -> Pcoq.Rule.next Pcoq.Rule.stop (Pcoq.Symbol.token (Tok.PIDENT(Some x))), (fun a _ -> f a)
  | x :: xs ->
      let r, f = gbpmp f xs in
      Pcoq.Rule.next r (Pcoq.Symbol.token (Tok.PFIELD (Some x))), (fun a _ -> f a)
  | [] -> assert false

let cache_abbrev_for_tac (_, { abbrev_name; tac_name = tacname; tac_fixed_args = more_args }) =
  let action args loc =
  let open Ltac_plugin in
  let tac =
    let open Tacexpr in
    let elpi_tac = {
      mltac_plugin = "elpi_plugin";
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
        | Constrexpr.CEvar _ -> CAst.make @@ Constrexpr.CHole(None,Namegen.IntroAnonymous,None)
        | _ -> Constrexpr_ops.map_constr_expr_with_binders (fun _ () -> ()) aux () orig in
        Coq_elpi_arg_HOAS.Tac.Term (aux () expr)
      | _ -> assert false)  in
    let tacname = loc, tacname in
    let tacname = Genarg.in_gen (Genarg.rawwit Coq_elpi_arg_syntax.wit_qualified_name) tacname in
    let args = args |> List.map (fun (arg,_) -> Coq_elpi_arg_HOAS.Tac.Term(arg)) in
    let args = Genarg.in_gen (Genarg.rawwit (Genarg.wit_list Coq_elpi_arg_syntax.wit_elpi_tactic_arg)) (more_args @ args) in
    (TacML (elpi_tac_entry, [TacGeneric(None, tacname); TacGeneric(None, args)])) in
  CAst.make @@ Constrexpr.CHole (None, Namegen.IntroAnonymous, Some (Genarg.in_gen (Genarg.rawwit Tacarg.wit_tactic) (CAst.make tac))) in
  let rule, action = gbpmp (Obj.magic action) (List.rev abbrev_name) in
  Pcoq.grammar_extend Pcoq.Constr.term (Pcoq.Fresh
    (Gramlib.Gramext.Before "10",
    [ (None, None, [ Pcoq.Production.make
      (Pcoq.Rule.next (Obj.magic rule) (Pcoq.Symbol.list0 (Pcoq.Symbol.nterm Pcoq.Constr.arg)))
      (Obj.magic action)
    ])]))

let subst_abbrev_for_tac (subst, { abbrev_name; tac_name; tac_fixed_args }) = {
  abbrev_name;
  tac_name;
  tac_fixed_args = List.map (Coq_elpi_arg_HOAS.Tac.subst subst) tac_fixed_args
}

let inAbbreviationForTactic : tac_abbrev -> Libobject.obj =
  Libobject.declare_object @@ Libobject.global_object_nodischarge "ELPI-EXPORTED-TAC-ABBREV"
      ~cache:cache_abbrev_for_tac ~subst:(Some subst_abbrev_for_tac)

let cache_tac_abbrev (q,qualid) = cache_abbrev_for_tac (q,{
  abbrev_name = qualid;
  tac_name = qualid;
  tac_fixed_args = [];
})


let cache_goption_declaration (_, (depr,key,value)) =
  let open Goptions in
  match value with
  | BoolValue x ->
      let _ : unit -> bool = Goptions.declare_bool_option_and_ref ~key ~value:x ~depr in
      ()
  | IntValue x ->
    let _ : unit -> int option = Goptions.declare_intopt_option_and_ref ~key ~depr in
    Goptions.set_int_option_value key x;
    ()
  | StringOptValue x ->
    let _ : unit -> string option = Goptions.declare_stringopt_option_and_ref ~key ~depr in
    Option.iter (Goptions.set_string_option_value key) x;
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
  let open Constrexpr in let open Libnames in let open Nametab in
  CAst.make @@ CMident (qualid_of_dirpath (dirpath_of_module x))

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
  LPCode {|
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% builtins %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% This section contains the API to access Coq
% The marker *E* means *experimental*, i.e. use at your own risk, it may change
% substantially or even disappear in future versions.
|};

  LPDoc "-- Misc ---------------------------------------------------------";

  MLCode(Pred("coq.say",
    VariadicIn(unit_ctx, !> B.any, "Prints an info message"),
  (fun args ~depth _hyps _constraints state ->
     let pp = pp ~depth in
     Feedback.msg_notice Pp.(str (pp2string (P.list ~boxed:true pp " ") args));
     state, ())),
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
  (fun category name args ~depth _hyps _constraints state ->
     let warning = CWarnings.create ~name ~category Pp.str in
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
     if coq_warning_cache category name loc txt then warning ?loc txt;
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
      let major, minor, patch = version_parser version in
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
    Full(global, "reads the type Ty of a global reference."))),
  (fun gr _ ~depth _ _ state ->
    let state, ty = type_of_global state gr in
    state, !:ty, [])),
  DocAbove);

  MLCode(Pred("coq.env.indt",
    In(inductive, "reference to the inductive type",
    Out(bool, "tt if the type is inductive (ff for co-inductive)",
    Out(int,  "number of parameters",
    Out(int,  "number of parameters that are uniform (<= parameters)",
    COut(closed_ground_term, "type of the inductive type constructor including parameters",
    Out(list constructor, "list of constructor names",
    COut(!>> B.list closed_ground_term, "list of the types of the constructors (type of KNames) including parameters",
    Full(global, "reads the inductive type declaration for the environment")))))))),
  (fun i _ _ _ arity knames ktypes ~depth { env } _ state ->
     let open Declarations in
     let mind, indbo as ind = lookup_inductive env i in
     let co  = mind.mind_finite <> Declarations.CoFinite in
     let lno = mind.mind_nparams in
     let luno = mind.mind_nparams_rec in
     let arity = if_keep arity (fun () ->
       Inductive.type_of_inductive (ind,Univ.Instance.empty)
       |> EConstr.of_constr) in
     let knames = if_keep knames (fun () ->
       CList.(init Declarations.(indbo.mind_nb_constant + indbo.mind_nb_args)
           (fun k -> i,k+1))) in
     let ktypes = if_keep ktypes (fun () ->
       Inductive.type_of_constructors (i,Univ.Instance.empty) ind
       |> CArray.map_to_list EConstr.of_constr) in
     state, !: co +! lno +! luno +? arity +? knames +? ktypes, [])),
  DocNext);

  MLCode(Pred("coq.env.indt-decl",
    In(inductive, "reference to the inductive type",
    COut(indt_decl_out,"HOAS description of the inductive type",
    Full(global,"reads the inductive type declaration for the environment"))),
  (fun i _ ~depth { env } _ state  ->
     let mind, indbo = lookup_inductive env i in
     let knames = CList.(init Declarations.(indbo.mind_nb_constant + indbo.mind_nb_args) (fun k -> GlobRef.ConstructRef(i,k+1))) in
     let k_impls = List.map (fun x -> Impargs.extract_impargs_data (Impargs.implicits_of_global x)) knames in
     let hd x = match x with [] -> [] | (_,x) :: _ -> List.map implicit_kind_of_status x in
     let k_impls = List.map hd k_impls in
     let i_impls = Impargs.extract_impargs_data @@ Impargs.implicits_of_global (GlobRef.IndRef i) in
     let i_impls = hd i_impls in
     state, !: (fst i, (mind,indbo), (i_impls,k_impls)), [])),
  DocNext);

  MLCode(Pred("coq.env.indc",
    In(constructor, "GR",
    Out(int, "ParamNo",
    Out(int, "UnifParamNo",
    Out(int, "Kno",
    COut(closed_ground_term,"Ty",
    Full (global, "reads the type Ty of an inductive constructor GR, as well as "^
          "the number of parameters ParamNo and uniform parameters "^
          "UnifParamNo and the number of the constructor Kno (0 based)")))))),
  (fun (i,k as kon) _ _ _ ty ~depth { env } _ state ->
    let open Declarations in
    let mind, indbo as ind = Inductive.lookup_mind_specif env i in
    let lno = mind.mind_nparams in
    let luno = mind.mind_nparams_rec in
    let ty = if_keep ty (fun () ->
      Inductive.type_of_constructor (kon,Univ.Instance.empty) ind
      |> EConstr.of_constr) in
    state, !: lno +! luno +! (k-1) +? ty, [])),
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
      | (Sorts.InSet | Sorts.InType) -> ()
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
  
  MLCode(Pred("coq.env.const",
    In(constant,  "GR",
    COut(!>> option closed_ground_term, "Bo",
    COut(closed_ground_term, "Ty",
    Full (global, "reads the type Ty and the body Bo of constant GR. "^
          "Opaque constants have Bo = none.")))),
  (fun c bo ty ~depth {env} _ state ->
    match c with
    | Constant c ->
        let state, ty = if_keep_acc ty state (fun s -> type_of_global s (GlobRef.ConstRef c)) in
        let state, bo = if_keep_acc bo state (fun state ->
          if Declareops.is_opaque (Environ.lookup_constant c env)
          then state, None
          else
            body_of_constant state c) in
        state, ?: bo +? ty, []
    | Variable v ->
        let state, ty = if_keep_acc ty state (fun s -> type_of_global s (GlobRef.VarRef v)) in
        let bo = if_keep bo (fun () ->
          match Environ.lookup_named v env with
          | Context.Named.Declaration.LocalDef(_,bo,_) -> Some (bo |> EConstr.of_constr)
          | Context.Named.Declaration.LocalAssum _ -> None) in
        state, ?: bo +? ty, [])),
  DocAbove);

  MLCode(Pred("coq.env.const-body",
    In(constant,  "GR",
    COut(!>> option closed_ground_term, "Bo",
    Full (global, "reads the body of a constant, even if it is opaque. "^
          "If such body is none, then the constant is a true axiom"))),
  (fun c _ ~depth {env} _ state ->
    match c with
    | Constant c ->
         let state, bo = body_of_constant state c in
         state, !: bo, []
    | Variable v ->
         state, !: begin
         match Environ.lookup_named v env with
         | Context.Named.Declaration.LocalDef(_,bo,_) -> Some (bo |> EConstr.of_constr)
         | Context.Named.Declaration.LocalAssum _ -> None
         end, [])),
  DocAbove);

  MLCode(Pred("coq.env.primitive?",
    In(constant,  "GR",
    Read (global,"tests if GR is a primitive constant (like uin63 addition)")),
  (fun c ~depth {env} _ state ->
    match c with
    | Constant c ->
        if Environ.is_primitive env c then ()
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

  MLCode(Pred("coq.env.module",
    In(modpath, "MP",
    Out(list gref, "Contents",
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
     let { section } = mk_coq_context ~options:default_options state in
     !: (section |> List.map (fun x -> Variable x)) )),
  DocAbove);

  MLCode(Pred("coq.env.current-path",
    Out(list B.string, "Path",
    Read(unit_ctx, "lists the current module path")),
  (fun _ ~depth _ _ state -> !: (mp2path (Safe_typing.current_modpath (Global.safe_env ()))))),
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

  LPDoc ("Note: universe constraints are taken from ELPI's constraints "^
         "store. Use coq.univ-* in order to add constraints (or any higher "^
         "level facility as coq.typecheck)");

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
- @using! (default: section variables actually used)|})))))),
  (fun id body types opaque _ ~depth {options} _ -> on_global_state "coq.env.add-const" (fun state ->
    let local = options.local = Some true in
    let sigma = get_sigma state in
     match body with
     | B.Unspec -> (* axiom *)
       begin match types with
       | B.Unspec ->
         err Pp.(str "coq.env.add-const: both Type and Body are unspecified")
       | B.Given ty ->
       warn_deprecated_add_axiom ();
       let gr = add_axiom_or_variable "coq.env.add-const" id sigma ty local options.inline in
       state, !: (global_constant_of_globref gr), []
     end
    | B.Given body ->
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
       let udecl = UState.default_univ_decl in
       let kind = Decls.(IsDefinition Definition) in
       let scope = if local
         then Locality.Discharge
         else Locality.(Global ImportDefaultBehavior) in
       let using = Option.map  Proof_using.(fun s ->
          let types = Option.List.cons types [] in
          let using = using_from_string s in
          definition_using (get_global_env state) sigma ~using ~terms:types)
         options.using in
       let cinfo = Declare.CInfo.make ?using ~name:(Id.of_string id) ~typ:types ~impargs:[] () in
       let info = Declare.Info.make ~scope ~kind ~poly:false ~udecl () in
       let gr = Declare.declare_definition ~cinfo ~info ~opaque ~body sigma in
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
- @using! (default: section variables actually used)
- @inline! (default: no inlining)
- @inline-at! N (default: no inlining)
|})))),
  (fun id ty _ ~depth {options} _ -> on_global_state "coq.env.add-axiom" (fun state ->
     let sigma = get_sigma state in
     let gr = add_axiom_or_variable "coq.env.add-axiom" id sigma ty false options.inline in
     state, !: (global_constant_of_globref gr), []))),
  DocAbove);

  MLCode(Pred("coq.env.add-section-variable",
    In(id,   "Name",
    CIn(closed_ground_term, "Ty",
    Out(constant, "C",
    Full (global, {|Declare a new section variable: C gets a constant derived from Name
and the current module|})))),
  (fun id ty _ ~depth {options} _ -> on_global_state "coq.env.add-section-variable" (fun state ->
     let sigma = get_sigma state in
     let gr = add_axiom_or_variable "coq.env.add-section-variable" id sigma ty true options.inline in
     state, !: (global_constant_of_globref gr), []))),
  DocAbove);

  MLCode(Pred("coq.env.add-indt",
    CIn(indt_decl_in, "Decl",
    Out(inductive, "I",
    Full(global, {|Declares an inductive type.
Supported attributes:
- @primitive! (default: false, makes records primitive)|}))),
  (fun (me, uctx, record_info, ind_impls) _ ~depth env _ -> on_global_state "coq.env.add-indt" (fun state ->
     let sigma = get_sigma state in
     if not (is_mutual_inductive_entry_ground me sigma) then
       err Pp.(str"coq.env.add-indt: the inductive type declaration must be ground. Did you forge to call coq.typecheck-indt-decl?");
     let primitive_expected = match record_info with Some(p, _) -> p | _ -> false in
     let ubinders = UState.Monomorphic_entry uctx, UnivNames.empty_binders in
     let () = DeclareUctx.declare_universe_context ~poly:false uctx in
     let mind =
       DeclareInd.declare_mutual_inductive_with_eliminations ~primitive_expected me ubinders ind_impls in
     let ind = mind, 0 in
     begin match record_info with
     | None -> () (* regular inductive *)
     | Some (primitive,field_specs) -> (* record: projection... *)
         let names, flags =
           List.(split (map (fun { name; is_coercion; is_canonical } -> name,
               { Record.Internal.pf_subclass = is_coercion ; pf_canonical = is_canonical })
             field_specs)) in
         let is_implicit = List.map (fun _ -> []) names in
         let open Entries in
         let k_ty = List.(hd (hd me.mind_entry_inds).mind_entry_lc) in
         let fields_as_relctx = Term.prod_assum k_ty in
         let projections =
           Record.Internal.declare_projections ind ~kind:Decls.Definition
             (Entries.Monomorphic_entry, UnivNames.empty_binders)
             (Names.Id.of_string "record")
             flags is_implicit fields_as_relctx
         in
         let struc = Structures.Structure.make (Global.env()) ind projections in
         Record.Internal.declare_structure_entry struc;
     end;
     state, !: ind, []))),
  DocAbove);

  LPDoc "Interactive module construction";

  MLData module_inline_default;

  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.begin-module-functor",
    In(id, "The name of the functor",
    In(option modtypath, "Its module type",
    In(list (pair id modtypath), "Parameters of the functor",
    Full(unit_ctx, "Starts a functor *E*")))),
  (fun name mp binders_ast ~depth _ _ -> on_global_state "coq.env.begin-module-functor" (fun state ->
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
     let _mp = Declaremods.start_module None id binders_ast ty in
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
  (fun _ ~depth _ _ -> on_global_state "coq.env.end-module" (fun state ->
     let mp = Declaremods.end_module () in
     state, !: mp, []))),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.begin-module-type-functor",
    In(id, "The name of the functor",
    In(list (pair id modtypath), "The parameters of the functor",
    Full(unit_ctx,"Starts a module type functor *E*"))),
  (fun id binders_ast ~depth _ _ -> on_global_state "coq.env.begin-module-type-functor" (fun state ->
     if Global.sections_are_opened () then
       err Pp.(str"This elpi code cannot be run within a section since it opens a module");
     let id = Id.of_string id in
     let binders_ast =
       List.map (fun (id, mty) ->
         [CAst.make (Id.of_string id)], (module_ast_of_modtypath mty))
         binders_ast in
     let _mp = Declaremods.start_modtype id binders_ast [] in
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
  (fun _ ~depth _ _ -> on_global_state "coq.env.end-module-type" (fun state ->
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
  (fun name mp f arguments inline _ ~depth _ _ -> on_global_state "coq.env.apply-module-functor" (fun state ->
     if Global.sections_are_opened () then
       err Pp.(str"This elpi code cannot be run within a section since it defines a module");
     let ty =
       match mp with
       | None -> Declaremods.Check []
       | Some mp -> Declaremods.(Enforce (module_ast_of_modtypath mp)) in
     let id = Id.of_string name in
     let f = module_ast_of_modpath f in
     let mexpr_ast_args = List.map module_ast_of_modpath arguments in
      let mexpr_ast =
         List.fold_left (fun hd arg -> CAst.make (Constrexpr.CMapply(hd,arg))) f mexpr_ast_args in
      let mp = Declaremods.declare_module id [] ty [mexpr_ast,inline] in
      state, !: mp, []))),
  DocNext);
  
  MLCode(Pred("coq.env.apply-module-type-functor",
    In(id, "The name of the new module type",
    In(modtypath, "The functor",
    In(list modpath, "Its arguments",
    In(module_inline_default, "Arguments inlining",
    Out(modtypath, "The modtypath of the new module type",
    Full(unit_ctx, "Applies a type functor *E*")))))),
  (fun name f arguments inline _ ~depth _ _ -> on_global_state "coq.env.apply-module-type-functor" (fun state ->
     if Global.sections_are_opened () then
       err Pp.(str"This elpi code cannot be run within a section since it defines a module");
     let id = Id.of_string name in
     let f,_ = module_ast_of_modtypath f in
     let mexpr_ast_args = List.map module_ast_of_modpath arguments in
     let mexpr_ast =
        List.fold_left (fun hd arg -> CAst.make (Constrexpr.CMapply(hd,arg))) f mexpr_ast_args in
     let mp = Declaremods.declare_modtype id [] [] [mexpr_ast,inline] in
      state, !: mp, []))),
  DocNext);

  (* XXX When Coq's API allows it, call vernacentries directly *)
  MLCode(Pred("coq.env.include-module",
    In(modpath, "ModPath",
    In(module_inline_default, "Inline",
    Full(unit_ctx, "is like the vernacular Include, Inline can be omitted *E*"))),
  (fun mp inline ~depth _ _ -> on_global_state "coq.env.include-module" (fun state ->
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
  (fun mp inline  ~depth _ _ -> on_global_state "coq.env.include-module-type" (fun state ->
     let fpath = Nametab.path_of_modtype mp in
     let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
     let i = CAst.make tname, inline in
     Declaremods.declare_include [i];
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.env.import-module",
    In(modpath, "ModPath",
    Full(unit_ctx, "is like the vernacular Import *E*")),
  (fun mp ~depth _ _ -> on_global_state "coq.env.import-module" (fun state ->
     Declaremods.import_module ~export:false Libobject.unfiltered mp;
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.env.export-module",
    In(modpath, "ModPath",
    Full(unit_ctx, "is like the vernacular Export *E*")),
  (fun mp ~depth _ _ -> on_global_state "coq.env.export-module" (fun state ->
     Declaremods.import_module ~export:true Libobject.unfiltered mp;
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
  (fun id ~depth _ _ -> on_global_state "coq.env.begin-section" (fun state ->
     Lib.open_section (Names.Id.of_string id);
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.env.end-section",
    Full(unit_ctx, "end the current section *E*"),
  (fun ~depth _ _ -> on_global_state_does_rewind_env "coq.env.end-section" (fun state ->
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

  LPDoc "-- Universes --------------------------------------------------------";

  MLData univ;

  MLData universe;

  MLCode(Pred("coq.univ.print",
    Read(unit_ctx,  "prints the set of universe constraints"),
  (fun ~depth _ _ state ->
    let sigma = get_sigma state in
    let uc = Evd.evar_universe_context sigma in
    let uc = Termops.pr_evar_universe_context uc in
    Feedback.msg_notice Pp.(str "Universe constraints: " ++ uc);
    ())),
  DocAbove);

  MLCode(Pred("coq.univ.leq",
    In(univ, "U1",
    In(univ, "U2",
    Full(unit_ctx, "constrains U1 <= U2"))),
  (fun u1 u2 ~depth _ _ state ->
    add_universe_constraint state (constraint_leq u1 u2), (),[])),
  DocAbove);

  MLCode(Pred("coq.univ.eq",
    In(univ, "U1",
    In(univ, "U2",
    Full(unit_ctx, "constrains U1 = U2"))),
  (fun u1 u2 ~depth _ _ state ->
    add_universe_constraint state (constraint_eq u1 u2),(), [])),
  DocAbove);

  MLCode(Pred("coq.univ.new",
    In(B.unspec (list id), "Names",
    Out(univ, "U",
    Full(unit_ctx, "fresh universe *E*"))),
  (fun nl _ ~depth _ _ state ->
     if not (nl = B.Unspec || nl = B.Given []) then nYI "named universes";
     let state, u = mk_fresh_univ state in
     state, !: u, [])),
  DocAbove);

  MLCode(Pred("coq.univ.sup",
    In(univ, "U1",
    In(univ, "U2",
    Full(unit_ctx,  "constrains U2 = U1 + 1"))),
  (fun u1 u2 ~depth _ _ state ->
    univ_super state u1 u2, (), [])),
  DocAbove);

  MLCode(Pred("coq.univ.max",
    In(univ, "U1",
    In(univ, "U2",
    Out(univ, "U3",
    Full(unit_ctx,  "constrains U3 = max U1 U2")))),
  (fun u1 u2 _ ~depth _ _ state ->
    let state, u3 = univ_max state u1 u2 in
    state, !: u3, [])),
  DocAbove);

  LPDoc "Very low level, don't use";

  MLCode(Pred("coq.univ.algebraic-max",
    In(univ, "U1",
    In(univ, "U2",
    Out(univ, "U3",
    Full(unit_ctx,  "constrains U3 = Max(U1,U2) *E*")))),
  (fun u1 u2 _ ~depth _ _ state ->
    state, !: (mk_algebraic_max u1 u2), [])),
  DocAbove);

  MLCode(Pred("coq.univ.algebraic-sup",
    In(univ, "U1",
    Out(univ, "U2",
    Full(unit_ctx,  "constrains U2 = Sup(U1) *E*"))),
  (fun u1 _ ~depth _ _ state ->
    state, !: (mk_algebraic_super u1), [])),
  DocAbove);

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

  MLCode(Pred("coq.float64->float",
    In(Coq_elpi_utils.float64,"F64",
    Out(B.float,"F",
    Easy "Transforms a primitive float on 64 bits to an elpi one. Currently, it should not fail.")),
    (fun f _ ~depth:_ ->
       let s = Float64.to_hex_string f in
       try !: (float_of_string s)
       with Failure _ -> raise No_clause)),
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
  (fun gr ~depth { options } _ -> on_global_state "coq.CS.declare-instance" (fun state ->
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
  (fun gr ~depth { options } _ -> on_global_state "coq.TC.declare-class" (fun state ->
     Record.declare_existing_class gr;
     state, (), []))),
  DocAbove);

  MLData tc_instance;
 
  MLCode(Pred("coq.TC.declare-instance",
    In(gref, "GR",
    In(int,  "Priority",
    Full(global, {|Declare GR as a Global type class instance with Priority.
Supported attributes:
- @global! (default: true)|}))),
  (fun gr priority ~depth { options } _ -> on_global_state "coq.TC.declare-instance" (fun state ->
     let global = if options.local = Some false then Hints.SuperGlobal else Hints.Local in
     let hint_priority = Some priority in
     let qualid =
       Nametab.shortest_qualid_of_global Names.Id.Set.empty gr in
     Classes.existing_instance global qualid
          (Some { Hints.empty_hint_info with Typeclasses.hint_priority });
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.TC.db",
    Out(list tc_instance, "Db",
    Easy "reads all instances"),
  (fun _ ~depth -> !: (Typeclasses.all_instances ()))),
  DocAbove);

  MLCode(Pred("coq.TC.db-for",
    In(gref, "GR",
    Out(list tc_instance, "Db",
    Read(global,"reads all instances of the given class GR"))),
  (fun gr _ ~depth { env } _ state ->
    !: (Typeclasses.instances env (get_sigma state) gr))),
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
- @global! (default: false)|})),
  (fun (gr, _, source, target) ~depth { options } _ -> on_global_state "coq.coercion.declare" (fun state ->
     let local = options.local <> Some false in
     let poly = false in
     begin match source, target with
     | B.Given source, B.Given target ->
        let source = ComCoercion.class_of_global source in
        ComCoercion.try_add_new_coercion_with_target gr ~local ~poly ~source ~target
     | _, _ ->
        ComCoercion.try_add_new_coercion gr ~local ~poly
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
  (fun gr (db,_) mode ~depth:_ {options} _ -> on_global_state "coq.hints.add-mode" (fun state ->
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
  (fun c (db,_) opaque ~depth:_ {options} _ -> on_global_state "coq.hints.set-opaque" (fun state ->
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
(fun gr (db,_) priority pattern ~depth:_ {env;options} _ -> on_global_state "coq.hints.add-resolve" (fun state ->
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
  (fun gref imps ~depth {options} _ -> on_global_state "coq.arguments.set-implicit" (fun state ->
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
  (fun gref ~depth { options } _ -> on_global_state "coq.arguments.set-default-implicit" (fun state ->
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
  (fun gref names ~depth { options } _ -> on_global_state "coq.arguments.set-name" (fun state ->
     let local = options.local <> Some false in
     let names = names |> List.map (function
       | None -> Names.Name.Anonymous
       | Some x -> Names.(Name.Name (Id.of_string x))) in
     Arguments_renaming.rename_arguments local gref names;
     state, (), []))),
  DocAbove);

  MLCode(Pred("coq.arguments.scope",
    In(gref,"GR",
    Out(list (option id),"Scopes",
    Easy "reads the notation scope of the arguments of a global reference. See also the %scope modifier for the Arguments command")),
  (fun gref _ ~depth -> !: (CNotation.find_arguments_scope gref))),
  DocAbove);

  MLCode(Pred("coq.arguments.set-scope",
    In(gref,"GR",
    In(list (option id),"Scopes",
    Full(global,
{|sets the notation scope of the arguments of a global reference.
Scope can be a scope name or its delimiter.
See also the %scope modifier for the Arguments command.
Supported attributes:
- @global! (default: false)|}))),
  (fun gref scopes ~depth { options } _ -> on_global_state "coq.arguments.set-scope" (fun state ->
     let local = options.local <> Some false in
     let scopes = scopes |> List.map (Option.map (fun k ->
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
  (fun gref strategy ~depth { options } _ -> on_global_state "coq.arguments.set-simplification" (fun state ->
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
      try Nametab.locate_syndef qualid
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
  (fun name nargs term onlyparsing _ ~depth { env; options } _ -> on_global_state "coq.notation.add-abbreviation" (fun state ->
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
               (id, ((Constrexpr.InConstrEntrySomeLevel,(None,[])),Notation_term.NtnTypeConstr)) :: vars in
             let env = EConstr.push_rel (Context.Rel.Declaration.LocalAssum(name,ty)) env in
             aux vars nenv env (n-1) t
         | _ ->
             API.Utils.type_error
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
     Syntax_def.declare_syntactic_definition ~local ~onlyparsing options.deprecation name (vars,pat);
     let qname = Libnames.qualid_of_string (Id.to_string name) in
     match Nametab.locate_extended qname with
     | Globnames.TrueGlobal _ -> assert false
     | Globnames.SynDef sd -> state, !: sd, []))),
  DocAbove);

  MLCode(Pred("coq.notation.abbreviation",
    In(abbreviation,"Abbreviation",
    In(B.list (B.poly "term"),"Args",
    Out(B.poly "term","Body",
    Full(global, "Unfolds an abbreviation")))),
  (fun sd arglist _ ~depth {env} _ state ->
    let args, _ = Syntax_def.search_syntactic_definition sd in
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
      CLocalAssum([lname],Default Glob_term.Explicit, CAst.make @@ CHole(None,Namegen.IntroAnonymous,None)),
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
    state, !: (API.Utils.beta ~depth t arglist), []
  )),
  DocAbove);

  MLCode(Pred("coq.notation.abbreviation-body",
    In(abbreviation,"Abbreviation",
    Out(B.int,"Nargs",
    Out(B.poly "term","Body",
    Full(global, "Retrieves the body of an abbreviation")))),
  (fun sd _ _ ~depth {env} _ state ->
    let args, _ = Syntax_def.search_syntactic_definition sd in
    let nargs = List.length args in
    let open Constrexpr in
    let binders, vars = List.split (CList.init nargs (fun i ->
      let name = Coq_elpi_glob_quotation.mk_restricted_name i in
      let lname = CAst.make @@ Name.Name (Id.of_string name) in
      CLocalAssum([lname],Default Glob_term.Explicit, CAst.make @@ CHole(None,Namegen.IntroAnonymous,None)),
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
    (fun name tacname more_args ~depth { options} _ -> on_global_state "coq.notation.add-abbreviation-for-tactic" (fun state ->
      let sigma = get_sigma state in
      let env = get_global_env state in
      let tac_fixed_args = more_args |> List.map (function
        | Coq_elpi_arg_HOAS.Cint n -> Coq_elpi_arg_HOAS.Tac.Int n
        | Coq_elpi_arg_HOAS.Cstr s -> Coq_elpi_arg_HOAS.Tac.String s
        | Coq_elpi_arg_HOAS.Ctrm t -> Coq_elpi_arg_HOAS.Tac.Term (Coq_elpi_utils.detype env sigma t,None)) in
      let abbrev_name = Coq_elpi_utils.string_split_on_char '.' name in
      let tac_name = Coq_elpi_utils.string_split_on_char '.' tacname in
      Lib.add_anonymous_leaf @@ inAbbreviationForTactic { abbrev_name; tac_name; tac_fixed_args};
      state, (), []))),
    DocAbove);

  MLData attribute_value;
  MLData attribute;

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
           let sigma = Evarconv.unify proof_context.env sigma ~with_ho:true Reduction.CUMUL ty ety in
           let state, assignments = set_current_sigma ~depth state sigma in
           state, !: ety +! B.mkOK, assignments
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
    InOut(B.ioarg universe, "U",
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
           let sigma = Evarconv.unify proof_context.env sigma ~with_ho:true Reduction.CUMUL (EConstr.mkSort s) (EConstr.mkSort es) in
           let state, assignments = set_current_sigma ~depth state sigma in
           state, !: es +! B.mkOK, assignments
       | NoData ->
           let flags = Evarconv.default_flags_of TransparentState.full in
           let sigma = Evarconv.solve_unif_constraints_with_heuristics ~flags ~with_ho:true proof_context.env sigma in
           let state, assignments = set_current_sigma ~depth state sigma in
           state, !: s +! B.mkOK, assignments
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
       let sigma = Evarconv.unify proof_context.env sigma ~with_ho:true Reduction.CONV a b in
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
       let sigma = Evarconv.unify proof_context.env sigma ~with_ho:true Reduction.CUMUL a b in
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
hole. Similarly universe levels present in T are disregarded.|}))))),
  (fun gt ety _ diag ~depth proof_context _ state ->
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
        Pretyping.understand_tcc_ty proof_context.env sigma ~expected_type gt in
      match ety_given with
      | `No ->
          let state, assignments = set_current_sigma ~depth state sigma in
          state, !: uj_type +! uj_val +! B.mkOK, assignments
      | `Yes ->
          let state, assignments = set_current_sigma ~depth state sigma in
          state, ?: None +! uj_val +! B.mkOK, assignments
      | `NoUnify ety ->
          let sigma = Evarconv.unify proof_context.env sigma ~with_ho:true Reduction.CUMUL uj_type ety in
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
     Out(universe, "U",
     COut(term,  "E",
     InOut(B.ioarg B.diagnostic, "Diagnostic",
     Full (proof_context,{|elabotares T expecting it to be a type of sort U.
T is allowed to contain holes (unification variables) but these are
not assigned even if the elaborated term has a term in place of the
hole. Similarly universe levels present in T are disregarded.|}))))),
  (fun gt es _ diag ~depth proof_context _ state ->
    try
      let sigma = get_sigma state in
      let expected_type = Pretyping.IsType in
      let sigma, uj_val, uj_type =
        Pretyping.understand_tcc_ty proof_context.env sigma ~expected_type gt in
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

  LPDoc "-- Coq's reduction machines ------------------------------------";

  MLCode(Pred("coq.reduction.lazy.whd_all",
    CIn(term,"T",
    COut(term,"Tred",
    Read(proof_context, "Puts T in weak head normal form"))),
    (fun t _ ~depth proof_context constraints state ->
       let sigma = get_sigma state in
       let t = EConstr.of_constr @@ Reduction.whd_all proof_context.env (EConstr.to_constr ~abort_on_undefined_evars:false sigma t) in
       !: t)),
  DocAbove);

  MLCode(Pred("coq.reduction.lazy.norm",
    CIn(term,"T",
    COut(term,"Tred",
    Read(proof_context, "Puts T in normal form"))),
    (fun t _ ~depth proof_context constraints state ->
       let sigma = get_sigma state in
       let t = Reductionops.nf_all proof_context.env sigma t in
       !: t)),
  DocAbove);

  MLCode(Pred("coq.reduction.cbv.norm",
    CIn(term,"T",
    COut(term,"Tred",
    Read(proof_context, "Puts T in weak head normal form"))),
    (fun t _ ~depth proof_context constraints state ->
       let sigma = get_sigma state in
       let t = Tacred.compute proof_context.env sigma t in
       !: t)),
  DocAbove);

  MLCode(Pred("coq.reduction.vm.norm",
    CIn(term,"T",
    CIn(B.unspecC term,"Ty",
    COut(term,"Tred",
    Read(proof_context, "Puts T in normal form. Its type Ty can be omitted (but is recomputed)")))),
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
    Read(proof_context, "Puts T in normal form. Its type Ty can be omitted (but is recomputed). Falls back to vm.norm if native compilation is not available.")))),
    (fun t ty _ ~depth proof_context constraints state ->
       let sigma = get_sigma state in
       let sigma, ty =
         match ty with
         | B.Given ty -> sigma, ty
         | B.Unspec -> Typing.type_of proof_context.env sigma t in
       let t =
         if Flags.get_native_compiler () then
           Nativenorm.native_norm proof_context.env sigma t ty
         else
           Vnorm.cbv_vm proof_context.env sigma t ty in
       !: t)),
  DocAbove);

  MLCode(Pred("coq.reduction.native.available?",
    Easy "Is native compilation available on this system/configuration?",
    (fun ~depth:_ -> if not (Flags.get_native_compiler ()) then raise No_clause)),
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

  LPDoc "-- Coq's conversion strategy tweaks --------------------------";

  MLData conversion_strategy;

  MLCode(Pred("coq.strategy.set",
    In(B.list constant, "CL",
    In(conversion_strategy, "Level",
    Full(global,"Sets the unfolding priority for all the constants in the list CL. See the command Strategy."))),
    (fun csts level ~depth:_ ctx _ -> on_global_state "coq.strategy.set" (fun state ->
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
              if Evar.Set.mem n acc_set then List.fold_left evrec acc l
              else
                let acc = Evar.Set.add n acc_set, n :: acc_rev_l in
                List.fold_left evrec acc l
          | _ -> EConstr.fold sigma evrec acc c
        in
        let _, rev_l = evrec (Evar.Set.empty, []) c in
        List.rev rev_l in
      let subgoals = evars_of_term sigma proof in
      let free_evars =
        let cache = Evarutil.create_undefined_evars_cache () in
        let map ev =
          let evi = Evd.find sigma ev in
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
    In(B.string, "Tac",
    CIn(goal, "G",
    Out(list sealed_goal,"GL",
    Full(raw_ctx, "Calls Ltac1 tactic named Tac on goal G (passing the arguments of G, see coq.ltac.call for a handy wrapper)")))),
    (fun tac_name (proof_context,goal,tac_args) _ ~depth _ _ state ->
      let open Ltac_plugin in
      let sigma = get_sigma state in
       let tac_args = tac_args |> List.map (function
         | Coq_elpi_arg_HOAS.Ctrm t -> Tacinterp.Value.of_constr t
         | Coq_elpi_arg_HOAS.Cstr s -> Geninterp.(Val.inject (val_tag (Genarg.topwit Stdarg.wit_string))) s
         | Coq_elpi_arg_HOAS.Cint i -> Tacinterp.Value.of_int i) in
       let tactic =
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
         let tac = Tacinterp.Value.of_closure (Tacinterp.default_ist ()) tacexpr in
         Tacinterp.Value.apply tac tac_args in
       let subgoals, sigma =
         let open Proofview in let open Notations in
         let focused_tac =
           Unsafe.tclSETGOALS [with_empty_state goal] <*> tactic in
         let _, pv = init sigma [] in
         let (), pv, _, _ =
           try
             apply ~name:(Id.of_string "elpi") ~poly:false proof_context.env focused_tac pv
           with e when CErrors.noncritical e ->
             Feedback.msg_debug (CErrors.print e);
             raise Pred.No_clause
         in
           proofview pv in
       let state, assignments = set_current_sigma ~depth state sigma in
       state, !: subgoals, assignments
      )),
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
    | Some { Goptions.opt_depr = x; _ }  -> !: x
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
    Lib.add_anonymous_leaf @@ inGoption (depr,key,value))),
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

  MLCode(Pred("coq.elpi.accumulate",
    In(B.unspec scope, "Scope",
    In(id, "DbName",
    In(clause, "Clause",
    Full (global, {|
Declare that, once the program is over, the given clause has to be
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
- @local! (default: false, discard at the end of section or module)|} )))),
  (fun scope dbname (name,graft,clause) ~depth ctx _ state ->
     let loc = API.Ast.Loc.initial "(elpi.add_clause)" in
     let dbname = Coq_elpi_utils.string_split_on_char '.' dbname in
     warn_if_contains_univ_levels ~depth clause;
     let vars = collect_term_variables ~depth clause in
     let clause = API.Utils.clause_of_term ?name ?graft ~depth loc clause in
     let local = ctx.options.local = Some true in
     match scope with
     | B.Unspec | B.Given ExecutionSite ->
         let scope = if local then Local else Regular in
         State.update clauses_for_later state (fun l ->
           (dbname,clause,vars,scope) :: l), (), []
     | B.Given Library ->
         if local then CErrors.user_err Pp.(str "coq.elpi.accumulate: library scope is incompatible with @local!");
         State.update clauses_for_later state (fun l ->
           (dbname,clause,vars,Global) :: l), (), []
     | B.Given CurrentModule ->
          let scope = if local then Local else Regular in
          let f = get_accumulate_to_db () in
          f dbname clause vars ~scope;
          state, (), []
     )),
  DocAbove);

  LPDoc "-- Utils ------------------------------------------------------------";
  ] @
  B.ocaml_set ~name:"coq.gref.set" gref (module GRSet) @
  B.ocaml_map ~name:"coq.gref.map" gref (module GRMap) @
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
