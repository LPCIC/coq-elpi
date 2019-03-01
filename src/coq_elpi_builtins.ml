(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi_API
module E = API.Extend.Data
module CS = API.Extend.CustomState
module CP = API.Extend.BuiltInPredicate
module P = API.Extend.Pp

module G = Globnames

open Names
open Glob_term

open Coq_elpi_utils
open Coq_elpi_HOAS

let body_of_constant_in_context state depth c =
  let state, bo = body_of_constant state c in
  match bo with
  | None -> state, None
  | Some bo ->
      let state, bo = constr2lp state ~depth bo in
      state, Some bo

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
           UnivNames.pr_with_global_universes p);
      raise CP.No_clause
  | Evd.UniversesDiffer | UState.UniversesDiffer ->
      Feedback.msg_debug Pp.(str"UniversesDiffer");
      raise CP.No_clause

let mk_fresh_univ state = new_univ state
  
let mk_algebraic_super x = Univ.super x
let mk_algebraic_max x y = Univ.Universe.sup x y

(* I don't want the user to even know that algebraic universes exist *)
let purge_algebraic_univs state t =
  (* no map_fold iterator :-/ *)      
  let state = ref state in
  let rec aux t =
    match Constr.kind t with
    | Constr.Sort (Sorts.Type u) when not (Univ.Universe.is_level u) ->
        let new_csts, v = mk_fresh_univ !state in
        state := add_universe_constraint new_csts (constraint_leq u v);
        Constr.mkSort (Sorts.Type v)
    | _ -> Constr.map aux t in
  let t = aux t in
  !state, t

let univ_super state u =
  let state, v = mk_fresh_univ state in
  let state, u =
    if Univ.Universe.is_level u then state, u
    else 
      let state, w = mk_fresh_univ state in
      add_universe_constraint state (constraint_leq u w), w in
  let state =
    add_universe_constraint state (constraint_leq (mk_algebraic_super u) v) in
  state, v

let univ_max state u1 u2 =
  let state, v = mk_fresh_univ state in
  let state =
    add_universe_constraint state (constraint_leq (mk_algebraic_max u1 u2) v) in
  state, v

let constr2lp ?coq_proof_ctx_names state depth t =
  let state, t = purge_algebraic_univs state t in
  constr2lp state ?coq_proof_ctx_names ~depth t

let type_of_global_in_context state depth r = 
  let state, ty = type_of_global state r in
  constr2lp state depth ty

(* pre-process arguments of a custom predicate turning UVars into fresh
 * universes *)
let force_univ ~depth state = function
  | CP.Flex _ | CP.Discard ->
      let state, u = mk_fresh_univ state in
      state, u
  | CP.Data u -> state, u

let clauses_for_later =
  CS.declare ~name:"coq-elpi:clauses_for_later"
    ~init:(CS.Other (fun () -> []))
    ~pp:(fun fmt l ->
       List.iter (fun (dbname, code) ->
         Format.fprintf fmt "db:%s code:%a\n" dbname
            Elpi_API.Pp.Ast.program code) l)
;;

(* In a perfect world where custom_constraints contains the entire
 * Coq state, this name is appropriate *)
let grab_global_state = grab_global_env

let to_coercion_class err depth x =
  match E.look ~depth x with
  | E.App(c,gr,[]) when is_globalc c ->
      begin match E.look ~depth gr with
      | E.CData gr when isgr gr -> Class.class_of_global (grout gr)
      | _ -> err ()
      end
  | _ when is_prod ~depth x -> Classops.CL_FUN
  | _ when is_sort ~depth x -> Classops.CL_SORT
  | _ -> err ()

type 'a unspec = Given of 'a | Unspec

(* to be used with In *)
let unspec data = {
  CP.ty = data.CP.ty;
  to_term = (function
     | Given x -> data.CP.to_term x
     | Unspec -> assert false); (* only for input *)
  of_term = (fun ~depth x ->
               match E.look ~depth x with
               | (E.UVar _ | E.AppUVar _) -> CP.Data Unspec
               | E.Discard -> CP.Data Unspec
               | t ->
                   match data.CP.of_term ~depth (E.kool t) with
                   | CP.Data x -> CP.Data (Given x)
                   | _ -> CP.Data Unspec)
}

let term = { CP.any with CP.ty = "term" }
let modpath = CP.data_of_cdata ~name:"@modpath" modpath
let modtypath = CP.data_of_cdata ~name:"@modtypath" modtypath
let id = { CP.string with CP.ty = "@id" }
let gref = {
  CP.ty = "@gref";
  to_term = (fun gr -> E.mkCData (grin gr));
  of_term = (fun ~depth x ->
               match E.look ~depth x with
               | E.CData c when isgr c -> CP.Data (grout c)
               | (E.UVar _ | E.AppUVar _) as x -> CP.Flex (E.kool x)
               | E.Discard -> CP.Discard
               | t -> raise (CP.TypeErr (E.kool t)))
}
let indt_gr s gr =
  match gr with
  | G.IndRef i -> i
  | _ -> err Pp.(str s ++ str ": not a reference to an inductive type")
let indc_gr s gr =
  match gr with
  | G.ConstructRef c -> c
  | _ -> err Pp.(str s ++ str ": not a reference to an inductive constructor")
let const_gr s gr =
  match gr with
  | G.ConstRef c -> `Const c
  | G.VarRef v -> `Var v
  | _ -> err Pp.(str s ++ str ": not a reference to an inductive constructor")
let bool = {
  CP.ty = "bool";
  to_term = (function true -> in_elpi_tt | false -> in_elpi_ff);
  of_term = (fun ~depth x ->
               let x = E.look ~depth x in
               if E.kool x == in_elpi_tt then CP.Data true
               else if E.kool x == in_elpi_ff then CP.Data false
               else match x with
               | (E.UVar _ | E.AppUVar _) -> CP.Flex (E.kool x)
               | E.Discard -> CP.Discard
               | _ -> raise (CP.TypeErr (E.kool x)))
}
let flag name = { (unspec bool) with CP.ty = name }
let indt_decl = { CP.any with CP.ty = "indt-decl" }
let cs_instance = { CP.any with CP.ty = "cs-instance" }
let tc_instance = { CP.any with CP.ty = "tc-instance" }
let clause = { CP.any with CP.ty = "clause" }
let univ =  CP.data_of_cdata ~name:"@univ" univ
let name =  CP.data_of_cdata ~name:"@name" name

let coq_builtins = 
  let open CP in
  let open Notation in
  let pp ~depth = P.term depth in
        
  [

  LPDoc "-- Printing (debugging) ---------------------------------------------";

  MLCode(Pred("coq.say",
    VariadicIn(any,"Prints an info message"),
  (fun args ~depth hyps { E.state } ->
     let pp = pp ~depth in
     Feedback.msg_info Pp.(str (pp2string (P.list ~boxed:true pp " ") args));
     state, ())),
  DocAbove);

  MLCode(Pred("coq.warn",
    VariadicIn(any,"Prints a warning message"),
  (fun args ~depth hyps { E.state } ->
     let pp = pp ~depth in
     Feedback.msg_warning Pp.(str (pp2string (P.list ~boxed:true pp " ") args));
     state, ())),
  DocAbove);

  MLCode(Pred("coq.error",
    VariadicIn(any,"Prints and *aborts* the program (it's a fatal error)"),
  (fun args ~depth hyps sol ->
     let pp = pp ~depth in
     err Pp.(str (pp2string (P.list ~boxed:true pp " ") args)))),
  DocAbove);

  LPDoc "-- Nametab ----------------------------------------------------------";

  MLCode(Pred("coq.locate",
    In(string, "Name",
    Out(term,  "TermFound",
    Easy "See the Locate vernacular. TermFound is indc, indt or const")),
  (fun s _ ~depth:_ ->
    let qualid = Libnames.qualid_of_string s in
    let gr =
      try 
        match Nametab.locate_extended qualid with
        | G.TrueGlobal gr -> gr
        | G.SynDef sd -> 
           match Syntax_def.search_syntactic_definition sd with
           | _, Notation_term.NRef gr -> gr
           | _ -> nYI "complex call to Locate"
        with Not_found ->
            err Pp.(str "Not found: " ++ Libnames.pr_qualid qualid) in
    !:(in_elpi_gr gr))),
  DocAbove);

  MLCode(Pred("coq.locate-module",
    In(id, "ModName",
    Out(modpath, "ModPath",
    Easy "locates a module. *E*")),
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
    Easy "locates a module. *E*")),
  (fun s _ ~depth ->
    let qualid = Libnames.qualid_of_string s in
    let mp =
      try Nametab.locate_modtype qualid
      with Not_found ->
        err Pp.(str "Module type not found: " ++ Libnames.pr_qualid qualid) in
    !:mp)),
  DocAbove);

  LPDoc "-- Environment: read ------------------------------------------------";

  MLCode(Pred("coq.env.typeof-gr",
    In(gref, "GR",
    Out(term, "Ty",
    Full "reads the type Ty of a (const GR, indt GR, indc GR)")),
  (fun gr _ ~depth _ { E.state } ->
    let state, ty = type_of_global_in_context state depth gr in
    state, !:ty)),
  DocAbove);

  LPDoc "While constants, inductive type and inductive constructors do share the same data type for their names, namely @gref, the predicates named coq.env-{const,indt,indc} can only be used for objects of kind {const,indt,indc} respectively.";

  MLCode(Pred("coq.env.indt",
    In(gref, "reference to the inductive type",
    Out(bool, "tt if the type is inductive (ff for co-inductive)",
    Out(int,  "number of parameters",
    Out(int,  "number of parameters that are uniform (<= parameters)",
    Out(term, "type of the inductive type constructor including parameters",
    Out(list term, "list of constructors like [ (indc \"O\"); (indc \"S\") ]",
    Out(list term, "list of the types of the constructors (type of KNames)",
    Full "reads the inductive type declaration for the environment"))))))),
  (fun gr _ _ _ arity knames ktypes ~depth _ { E.state } ->
     let i = indt_gr "coq.env.indt" gr in
     let open Declarations in
     let env, evd = get_global_env_evd state in
     let mind, indbo as ind = Inductive.lookup_mind_specif env i in
     if Array.length mind.mind_packets <> 1 then
       nYI "API(env) mutual inductive";
     if Declareops.inductive_is_polymorphic mind then
       nYI "API(env) poly mutual inductive";
     if mind.mind_finite = Declarations.CoFinite then
       nYI "API(env) co-inductive";
     let co  = true in
     let lno = mind.mind_nparams in
     let luno = mind.mind_nparams_rec in
     let state, arity =
       if arity = Discard then state, None else
       let ty =
         Inductive.type_of_inductive
           env (ind,Univ.Instance.empty) in
       let state, ty = constr2lp state depth ty in
       state, Some ty in
     let knames =
       if knames = Discard then None else
       Some CList.(map in_elpi_gr (init
         Declarations.(indbo.mind_nb_constant + indbo.mind_nb_args)
           (fun k -> G.ConstructRef (i,k+1)))) in
     let state, ktypes =
       if ktypes = Discard then state, None else
       let kts = Inductive.type_of_constructors (i,Univ.Instance.empty) ind in
       let state, ktypes =
         List.fold_right (fun t (state, acc) ->
           let state, t = constr2lp state depth t in
           state, t :: acc)
         (Array.to_list kts) (state, []) in
       state, Some ktypes in
     state, !: co +! lno +! luno +? arity +? knames +? ktypes)),
  DocNext);

  MLCode(Pred("coq.env.indc",
    In(gref, "GR",
    Out(int, "ParamNo",
    Out(int, "UnifParamNo",
    Out(int, "Kno",
    Out(term,"Ty",
    Full ("reads the type Ty of an inductive constructor GR, as well as "^
          "the number of parameters ParamNo and uniform parameters "^
          "UnifParamNo and the number of the constructor Kno (0 based)")))))),
  (fun gr _ _ _ ty ~depth _ { E.state } ->
    let (i,k as kon) = indc_gr "coq.env.indc" gr in
    let open Declarations in
    let env, evd = get_global_env_evd state in
    let mind, indbo as ind = Inductive.lookup_mind_specif env i in
    let lno = mind.mind_nparams in
    let luno = mind.mind_nparams_rec in
    let state, ty =
      if ty = Discard then state, None else
      let ty = Inductive.type_of_constructor (kon,Univ.Instance.empty) ind in
      let state, ty = constr2lp state depth ty in
      state, Some ty in
    state, !: lno +! luno +! (k-1) +? ty)),
  DocAbove);

  MLCode(Pred("coq.env.const-opaque?",
    In(gref, "GR",
    Read "checks if GR is an opaque constant"),
  (fun gr ~depth _ { E.state } ->
    let env, evd = get_global_env_evd state in
    match const_gr "coq.env.const-opaque?" gr with
    | `Const c ->
        let open Declareops in
        let cb = Environ.lookup_constant c env in
        if is_opaque cb || not(constant_has_body cb) then ()
        else raise CP.No_clause
    | `Var v ->
        match Environ.lookup_named v env with
        | Context.Named.Declaration.LocalDef _ -> raise CP.No_clause
        | Context.Named.Declaration.LocalAssum _ -> ())),
  DocAbove);

  MLCode(Pred("coq.env.const",
    In(gref,  "GR",
    Out(term, "Bo",
    Out(term, "Ty",
    Full ("reads the type Ty and the body Bo of constant GR. "^
          "Opaque constants have Bo = hole.")))),
  (fun gr bo ty ~depth _ { E.state } ->
    let env, evd = get_global_env_evd state in
    match const_gr "coq.env.const" gr with
    | `Const c ->
        let state, ty =
          if ty = Discard then state, None else
          let state, ty = type_of_global_in_context state depth gr in
          state, Some ty in
        let state, bo =
          if bo = Discard then state, None else
          let opaque = Declareops.is_opaque (Environ.lookup_constant c env) in
          if opaque then state, Some in_elpi_implicit
          else
            let state, bo = body_of_constant_in_context state depth c in
            state, Some (Option.default in_elpi_implicit bo) in
        state, ?: bo +? ty
    | `Var v ->
        let state, ty =
          if ty = Discard then state, None else
          let state, ty = type_of_global_in_context state depth gr in
          state, Some ty in
        let state, bo = 
          if bo = Discard then state, None else
          match Environ.lookup_named v env with
          | Context.Named.Declaration.LocalDef(_,bo,_) ->
              let state, bo = constr2lp state depth bo in
              state, Some bo
          | Context.Named.Declaration.LocalAssum _ ->
              state, Some in_elpi_implicit in
        state, ?: bo +? ty)),
  DocAbove);

  MLCode(Pred("coq.env.const-body",
    In(gref,  "GR",
    Out(term, "Bo",
    Full ("reads the body of a constant, even if it is opaque. "^
          "If such body is hole, then the constant is a true axiom"))),
  (fun gr _ ~depth _ { E.state } ->
    let env, evd = get_global_env_evd state in
    match const_gr "coq.env.const-body" gr with
    | `Const c ->
         let state, bo = 
           let state, bo = body_of_constant_in_context state depth c in
           state, Option.default in_elpi_implicit bo in
         state, !: bo
    | `Var v ->
         let state, bo =
           match Environ.lookup_named v env with
           | Context.Named.Declaration.LocalDef(_,bo,_) ->
               constr2lp state depth bo
           | Context.Named.Declaration.LocalAssum _ ->
              state, in_elpi_implicit in
         state, !: bo)),
  DocAbove);

  MLCode(Pred("coq.env.module",
    In(modpath, "MP",
    Out(list term, "Contents",
    Read "lists the contents of a module (recurses on submodules) *E*")),
  (fun mp _ ~depth _ { E.state } ->
    let env, evd = get_global_env_evd state in
    !: (in_elpi_module (Environ.lookup_module mp env)))),
  DocAbove);

  MLCode(Pred("coq.env.module-type",
    In(modtypath, "MTP",
    Out(list id,  "Entries",
    Read ("lists the items made visible by module type "^
          "(does not recurse on submodules) *E*"))),
  (fun mp _ ~depth _ { E.state } ->
    let env, evd = get_global_env_evd state in
    !: (in_elpi_module_type (Environ.lookup_modtype mp env)))),
  DocAbove);

  LPDoc "-- Environment: write -----------------------------------------------";

  LPDoc ("Note: universe constraints are taken from ELPI's constraints "^
         "store. Use coq.univ-* in order to add constraints (or any higher "^
         "level facility as coq.elaborate or of from engine/elaborator.elpi)");

  MLCode(Pred("coq.env.add-const",
    In(id,   "Name",
    In(term, "Bo",
    In(unspec term, "Ty",
    In(flag "@opaque?", "Opaque",
    Out(term, "T",
    Full ("declare a new constant: T gets (const GR) for a new GR derived "^
          "from Name and the current module; Type can be left unspecified "^
          "and in that case the inferred one is taken (as in writing "^
          "Definition x := t); Body can be unspecified and in that case "^
          "an axiom is added")))))),
  (fun id bo ty opaque _ ~depth _ { E.state } ->
     if is_unspecified_term ~depth bo then begin (* Axiom *)
       match ty with
       | Unspec ->
         err Pp.(str "coq.env.add-const: both Type and Body are unspecified")
       | Given ty when is_unspecified_term ~depth ty ->
         err Pp.(str "coq.env.add-const: both Type and Body are unspecified")
       | Given ty ->
       let state, ty = lp2constr [] ~depth state ty in
       let env, evd = get_global_env_evd state in
       let ty = EConstr.to_constr evd ty in
       let used = EConstr.universes_of_constr evd (EConstr.of_constr ty) in
       let evd = Evd.restrict_universe_context evd used in
       let dk = Decl_kinds.(Global, false, Logical) in
       let gr, _, _ =
         ComAssumption.declare_assumption false dk
           (ty, Entries.Monomorphic_const_entry (Evd.universe_context_set evd))
           UnivNames.empty_binders [] false Declaremods.NoInline
           CAst.(make @@ Id.of_string id) in
       let state = grab_global_state state in
       state, !: (in_elpi_gr gr)
     end else
       let state, ty =
         match ty with
         | Unspec -> state, None
         | Given ty when is_unspecified_term ~depth ty ->
             state, None
         | Given ty ->
           let state, ty = lp2constr [] ~depth state ty in
           state, Some ty in
       let state, bo = lp2constr [] state ~depth bo in
       let env, evd = get_global_env_evd state in
       let bo, ty = EConstr.(to_constr evd bo, Option.map (to_constr evd) ty) in
        let ce =
          let evd = Evd.minimize_universes evd in
          let fold uvars c =
            Univ.LSet.union uvars
              (EConstr.universes_of_constr evd (EConstr.of_constr c))
          in
          let univ_vars =
            List.fold_left fold Univ.LSet.empty (Option.List.cons ty [bo]) in
          let evd = Evd.restrict_universe_context evd univ_vars in
          (* Check we conform to declared universes *)
          let uctx =
             Evd.check_univ_decl ~poly:false evd UState.default_univ_decl in
          Declare.definition_entry
            ~opaque:(opaque = Given true) ?types:ty ~univs:uctx bo in
       let dk = Decl_kinds.(Global, false, Definition) in
       let gr =
         DeclareDef.declare_definition
          (Id.of_string id) dk ce
          UnivNames.empty_binders [] Lemmas.(mk_hook (fun _ x -> x)) in
       let state = grab_global_state state in
       state, !: (in_elpi_gr gr))),
  DocAbove);

  MLCode(Pred("coq.env.add-indt",
    In(indt_decl, "Decl",
    Out(term, "I",
    Full "Declares an inductive type")),
  (fun decl _ ~depth _ { E.state } ->
     let state, me, record_info = lp2inductive_entry ~depth state decl in
     let mind =
       ComInductive.declare_mutual_inductive_with_eliminations me UnivNames.empty_binders [] in
     begin match record_info with
     | None -> () (* regular inductive *)
     | Some field_specs -> (* record: projection... *)
         let names, is_coercion =
           List.(split (map (fun { name; is_coercion } -> name, is_coercion)
             field_specs)) in
         let is_implicit = List.map (fun _ -> []) names in
         let rsp = (mind,0) in
         let cstr = (rsp,1) in
         let open Entries in
         let k_ty = List.(hd (hd me.mind_entry_inds).mind_entry_lc) in
         let fields_as_relctx = Term.prod_assum k_ty in
         let _, evd = get_global_env_evd state in
         let kinds, sp_projs =
           Record.declare_projections rsp ~kind:Decl_kinds.Definition
             (Entries.Monomorphic_const_entry
               (Evd.universe_context_set evd))
             (Names.Id.of_string "record")
             is_coercion UnivNames.empty_binders is_implicit fields_as_relctx
         in
         Recordops.declare_structure
           (rsp,cstr,List.rev kinds,List.rev sp_projs);
     end;
     let state = grab_global_state state in
     state, !: (in_elpi_gr (Globnames.IndRef(mind,0))))),
  DocAbove);

  LPDoc "Interactive module construction";

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  MLCode(Pred("coq.env.begin-module",
    In(id, "Name",
    In(unspec modtypath, "ModTyPath",
    Full "Starts a module, the modtype can be unspecified *E*")),
  (fun name mp ~depth _ { E.state } ->
     let ty =
       match mp with
       | Unspec -> Declaremods.Check []
       | Given mp ->
           let fpath = Nametab.path_of_modtype mp in
           let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
           Declaremods.(Enforce (CAst.make tname, DefaultInline)) in
     let id = Id.of_string name in
     let _mp = Declaremods.start_module Modintern.interp_module_ast
           None id [] ty in
     let state = grab_global_state state in
     state, ())),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  MLCode(Pred("coq.env.end-module",
    Out(modpath, "ModPath",
    Full "end the current module that becomes known as ModPath *E*"),
  (fun _ ~depth _ { E.state } ->
     let mp = Declaremods.end_module () in
     let state = grab_global_state state in
     state, !: mp)),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  MLCode(Pred("coq.env.begin-module-type",
    In(id, "Name",
    Full "Starts a module type *E*"),
  (fun id ~depth _ { E.state } ->
     let id = Id.of_string id in
     let _mp =
       Declaremods.start_modtype Modintern.interp_module_ast id [] [] in
     let state = grab_global_state state in
      state, ())),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  MLCode(Pred("coq.env.end-module-type",
    Out(modtypath, "ModTyPath",
    Full "end the current module type that becomes known as ModPath *E*"),
  (fun _ ~depth _ { E.state } ->
     let mp = Declaremods.end_modtype () in
     let state = grab_global_state state in
     state, !: mp)),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  MLCode(Pred("coq.env.include-module",
    In(modpath, "ModPath",
    Full "is like the vernacular Include *E*"),
  (fun mp ~depth _ { E.state } ->
     let fpath = match mp with
       | ModPath.MPdot(mp,l) ->
           Libnames.make_path (ModPath.dp mp) (Label.to_id l)
       | _ -> nYI "functors" in
     let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
     let i = CAst.make tname, Declaremods.DefaultInline in
     Declaremods.declare_include Modintern.interp_module_ast [i];
     let state = grab_global_state state in
     state, ())),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  MLCode(Pred("coq.env.include-module-type",
    In(modtypath, "ModTyPath",
    Full "is like the vernacular Include *E*"),
  (fun mp ~depth _ { E.state } ->
     let fpath = Nametab.path_of_modtype mp in
     let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
     let i = CAst.make tname, Declaremods.DefaultInline in
     Declaremods.declare_include Modintern.interp_module_ast [i];
     let state = grab_global_state state in
     state, ())),
  DocAbove);

  LPDoc "-- Universes --------------------------------------------------------";

  MLCode(Pred("coq.univ.print-constraints",
    Read "prints the set of universe constraints",
  (fun ~depth _ { E.state } ->
    let _, evd = get_global_env_evd state in
    let uc = Evd.evar_universe_context evd in
    let uc = Termops.pr_evar_universe_context uc in
    Feedback.msg_info Pp.(str "Universe constraints: " ++ uc);
    ())),
  DocAbove);

  MLCode(Pred("coq.univ.leq",
    Out(univ, "U1",
    Out(univ, "U2",
    Full "constrains U1 <= U2")),
  (fun u1 u2 ~depth _ { E.state } ->
    let state, u1 = force_univ ~depth state u1 in
    let state, u2 = force_univ ~depth state u2 in
    add_universe_constraint state (constraint_leq u1 u2), !: u1 +! u2)),
  DocAbove);

  MLCode(Pred("coq.univ.eq",
    Out(univ, "U1",
    Out(univ, "U2",
    Full "constrains U1 = U2")),
  (fun u1 u2 ~depth _ { E.state } ->
    let state, u1 = force_univ ~depth state u1 in
    let state, u2 = force_univ ~depth state u2 in
    add_universe_constraint state (constraint_eq u1 u2), !: u1 +! u2)),
  DocAbove);

  MLCode(Pred("coq.univ.new",
    In(unspec (list id), "Names",
    Out(univ, "U",
    Full "fresh universe *E*")),
  (fun nl _ ~depth _ { E.state } ->
     if not (nl = Unspec || nl = Given []) then nYI "named universes";
     let state, u = new_univ state in
     state, !: u)),
  DocAbove);

  MLCode(Pred("coq.univ.sup",
    Out(univ, "U1",
    Out(univ, "U2",
    Full "constrains U2 = U1 + 1")),
  (fun u1 _ ~depth _ { E.state } ->
    let state, u1 = force_univ ~depth state u1 in
    let state, u2 = univ_super state u1 in
    state, !: u1 +! u2)),
  DocAbove);

  MLCode(Pred("coq.univ.max",
    Out(univ, "U1",
    Out(univ, "U2",
    Out(univ, "U3",
    Full "constrains U3 = max U1 U2"))),
  (fun u1 u2 _ ~depth _ { E.state } ->
    let state, u1 = force_univ ~depth state u1 in
    let state, u2 = force_univ ~depth state u2 in
    let state, u3 = univ_max state u1 u2 in
    state, !: u1 +! u2 +! u3)),
  DocAbove);

  LPDoc "Very low level, don't use";

  MLCode(Pred("coq.univ.algebraic-max",
    Out(univ, "U1",
    Out(univ, "U2",
    Out(univ, "U3",
    Full "constrains U3 = Max(U1,U2) *E*"))),
  (fun u1 u2 _ ~depth _ { E.state } ->
    let state, u1 = force_univ ~depth state u1 in
    let state, u2 = force_univ ~depth state u2 in
    state, !: u1 +! u2 +! (mk_algebraic_max u1 u2))),
  DocAbove);

  MLCode(Pred("coq.univ.algebraic-sup",
    Out(univ, "U1",
    Out(univ, "U2",
    Full "constrains U2 = Sup(U1) *E*")),
  (fun u1 _ ~depth _ { E.state } ->
    let state, u1 = force_univ ~depth state u1 in
    state, !: u1 +! (mk_algebraic_super u1))),
  DocAbove);

  LPDoc "-- Databases (TC, CS, Coercions) ------------------------------------";

  MLCode(Pred("coq.CS.declare-instance",
    In(gref, "GR",
    Full "declares GR as a canonical structure instance"),
  (fun gr ~depth _ { E.state } ->
     Recordops.declare_canonical_structure gr;
     let state = grab_global_state state in
     state, ())),
  DocAbove);

  MLCode(Pred("coq.CS.db",
    Out(list cs_instance, "Db",
    Full "reads all instances"),
  (fun _ ~depth _ { E.state } ->
     let l = Recordops.canonical_projections () in
     let state, l = CList.fold_left_map (canonical_solution2lp ~depth) state l in
     state, !: l)),
  DocAbove);

  MLCode(Pred("coq.TC.declare-instance",
    In(gref, "GR",
    In(int,  "Priority",
    In(flag "@global?", "Global",
    Full "declare GR as a Global type class instance with Priority"))),
  (fun gr priority global ~depth _ { E.state } ->
     let global = global = Given true in
     let hint_priority = Some priority in
     let qualid =
       Nametab.shortest_qualid_of_global Names.Id.Set.empty gr in
     Classes.existing_instance global qualid
          (Some { Hints.empty_hint_info with Typeclasses.hint_priority });
     let state = grab_global_state state in
     state, ())),
  DocAbove);

  MLCode(Pred("coq.TC.db",
    Out(list tc_instance, "Db",
    Full "reads all instances"),
  (fun _ ~depth _ { E.state } ->
     let l = Typeclasses.all_instances () in
     let state, l = CList.fold_left_map (instance2lp ~depth) state l in
     state, !: l)),
  DocAbove);

  MLCode(Pred("coq.TC.db-for",
    In(gref, "GR",
    Out(list tc_instance, "Db",
    Full "reads all instances of the given class GR")),
  (fun gr _ ~depth _ { E.state } ->
     let l = Typeclasses.instances gr in
     let state, l = CList.fold_left_map (instance2lp ~depth) state l in
     state, !: l)),
  DocAbove);

  MLCode(Pred("coq.TC.class?",
    In(gref, "GR",
    Easy "checks if GR is a class"),
  (fun gr ~depth ->
     if Typeclasses.is_class gr then () else raise CP.No_clause)),
  DocAbove);

  MLCode(Pred("coq.coercion.declare",
    In(gref, "GR",
    In(term, "From",
    In(term, "To",
    In(flag "@global?", "Global",
    Full ("declares GR as a coercion From >-> To. To can also be "^
          "{{ _ -> _ }} or {{ Type }} for Funclass or Sortclass"))))),
  (fun gr from to_ global ~depth _ { E.state } ->
     let local = not (global = Given true) in
     let poly = false in
     let error () = err (Pp.str "coq.coercion.declare: wrong class") in
     let source = to_coercion_class error depth from in
     let target = to_coercion_class error depth to_ in
     Class.try_add_new_coercion_with_target gr ~local poly ~source ~target;
     let state = grab_global_state state in
     state, ())),
  DocAbove);

  LPDoc "-- Coq's pretyper ---------------------------------------------------";

  MLCode(Pred("coq.typecheck",
    In(term,  "T",
    Out(term, "Ty",
    Full ("typchecks a closed term (no holes, no context). This "^
          "limitation shall be lifted in the future. Inferred universe "^
          "constraints are put in the constraint store"))),
  (fun t _ ~depth hyps solution ->
     try
       let state, env, evd, coq_proof_ctx_names = get_current_env_evd ~depth hyps solution in
       let state, t = lp2constr [] ~depth ~coq_proof_ctx_names state t in
       let evd, ty = Typing.type_of env evd t in
       let state = set_evd state evd in
       let state, ty = constr2lp state depth ~coq_proof_ctx_names (EConstr.to_constr evd ty) in
       state, !: ty
     with Pretype_errors.PretypeError _ -> raise CP.No_clause)),
  DocAbove);

  MLCode(Pred("coq.elaborate",
    In(term,  "T",
    Out(term,  "E",
    Out(term,  "ETy",
    Full ("elabotares terms that can contain \"hole\".  It is able to "^
          "work in a proof and hypothetical context, as long as all bound "^
          "variables are accompanied by a decl or def hypothesis. "^
          "Limitation: the resulting term has to be evar free (no "^
          "unresolved holes), shall be lifted in the future")))),
  (fun t _ _ ~depth hyps solution ->
     let state, env, evd, coq_proof_ctx_names = get_current_env_evd ~depth hyps solution in
     let state, t = lp2constr [] ~depth ~coq_proof_ctx_names state t in
     let gt =
       (* To avoid turning named universes into unnamed ones *)
       Flags.with_option Constrextern.print_universes
         (Detyping.detype Detyping.Now false Id.Set.empty env evd) t in
     let gt =
       let c, _ = EConstr.destConst evd (in_coq_hole ()) in
       let rec map x = match DAst.get x with
         | GRef(Globnames.ConstRef x,None)
           when Constant.equal c x ->
              mkGHole
         | _ -> Glob_ops.map_glob_constr map x in
       map gt in
     let evd, uj_val, uj_type =
       Pretyping.understand_tcc_ty env evd gt in
     let state = set_evd state evd in
     let state, t  =
       constr2lp ~coq_proof_ctx_names state depth (EConstr.to_constr evd uj_val)  in
     let state, ty =
       constr2lp ~coq_proof_ctx_names state depth (EConstr.to_constr evd uj_type) in
     state, !: t +! ty)),
  DocAbove);

  LPDoc "-- Datatypes conversions --------------------------------------------";

  MLCode(Pred("coq.name-suffix",
    In(name, "Name",
    In(any,  "Suffix",
    Out(name,"NameSuffix",
    Easy "suffixes a Name with a string or an int or another name"))),
  (fun n suffix _ ~depth ->
     match E.look ~depth suffix with
     | E.CData i when E.C.(is_string i || is_int i || isname i) ->
         let s = Pp.string_of_ppcmds (Name.print n) in
         let suffix =
           if E.C.is_string i then E.C.to_string i
           else if E.C.is_int i then string_of_int (E.C.to_int i)
           else Pp.string_of_ppcmds (Name.print (nameout i)) in
         let s = s ^ suffix in
         !: (Name.mk_name (Id.of_string s))
     | _ -> err Pp.(str "coq.name-suffix: suffix is not int|string|@name"))),
  DocAbove);

  MLCode(Pred("coq.string->name",
    In(string, "Hint",
    Out(name,  "Name",
    Easy "creates a name hint")),
  (fun s _ ~depth -> !: (Name.mk_name (Id.of_string s)))),
  DocAbove);

  MLCode(Pred("coq.gr->id",
    In(any, "GR",
    Out(id, "Id",
    Read ("extracts the label (last component of a full kernel name). "^
          "Accepts also as @id in input, in this case it is the identity"))),
  (fun t _ ~depth _ { E.state } ->
     match E.look ~depth t with
     | E.CData id when E.C.is_string id -> !: (E.C.to_string id)
     | E.CData gr when isgr gr ->
          let open Globnames in
          let gr = grout gr in
          begin match gr with
          | VarRef v ->
              !: (Id.to_string v)
          | ConstRef c ->
              !: (Id.to_string (Label.to_id (Constant.label c)))
          | IndRef (i,0) ->
              let open Declarations in
              let env, evd = get_global_env_evd state in
              let { mind_packets } = Environ.lookup_mind i env in
              !: (Id.to_string (mind_packets.(0).mind_typename))
          | ConstructRef ((i,0),j) ->
              let open Declarations in
              let env, evd = get_global_env_evd state in
              let { mind_packets } = Environ.lookup_mind i env in
              !: (Id.to_string (mind_packets.(0).mind_consnames.(j-1)))
          | IndRef _  | ConstructRef _ ->
               nYI "mutual inductive (make-derived...)" end
     | _ -> err Pp.(str "coq.gr->id: input is not a @gref or an @id"))),
   DocAbove);

  MLCode(Pred("coq.gr->string",
    In(any, "GR",
    Out(string, "FullPath",
    Read "extract the full kernel name. GR can be a @gref or @id")),
  (fun t _ ~depth _ { E.state } ->
     match E.look ~depth t with
     | E.CData s when E.C.is_string s -> !: (E.C.to_string s)
     | E.CData gr when isgr gr ->
          let open Globnames in
          let gr = grout gr in
          begin match gr with
          | VarRef v -> !: (Id.to_string v)
          | ConstRef c -> !: (Constant.to_string c)
          | IndRef (i,0) -> !: (MutInd.to_string i)
          | ConstructRef ((i,0),j) ->
              let env, evd = get_global_env_evd state in
              let open Declarations in
              let { mind_packets } = Environ.lookup_mind i env in
              let klbl = Id.to_string (mind_packets.(0).mind_consnames.(j-1)) in
              !: (MutInd.to_string i^"."^klbl)
          | IndRef _  | ConstructRef _ ->
               nYI "mutual inductive (make-derived...)" end
     | _ -> err Pp.(str "coq.gr->string: input is not a @gref or an @id"))),
  DocAbove);

  MLCode(Pred("coq.term->string",
    In(term,"T",
    Out(string, "S",
    Full("prints a term T to a string S using Coq's pretty printer"))),
  (fun t _ ~depth hyps sol ->
     let state, env, evd, coq_proof_ctx_names = get_current_env_evd ~depth hyps sol in
     let state, t =
       lp2constr ~tolerate_undef_evar:true [] ~depth ~coq_proof_ctx_names state t in
     let s = Pp.string_of_ppcmds (Printer.pr_econstr_env env evd t) in
     state, !: s)),
  DocAbove);

  LPDoc "-- Access to Elpi's data --------------------------------------------";

   (* Self modification *)
  MLCode(Pred("coq.elpi.accumulate",
    In(id, "DbName",
    In(clause, "Clause",
    Full ("Declare that, once the program is over, the given clause has to "^
          "be added to the given db (see Elpi Db)" ))),
  (fun dbname p ~depth _ { E.state } ->
     let p = in_elpi_clause ~depth p in
     CS.update clauses_for_later state (fun l -> (dbname,p) :: l), ())),
  DocAbove);

  ]
;;



