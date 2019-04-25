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
        Constr.mkType v
    | _ -> Constr.map aux t in
  let t = aux t in
  !state, t

let univ_super state u v =
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

(* XXX hack waiting for full roundtrip *)
let econstr2lp ?coq_proof_ctx_names state depth t =
  let t = EConstr.Unsafe.to_constr t in
  constr2lp ?coq_proof_ctx_names state depth t

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

type 'a unspec = Given of 'a | Unspec
let unspec2opt = function Given x -> Some x | Unspec -> None
let opt2unspec = function Some x -> Given x | None -> Unspec

let unspec data = {
  CP.ty = data.CP.ty;
  doc = "Can be left _";
  embed = (fun ~depth hyps solution -> function
     | Given x -> data.CP.embed ~depth hyps solution x
     | Unspec -> solution.E.state, E.mkDiscard, []);
  readback = (fun ~depth hyps solution x ->
      match E.look ~depth x with
      | (E.UVar _ | E.AppUVar _ | E.Discard) -> solution.E.state, Unspec
      | t when E.kool t == in_elpi_implicit -> solution.E.state, Unspec
      | t ->
        let state, x = data.CP.readback ~depth hyps solution (E.kool t) in
        state, Given x)
}

let grefc = gref
let gref =
  let doc = "Name for a global object (printed short, but internally they are quite long, eg Coq.Init.Datatypes.nat)." in
  CP.cdata ~name:"gref" ~doc grefc

let term = {
  CP.ty = CP.TyName "term"; 
  doc = "A Coq term containing evars";
  readback = (fun ~depth hyps solution x ->
     let state, _env, _evd, coq_proof_ctx_names = get_current_env_evd ~depth hyps solution in
     let constraints = E.constraints solution.E.constraints in
     let state, t = lp2constr constraints ~depth ~coq_proof_ctx_names state x in
     state, t);
  embed = (fun ~depth hyps solution x ->
     let state, _env, _evd, coq_proof_ctx_names = get_current_env_evd ~depth hyps solution in
     let state, t = econstr2lp ~coq_proof_ctx_names state depth x in
     state, t, []);
}

let prop = { CP.any with CP.ty = CP.TyName "prop" }
let raw_term = { CP.any with CP.ty = CP.TyName "term" }

let modpathc = modpath
let modpath = CP.cdata ~name:"modpath" modpathc

let modtypathc = modtypath
let modtypath = CP.cdata ~name:"modtypath" modtypathc

let id =
  let doc =
{|Name as input by the user, e.g. in the declaration of an inductive, the name
of constructors are @id (since they matter to the user, e.g. they all must
be distinct).  |} in  
  CP.cdata ~name:"id" ~doc E.C.string

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
let bool = Elpi_builtin.bool

let flag name = { (unspec bool) with CP.ty = CP.TyName name }
let indt_decl = { CP.any with CP.ty = CP.TyName "indt-decl" }

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

(* We patch data_of_cdata by forcing all output universes that
 * are unification variables to be a Coq universe variable, so that
 * we can always call Coq's API *)
let univc = univ
let univ =
  (* turn UVars into fresh universes *)
  let doc = "Universe level for the predicative hierarchy of Type" in
  let univ = CP.cdata ~name:"univ" ~doc univ in
  { univ with
  CP.readback = begin fun ~depth hyps solution t ->
    match E.look ~depth t with
    | (E.UVar _ | E.AppUVar _) -> mk_fresh_univ solution.E.state 
    | _ -> univ.CP.readback ~depth hyps solution t
  end
}
let get_univ name = function CP.Data u -> u | _ -> API.Extend.Utils.type_error (name ^": @univ expected, got _")

let sort_adt = let open CP in let open ADT in {
  ty = TyName "universe";
  doc = "Universes (for the sort term former)";
  constructors = [
    K("prop","impredicative sort of propositions",N,
      Sorts.prop,
      fun ~ok ~ko -> function Sorts.Prop -> ok | _ -> ko);
    K("sprop","impredicative sort of propositions with definitional proof irrelevance",N,
      Sorts.sprop,
      fun ~ok ~ko -> function Sorts.Prop -> ok | _ -> ko);
    K("typ","predicative sort of data (carries a level)",A(univ,N),
      (fun u -> Sorts.sort_of_univ u),
      fun ~ok ~ko -> function
        | Sorts.Type x -> ok x 
        | Sorts.Set -> ok Univ.type0_univ
        | _ -> ko);
  ]
}
let sort = CP.adt sort_adt

let cs_pattern_adt = let open CP in let open ADT in let open Recordops in {
  ty = TyName "cs-pattern";
  doc = "Pattern for canonical values";
  constructors = [
    K("cs-gref","",A(gref,N),
      (fun x -> Const_cs x),
      (fun ~ok ~ko -> function Const_cs x -> ok x | _ -> ko));
    K("cs-prod","",N,
      Prod_cs,
      (fun ~ok ~ko -> function Prod_cs -> ok | _ -> ko));
    K("cs-sort","",A(sort,N),
      (fun s -> Sort_cs (Sorts.family s)),
      (fun ~ok ~ko -> function
        | Sort_cs Sorts.InSet -> ok Sorts.set
        | Sort_cs Sorts.InProp -> ok Sorts.prop
        | Sort_cs Sorts.InType ->
            fun ({ E.state } as sol) ->
              let state, u = mk_fresh_univ state in
              ok (Sorts.sort_of_univ u) { sol with E.state }
        | _ -> ko))
  ]
}
let cs_pattern = CP.adt cs_pattern_adt

let cs_instance_adt = let open CP in let open ADT in let open Recordops in {
  ADT.ty = TyName "cs-instance";
  doc = "Canonical Structure instances: (cs-instance Proj ValPat Inst)";
  constructors = [
    K("cs-instance","",A(gref,A(cs_pattern,A(term,N))),
      (fun p v i -> assert false),
      (fun ~ok ~ko ((proj_gr,patt), {
  o_DEF = solution;       (* c *)
  o_CTX = uctx_set;
  o_INJ = def_val_pos;    (* Some (j \in [0-n]) if ti = xj *)
  o_TABS = types;         (* b1 .. bk *)
  o_TPARAMS = params;     (* p1 .. pm *)
  o_NPARAMS = nparams;    (* m *)
  o_TCOMPS = cval_args }) -> ok proj_gr patt (EConstr.of_constr solution)))
  ]
}
let cs_instance = CP.adt cs_instance_adt

let tc_instance_adt = let open CP in let open ADT in let open Typeclasses in {
  ty = TyName "tc-instance";
  doc = "Type class instance with priority";
  constructors = [
    K("tc-instance","",A(gref,A(int,N)),
      (fun g p -> nYI "lp2instance"),
      (fun ~ok ~ko i ->
          ok (instance_impl i) (Option.default 0 (hint_priority i))));  
]}
let tc_instance = CP.adt tc_instance_adt

let grafting_adt = let open CP in let open ADT in {
  ty = TyName "grafting";
  doc = "";
  constructors = [
    K("before","",A(id,N),
        (fun x -> (`Before,x)),
        (fun ~ok ~ko -> function (`Before,x) -> ok x | _ -> ko));
    K("after","",A(id,N),
        (fun x -> (`After,x)),
        (fun ~ok ~ko -> function (`After,x) -> ok x | _ -> ko));
  ]
}
let grafting = CP.adt grafting_adt

let clause_adt = let open CP in let open ADT in {
  ty = TyName "clause";
  doc = {|clauses

A clause like
  :name "foo" :before "bar" foo X Y :- bar X Z, baz Z Y
is represented as
  clause "foo" (before "bar") (pi x y z\ foo x y :- bar x z, baz z y)
that is exactly what one would load in the context using =>.
          
The name and the grafting specification can be left unspecified.|};
  constructors = [
    K("clause","",A(unspec id,A(unspec grafting,A(prop,N))),
      (fun id graft c -> unspec2opt id, unspec2opt graft, c),
      (fun ~ok ~ko (id,graft,c) -> ok (opt2unspec id) (opt2unspec graft) c));
  ]
}
let clause = CP.adt clause_adt

let class_adt = let open CP in let open ADT in let open Classops in {
  ty = TyName "class";
  doc = "Node of the coercion graph";
  constructors = [
   K("funclass","",N,
     CL_FUN,
     fun ~ok ~ko -> function Classops.CL_FUN -> ok | _ -> ko);
   K("sortclass","",N,
     CL_SORT,
     fun ~ok ~ko -> function CL_SORT -> ok | _ -> ko);
   K("grefclass","",A(gref,N),
     Class.class_of_global,
     fun ~ok ~ko -> function 
     | CL_SECVAR v -> ok (GlobRef.VarRef v)
     | CL_CONST c -> ok (GlobRef.ConstRef c)
     | CL_IND i -> ok (GlobRef.IndRef i)
     | CL_PROJ p -> ok (GlobRef.ConstRef (Projection.Repr.constant p))
     | _ -> ko)
]
}
let class_ = CP.adt class_adt

let coercion_adt = let open CP in let open ADT in {
  ty = TyName "coercion";
  doc = "Edge of the coercion graph";
  constructors =  [
    K("coercion","", A(gref,A(unspec CP.int,A(class_,A(class_,N)))),
      (fun t np src tgt -> t,np,src,tgt),
      fun ~ok ~ko:_ -> function (t,np,src,tgt) -> ok t np src tgt)
  ]
}
let coercion = CP.adt coercion_adt

let namec = name
let name =
  let doc =
{|Name hints (in binders), can be input writing a name between backticks, e.g.
`x` or `_` for anonymous. Important: these are just printing hints with no
meaning, hence in elpi two @name are always related: `x` = `y`.|} in
  CP.cdata ~name:"name" ~doc namec

let warning = CWarnings.create ~name:"lib" ~category:"elpi" Pp.str

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
     let loc, args =
       if args = [] then None, args
       else
         let x, args = List.hd args, List.tl args in
         match E.look ~depth x with
         | E.CData loc when E.C.is_loc loc ->
           Some (Coq_elpi_utils.to_coq_loc (E.C.to_loc loc)), args
         | _ -> None, x :: args
     in
     warning ?loc (pp2string (P.list ~boxed:true pp " ") args);
     state, ())),
  DocAbove);

  MLCode(Pred("coq.error",
    VariadicIn(any,"Prints and *aborts* the program (it's a fatal error)"),
  (fun args ~depth hyps sol ->
     let pp = pp ~depth in
     err Pp.(str (pp2string (P.list ~boxed:true pp " ") args)))),
  DocAbove);

  MLCode(Pred("coq.version",
    Out(string, "VersionString",
    Out(int, "Major",
    Out(int, "Minor",
    Out(int, "Patch",
    Easy "Fetches the version of Coq, as a string and as 3 numbers")))),
    (fun _ _ _ _ ~depth:_ ->
      let version = Coq_config.version in
      match Str.split (Str.regexp_string ".") version with
      | [ major; minor; patch ] ->
           !: version +!
           int_of_string major +! int_of_string minor +! int_of_string patch
      | _ -> !: version +! -1 +! -1 +! -1)),
  DocAbove);

  LPDoc "-- Nametab ----------------------------------------------------------";

  MLCode(Pred("coq.locate",
    In(string, "Name",
    Out(raw_term,  "TermFound",
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

  MLCData(id,E.C.string);

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

  MLCData (gref,grefc);

  MLCode(Pred("coq.env.typeof-gr",
    In(gref, "GR",
    Out(raw_term, "Ty",
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
    Out(list raw_term, "list of constructors like [ (indc \"O\"); (indc \"S\") ]",
    Out(list raw_term, "list of the types of the constructors (type of KNames)",
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
     let arity =
       if arity = Discard then None else
       let ty = Inductive.type_of_inductive env (ind,Univ.Instance.empty) in
       Some (EConstr.of_constr ty) in
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
    Out(raw_term,"Ty",
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
    Out(raw_term, "Bo",
    Out(raw_term, "Ty",
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
    Out(raw_term, "Bo",
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

  MLCData (modpath,modpathc);
  MLCData (modtypath,modtypathc);

  MLCode(Pred("coq.env.module",
    In(modpath, "MP",
    Out(list raw_term, "Contents",
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
    In(unspec raw_term, "Bo",
    In(unspec raw_term, "Ty",
    In(flag "@opaque?", "Opaque",
    Out(raw_term, "T",
    Full ("declare a new constant: T gets (const GR) for a new GR derived "^
          "from Name and the current module; Type can be left unspecified "^
          "and in that case the inferred one is taken (as in writing "^
          "Definition x := t); Body can be unspecified and in that case "^
          "an axiom is added")))))),
  (fun id bo ty opaque _ ~depth _ { E.state } ->
     match bo with
     | Unspec -> (* axiom *)
       begin match ty with
       | Unspec ->
         err Pp.(str "coq.env.add-const: both Type and Body are unspecified")
       | Given ty ->
       let state, ty = lp2constr [] ~depth state ty in
       let env, evd = get_global_env_evd state in
       let ty = EConstr.to_constr evd ty in
       let used = EConstr.universes_of_constr evd (EConstr.of_constr ty) in
       let evd = Evd.restrict_universe_context evd used in
       let dk = Decl_kinds.(Global, false, Logical) in
       let gr, _, _ =
         (* pstate is needed in Coq due to bogus reasons [to emit a warning] *)
         ComAssumption.declare_assumption ~pstate:None false dk
           (ty, Evd.univ_entry ~poly:false evd)
           UnivNames.empty_binders [] false Declaremods.NoInline
           CAst.(make @@ Id.of_string id) in
       let state = grab_global_state state in
       state, !: (in_elpi_gr gr)
     end
    | Given bo ->
       let state, ty =
         match ty with
         | Unspec -> state, None
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
         (* Again [ontop] is only needed for a warning *)
         DeclareDef.declare_definition ~ontop:None
          (Id.of_string id) dk ce
          UnivNames.empty_binders [] in
       let state = grab_global_state state in
       state, !: (in_elpi_gr gr))),
  DocAbove);

  MLCode(Pred("coq.env.add-indt",
    In(indt_decl, "Decl",
    Out(raw_term, "I",
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
             (Evd.univ_entry ~poly:false evd)
             (Names.Id.of_string "record")
             is_coercion is_implicit fields_as_relctx
         in
         Recordops.declare_structure
           (cstr, List.rev kinds, List.rev sp_projs);
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

  MLCData (univ,univc);

  MLADT sort_adt; 

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
    InOut(univ, "U1",
    InOut(univ, "U2",
    Full "constrains U1 <= U2")),
  (fun u1 u2 ~depth _ { E.state } ->
    let u1 = get_univ "coq.univ.leq" u1 in
    let u2 = get_univ "coq.univ.leq" u2 in
    add_universe_constraint state (constraint_leq u1 u2), !: u1 +! u2)),
  DocAbove);

  MLCode(Pred("coq.univ.eq",
    InOut(univ, "U1",
    InOut(univ, "U2",
    Full "constrains U1 = U2")),
  (fun u1 u2 ~depth _ { E.state } ->
    let u1 = get_univ "coq.univ.eq" u1 in
    let u2 = get_univ "coq.univ.eq" u2 in
    add_universe_constraint state (constraint_eq u1 u2), !: u1 +! u2)),
  DocAbove);

  MLCode(Pred("coq.univ.new",
    In(unspec (list id), "Names",
    Out(univ, "U",
    Full "fresh universe *E*")),
  (fun nl _ ~depth _ { E.state } ->
     if not (nl = Unspec || nl = Given []) then nYI "named universes";
     let state, u = mk_fresh_univ state in
     state, !: u)),
  DocAbove);

  MLCode(Pred("coq.univ.sup",
    InOut(univ, "U1",
    InOut(univ, "U2",
    Full "constrains U2 = U1 + 1")),
  (fun u1 u2 ~depth _ { E.state } ->
    let u1 = get_univ "coq.univ.sup" u1 in
    let u2 = get_univ "coq.univ.sup" u2 in
    let state, u2 = univ_super state u1 u2 in
    state, !: u1 +! u2)),
  DocAbove);

  MLCode(Pred("coq.univ.max",
    InOut(univ, "U1",
    InOut(univ, "U2",
    Out(univ, "U3",
    Full "constrains U3 = max U1 U2"))),
  (fun u1 u2 _ ~depth _ { E.state } ->
    let u1 = get_univ "coq.univ.max" u1 in
    let u2 = get_univ "coq.univ.max" u2 in
    let state, u3 = univ_max state u1 u2 in
    state, !: u1 +! u2 +! u3)),
  DocAbove);

  LPDoc "Very low level, don't use";

  MLCode(Pred("coq.univ.algebraic-max",
    InOut(univ, "U1",
    InOut(univ, "U2",
    Out(univ, "U3",
    Full "constrains U3 = Max(U1,U2) *E*"))),
  (fun u1 u2 _ ~depth _ { E.state } ->
    let u1 = get_univ "coq.univ.algebraic-max" u1 in
    let u2 = get_univ "coq.univ.algebraic-max" u2 in
    state, !: u1 +! u2 +! (mk_algebraic_max u1 u2))),
  DocAbove);

  MLCode(Pred("coq.univ.algebraic-sup",
    InOut(univ, "U1",
    InOut(univ, "U2",
    Full "constrains U2 = Sup(U1) *E*")),
  (fun u1 _ ~depth _ { E.state } ->
    let u1 = get_univ "coq.univ.algebraic-sup" u1 in
    state, !: u1 +! (mk_algebraic_super u1))),
  DocAbove);

  LPDoc "-- Databases (TC, CS, Coercions) ------------------------------------";

  MLADT cs_pattern_adt;
  MLADT cs_instance_adt;

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
     state, !: l)),
  DocAbove);

  MLADT tc_instance_adt;

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
    Easy "reads all instances"),
  (fun _ ~depth -> !: (Typeclasses.all_instances ()))),
  DocAbove);

  MLCode(Pred("coq.TC.db-for",
    In(gref, "GR",
    Out(list tc_instance, "Db",
    Read "reads all instances of the given class GR")),
  (fun gr _ ~depth _ { E.state } ->
    !: (Typeclasses.instances gr))),
  DocAbove);

  MLCode(Pred("coq.TC.class?",
    In(gref, "GR",
    Easy "checks if GR is a class"),
  (fun gr ~depth ->
     if Typeclasses.is_class gr then () else raise CP.No_clause)),
  DocAbove);

  MLADT class_adt;
  MLADT coercion_adt;

  MLCode(Pred("coq.coercion.declare",
    In(coercion, "C",
    In(flag "@global?", "Global",
    Full ("declares C = (coercion GR _ From To) as a coercion From >-> To. "))),
  (fun (gr, _, source, target) global ~depth _ { E.state } ->
     let local = not (global = Given true) in
     let poly = false in
     Class.try_add_new_coercion_with_target gr ~local poly ~source ~target;
     let state = grab_global_state state in
     state, ())),
  DocAbove);

  MLCode(Pred("coq.coercion.db",
    Out(list coercion, "L",
    Easy ("reads all declared coercions")),
  (fun _ ~depth ->
    (* TODO: fix API in Coq *)
     let pats = Classops.inheritance_graph () in
     let coercions = pats |> CList.map_filter (function
       | (source,target),[c] ->
           Some(c.Classops.coe_value,
                Given c.Classops.coe_param,
                fst (Classops.class_info_from_index source),
                fst (Classops.class_info_from_index target))
       | _ -> None) in
     !: coercions)),
  DocAbove);

  MLCode(Pred("coq.coercion.db-for",
    In(class_,"From",
    In(class_,"To",
    Out(list (Elpi_builtin.pair raw_term int), "L",
    Easy ("reads all declared coercions")))),
  (fun source target _ ~depth ->
    let source,_ = Classops.class_info source in
    let target,_ = Classops.class_info target in
    let path = Classops.lookup_path_between_class (source,target) in
     let coercions = path |> List.map (fun c ->
     in_elpi_gr c.Classops.coe_value, c.Classops.coe_param) in
     !: coercions)),
  DocAbove);

  LPDoc "-- Coq's pretyper ---------------------------------------------------";

  MLCode(Pred("coq.typecheck",
    In(raw_term,  "T",
    Out(raw_term, "Ty",
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
    In(raw_term,  "T",
    Out(raw_term,  "E",
    Out(raw_term,  "ETy",
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

  MLCData(name,namec);

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
    In(raw_term,"T",
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
  MLADT clause_adt;
  MLADT grafting_adt;

  MLCode(Pred("coq.elpi.accumulate",
    In(id, "DbName",
    In(clause, "Clause",
    Full ("Declare that, once the program is over, the given clause has to "^
          "be added to the given db (see Elpi Db)" ))),
  (fun dbname (name,graft,clause) ~depth _ { E.state } ->
     let loc = API.Ast.Loc.initial "(elpi.add_clause)" in
     CS.update clauses_for_later state (fun l ->
        (dbname,API.Extend.Utils.clause_of_term ?name ?graft ~depth loc clause) :: l), ())),
  DocAbove);

  ]
;;



