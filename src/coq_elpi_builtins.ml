(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module E = API.RawData
module CS = API.State
module P = API.RawPp
module CP = API.Conversion
module B = API.BuiltInData
module Pr = API.BuiltInPredicate

module G = Globnames

open Names
open Glob_term

open Coq_elpi_utils
open Coq_elpi_HOAS

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
      raise Pr.No_clause
  | Evd.UniversesDiffer | UState.UniversesDiffer ->
      Feedback.msg_debug Pp.(str"UniversesDiffer");
      raise Pr.No_clause

let mk_fresh_univ state = new_univ state
  
let mk_algebraic_super x = Univ.super x
let mk_algebraic_max x y = Univ.Universe.sup x y

(* I don't want the user to even know that algebraic universes exist *)
let purge_algebraic_univs state t =
  let sigma = get_sigma state in
  (* no map_fold iterator :-/ *)      
  let state = ref state in
  let rec aux t =
    match EConstr.kind sigma t with
    | Constr.Sort s -> begin
        match EConstr.ESorts.kind sigma s with
        | Sorts.Type u when not (Univ.Universe.is_level u) ->
            let new_csts, v = mk_fresh_univ !state in
            state := add_universe_constraint new_csts (constraint_leq u v);
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

let clauses_for_later =
  CS.declare ~name:"coq-elpi:clauses_for_later"
    ~init:(fun () -> [])
    ~pp:(fun fmt l ->
       List.iter (fun (dbname, code) ->
         Format.fprintf fmt "db:%s code:%a\n" dbname
            Elpi.API.Pp.Ast.program code) l)
;;

(* In a perfect world where custom_constraints contains the entire
 * Coq state, this name is appropriate *)
let grab_global_state = grab_global_env

type 'a unspec = Given of 'a | Unspec
let unspec2opt = function Given x -> Some x | Unspec -> None
let opt2unspec = function Some x -> Given x | None -> Unspec

let unspec data = {
  CP.ty = data.CP.ty;
  pp_doc = (fun fmt () -> Format.fprintf fmt "Can be left _");
  pp = (fun fmt -> function
    | Unspec -> Format.fprintf fmt "Unspec"
    | Given x -> Format.fprintf fmt "Given %a" data.CP.pp x);
  embed = (fun ~depth hyps constraints state -> function
     | Given x -> data.CP.embed ~depth hyps constraints state x
     | Unspec -> state, E.mkDiscard, []);
  readback = (fun ~depth hyps constraints state x ->
      match E.look ~depth x with
      | (E.UnifVar _ | E.Discard) -> state, Unspec, []
      | t when E.kool t = in_elpi_hole -> state, Unspec, []
      | t ->
        let state, x, gls = data.CP.readback ~depth hyps constraints state (E.kool t) in
        state, Given x, gls)
}

let term = {
  CP.ty = CP.TyName "term"; 
  pp_doc = (fun fmt () -> Format.fprintf fmt "A Coq term containing evars");
  pp = (fun fmt t -> Format.fprintf fmt "%s" (Pp.string_of_ppcmds (Printer.pr_econstr_env (Global.env()) Evd.empty t)));
  readback = (lp2constr ~tolerate_undef_evar:false);
  embed = constr2lp;
}

let prop = { B.any with CP.ty = CP.TyName "prop" }
let raw_term = { B.any with CP.ty = CP.TyName "term" }
let raw_goal = { B.any with CP.ty = CP.TyName "goal" }

let id = { B.string with API.Conversion.ty = CP.TyName "@id" }

let bool = Elpi.Builtin.bool

let flag name = { (unspec bool) with CP.ty = CP.TyName name }
let indt_decl = { B.any with CP.ty = CP.TyName "indt-decl" }

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
  let open CP in let open API.AlgebraicData in let open Recordops in declare {
  ty = TyName "cs-pattern";
  doc = "Pattern for canonical values";
  pp = (fun fmt -> function
    | Const_cs x -> Format.fprintf fmt "Const_cs %s" "<todo>"
    | Prod_cs -> Format.fprintf fmt "Prod_cs"
    | Sort_cs _ ->  Format.fprintf fmt "Sort_cs"
    | Default_cs -> Format.fprintf fmt "Default_cs");
  constructors = [
    K("cs-gref","",A(gref,N),
      B (fun x -> Const_cs x),
      M (fun ~ok ~ko -> function Const_cs x -> ok x | _ -> ko ()));
    K("cs-prod","",N,
      B Prod_cs,
      M (fun ~ok ~ko -> function Prod_cs -> ok | _ -> ko ()));
    K("cs-default","",N,
      B Default_cs,
      M (fun ~ok ~ko -> function Prod_cs -> ok | _ -> ko ()));
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
}

let cs_instance = let open CP in let open API.AlgebraicData in let open Recordops in declare {
  ty = TyName "cs-instance";
  doc = "Canonical Structure instances: (cs-instance Proj ValPat Inst)";
  pp = (fun fmt (_,{ o_DEF }) -> Format.fprintf fmt "%s" Pp.(string_of_ppcmds (Printer.pr_constr_env (Global.env()) Evd.empty o_DEF)));
  constructors = [
    K("cs-instance","",A(gref,A(cs_pattern,A(term,N))),
      B (fun p v i -> assert false),
      M (fun ~ok ~ko ((proj_gr,patt), {
  o_DEF = solution;       (* c *)
  o_CTX = uctx_set;
  o_INJ = def_val_pos;    (* Some (j \in [0-n]) if ti = xj *)
  o_TABS = types;         (* b1 .. bk *)
  o_TPARAMS = params;     (* p1 .. pm *)
  o_NPARAMS = nparams;    (* m *)
  o_TCOMPS = cval_args }) -> ok proj_gr patt (EConstr.of_constr solution)))
  ]
}

let tc_instance = let open CP in let open API.AlgebraicData in let open Typeclasses in declare {
  ty = TyName "tc-instance";
  doc = "Type class instance with priority";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("tc-instance","",A(gref,A(B.int,N)),
      B (fun g p -> nYI "lp2instance"),
      M (fun ~ok ~ko i ->
          ok (instance_impl i) (Option.default 0 (hint_priority i))));  
]}

let grafting = let open CP in let open API.AlgebraicData in declare {
  ty = TyName "grafting";
  doc = "";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("before","",A(id,N),
        B (fun x -> (`Before,x)),
        M (fun ~ok ~ko -> function (`Before,x) -> ok x | _ -> ko ()));
    K("after","",A(id,N),
        B (fun x -> (`After,x)),
        M (fun ~ok ~ko -> function (`After,x) -> ok x | _ -> ko ()));
  ]
}

let clause = let open CP in let open API.AlgebraicData in declare {
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
    K("clause","",A(unspec id,A(unspec grafting,A(prop,N))),
      B (fun id graft c -> unspec2opt id, unspec2opt graft, c),
      M (fun ~ok ~ko (id,graft,c) -> ok (opt2unspec id) (opt2unspec graft) c));
  ]
}

let class_ = let open CP in let open API.AlgebraicData in let open Classops in declare {
  ty = TyName "class";
  doc = "Node of the coercion graph";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
   K("funclass","",N,
     B CL_FUN,
     M (fun ~ok ~ko -> function Classops.CL_FUN -> ok | _ -> ko ()));
   K("sortclass","",N,
     B CL_SORT,
     M (fun ~ok ~ko -> function CL_SORT -> ok | _ -> ko ()));
   K("grefclass","",A(gref,N),
     B Class.class_of_global,
     M (fun ~ok ~ko -> function 
     | CL_SECVAR v -> ok (GlobRef.VarRef v)
     | CL_CONST c -> ok (GlobRef.ConstRef c)
     | CL_IND i -> ok (GlobRef.IndRef i)
     | CL_PROJ p -> ok (GlobRef.ConstRef (Projection.Repr.constant p))
     | _ -> ko ()))
]
}

let coercion = let open CP in let open API.AlgebraicData in declare {
  ty = TyName "coercion";
  doc = "Edge of the coercion graph";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors =  [
    K("coercion","", A(gref,A(unspec B.int,A(class_,A(class_,N)))),
      B (fun t np src tgt -> t,np,src,tgt),
      M (fun ~ok ~ko:_ -> function (t,np,src,tgt) -> ok t np src tgt))
  ]
}

let warning = CWarnings.create ~name:"lib" ~category:"elpi" Pp.str

let if_keep x f =
  match x with
  | Pr.Discard -> None
  | Pr.Keep -> Some (f ())

let if_keep_acc x state f =
  match x with
  | Pr.Discard -> state, None
  | Pr.Keep ->
       let state, x = f state in
       state, Some x

let coq_builtins = 
  let open API.BuiltIn in
  let open Pr in
  let open Notation in
  let pp ~depth = P.term depth in
        
  [

  LPDoc "-- Printing (debugging) ---------------------------------------------";

  MLCode(Pred("coq.say",
    VariadicIn(B.any,"Prints an info message"),
  (fun args ~depth _hyps _constraints state ->
     let pp = pp ~depth in
     Feedback.msg_info Pp.(str (pp2string (P.list ~boxed:true pp " ") args));
     state, ())),
  DocAbove);

  MLCode(Pred("coq.warn",
    VariadicIn(B.any,"Prints a warning message"),
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
     state, ())),
  DocAbove);

  MLCode(Pred("coq.error",
    VariadicIn(B.any,"Prints and *aborts* the program (it's a fatal error)"),
  (fun args ~depth _hyps _constraints _state ->
     let pp = pp ~depth in
     err Pp.(str (pp2string (P.list ~boxed:true pp " ") args)))),
  DocAbove);

  MLCode(Pred("coq.version",
    Out(B.string, "VersionString",
    Out(B.int, "Major",
    Out(B.int, "Minor",
    Out(B.int, "Patch",
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
    In(B.string, "Name",
    Out(gref,  "TermFound",
    Easy "Locates a global term")),
  (fun s _ ~depth ->
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
    !: gr)),
  DocAbove);

  (* MLData id; *)
  LPDoc {|Name as input by the user, e.g. in the declaration of an inductive, the name
of constructors are @id (since they matter to the user, e.g. they all must
be distinct).|};
  LPCode "macro @id :- ctype \"string\".";

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

  MLData constant;
  MLData inductive;
  MLData constructor;
  MLData gref;

  MLCode(Pred("coq.env.typeof-gr",
    In(gref, "GR",
    Out(term, "Ty",
    Full "reads the type Ty of a (const GR, indt GR, indc GR)")),
  (fun gr _ ~depth _ _ state ->
    let state, ty = type_of_global state gr in
    state, !:ty, [])),
  DocAbove);

  LPDoc "While constants, inductive type and inductive constructors do share the same data type for their names, namely @gref, the predicates named coq.env-{const,indt,indc} can only be used for objects of kind {const,indt,indc} respectively.";

  MLCode(Pred("coq.env.indt",
    In(inductive, "reference to the inductive type",
    Out(bool, "tt if the type is inductive (ff for co-inductive)",
    Out(B.int,  "number of parameters",
    Out(B.int,  "number of parameters that are uniform (<= parameters)",
    Out(term, "type of the inductive type constructor including parameters",
    Out(B.list constructor, "list of constructor names",
    Out(B.list term, "list of the types of the constructors (type of KNames) including parameters",
    Full "reads the inductive type declaration for the environment"))))))),
  (fun i _ _ _ arity knames ktypes ~depth _ _ state ->
     let open Declarations in
     let env, sigma = get_global_env_sigma state in
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
     let arity = if_keep arity (fun () ->
       Inductive.type_of_inductive env (ind,Univ.Instance.empty)
       |> EConstr.of_constr) in
     let knames = if_keep knames (fun () ->
       CList.(init Declarations.(indbo.mind_nb_constant + indbo.mind_nb_args)
           (fun k -> i,k+1))) in
     let ktypes = if_keep ktypes (fun () ->
       Inductive.type_of_constructors (i,Univ.Instance.empty) ind
       |> CArray.map_to_list EConstr.of_constr) in
     state, !: co +! lno +! luno +? arity +? knames +? ktypes, [])),
  DocNext);

  MLCode(Pred("coq.env.indc",
    In(constructor, "GR",
    Out(B.int, "ParamNo",
    Out(B.int, "UnifParamNo",
    Out(B.int, "Kno",
    Out(term,"Ty",
    Full ("reads the type Ty of an inductive constructor GR, as well as "^
          "the number of parameters ParamNo and uniform parameters "^
          "UnifParamNo and the number of the constructor Kno (0 based)")))))),
  (fun (i,k as kon) _ _ _ ty ~depth _ _ state ->
    let open Declarations in
    let env, sigma = get_global_env_sigma state in
    let mind, indbo as ind = Inductive.lookup_mind_specif env i in
    let lno = mind.mind_nparams in
    let luno = mind.mind_nparams_rec in
    let ty = if_keep ty (fun () ->
      Inductive.type_of_constructor (kon,Univ.Instance.empty) ind
      |> EConstr.of_constr) in
    state, !: lno +! luno +! (k-1) +? ty, [])),
  DocAbove);

  MLCode(Pred("coq.env.const-opaque?",
    In(constant, "GR",
    Read "checks if GR is an opaque constant"),
  (fun c ~depth _ _ state ->
    let env, sigma = get_global_env_sigma state in
    match c with
    | Constant c ->
        let open Declareops in
        let cb = Environ.lookup_constant c env in
        if is_opaque cb || not(constant_has_body cb) then ()
        else raise Pr.No_clause
    | Variable v ->
        match Environ.lookup_named v env with
        | Context.Named.Declaration.LocalDef _ -> raise Pr.No_clause
        | Context.Named.Declaration.LocalAssum _ -> ())),
  DocAbove);

  MLCode(Pred("coq.env.const",
    In(constant,  "GR",
    Out(term, "Bo",
    Out(term, "Ty",
    Full ("reads the type Ty and the body Bo of constant GR. "^
          "Opaque constants have Bo = hole.")))),
  (fun c bo ty ~depth _ _ state ->
    let env, sigma = get_global_env_sigma state in
    match c with
    | Constant c ->
        let state, ty = if_keep_acc ty state (fun s -> type_of_global s (Globnames.ConstRef c)) in
        let state, bo = if_keep_acc bo state (fun state ->
          if Declareops.is_opaque (Environ.lookup_constant c env)
          then state, in_coq_hole ()
          else
            let state, bo = body_of_constant state c in
            state, Option.default (in_coq_hole ()) bo) in
        state, ?: bo +? ty, []
    | Variable v ->
        let state, ty = if_keep_acc ty state (fun s -> type_of_global s (Globnames.VarRef v)) in
        let bo = if_keep bo (fun () ->
          match Environ.lookup_named v env with
          | Context.Named.Declaration.LocalDef(_,bo,_) -> bo |> EConstr.of_constr
          | Context.Named.Declaration.LocalAssum _ -> in_coq_hole ()) in
        state, ?: bo +? ty, [])),
  DocAbove);

  MLCode(Pred("coq.env.const-body",
    In(constant,  "GR",
    Out(term, "Bo",
    Full ("reads the body of a constant, even if it is opaque. "^
          "If such body is hole, then the constant is a true axiom"))),
  (fun c _ ~depth _ _ state ->
    let env, sigma = get_global_env_sigma state in
    match c with
    | Constant c ->
         let state, bo = body_of_constant state c in
         state, !: (Option.default (in_coq_hole ()) bo), []
    | Variable v ->
         state, !: begin
         match Environ.lookup_named v env with
         | Context.Named.Declaration.LocalDef(_,bo,_) -> bo |> EConstr.of_constr
         | Context.Named.Declaration.LocalAssum _ -> in_coq_hole ()
         end, [])),
  DocAbove);

  MLData modpath;
  MLData modtypath;

  MLCode(Pred("coq.env.module",
    In(modpath, "MP",
    Out(B.list gref, "Contents",
    Read "lists the contents of a module (recurses on submodules) *E*")),
  (fun mp _ ~depth _ _ state ->
    let env, sigma = get_global_env_sigma state in
    let t = in_elpi_module ~depth state (Environ.lookup_module mp env) in
    !: t)),
  DocAbove);

  MLCode(Pred("coq.env.module-type",
    In(modtypath, "MTP",
    Out(B.list id,  "Entries",
    Read ("lists the items made visible by module type "^
          "(does not recurse on submodules) *E*"))),
  (fun mp _ ~depth _ _ state ->
    let env, sigma = get_global_env_sigma state in
    !: (in_elpi_module_type (Environ.lookup_modtype mp env)))),
  DocAbove);

  LPDoc "-- Environment: write -----------------------------------------------";

  LPDoc ("Note: universe constraints are taken from ELPI's constraints "^
         "store. Use coq.univ-* in order to add constraints (or any higher "^
         "level facility as coq.elaborate or of from engine/elaborator.elpi)");

  MLCode(Pred("coq.env.add-const",
    In(id,   "Name",
    In(unspec term, "Bo",
    In(unspec term, "Ty",
    In(flag "@opaque?", "Opaque",
    Out(constant, "C",
    Full ("declare a new constant: C gets a @constant derived "^
          "from Name and the current module; Ty can be left unspecified "^
          "and in that case the inferred one is taken (as in writing "^
          "Definition x := t); Bo can be left unspecified and in that case "^
          "an axiom is added")))))),
  (fun id bo ty opaque _ ~depth _ _ state ->
     match bo with
     | Unspec -> (* axiom *)
       begin match ty with
       | Unspec ->
         err Pp.(str "coq.env.add-const: both Type and Body are unspecified")
       | Given ty ->
       let env, sigma = get_global_env_sigma state in
       let used = EConstr.universes_of_constr sigma ty in
       let sigma = Evd.restrict_universe_context sigma used in
       let dk = Decl_kinds.(Global, false, Logical) in
       let gr, _, _ =
         (* pstate is needed in Coq due to bogus reasons [to emit a warning] *)
         ComAssumption.declare_assumption ~pstate:None false dk
           (EConstr.to_constr sigma ty, Evd.univ_entry ~poly:false sigma)
           UnivNames.empty_binders [] false Declaremods.NoInline
           CAst.(make @@ Id.of_string id) in
       let state = grab_global_state state in
       state, !: (global_constant_of_globref gr), []
     end
    | Given bo ->
       let ty =
         match ty with
         | Unspec -> None
         | Given ty -> Some ty in
       let env, sigma = get_global_env_sigma state in
       let bo, ty = EConstr.(to_constr sigma bo, Option.map (to_constr sigma) ty) in
        let ce =
          let sigma = Evd.minimize_universes sigma in
          let fold uvars c =
            Univ.LSet.union uvars
              (EConstr.universes_of_constr sigma (EConstr.of_constr c))
          in
          let univ_vars =
            List.fold_left fold Univ.LSet.empty (Option.List.cons ty [bo]) in
          let sigma = Evd.restrict_universe_context sigma univ_vars in
          (* Check we conform to declared universes *)
          let uctx =
             Evd.check_univ_decl ~poly:false sigma UState.default_univ_decl in
          Declare.definition_entry
            ~opaque:(opaque = Given true) ?types:ty ~univs:uctx bo in
       let dk = Decl_kinds.(Global, false, Definition) in
       let gr =
         (* Again [ontop] is only needed for a warning *)
         DeclareDef.declare_definition ~ontop:None
          (Id.of_string id) dk ce
          UnivNames.empty_binders [] in
       let state = grab_global_state state in
       state, !: (global_constant_of_globref gr), [])),
  DocAbove);

  MLCode(Pred("coq.env.add-indt",
    In(indt_decl, "Decl",
    Out(inductive, "I",
    Full "Declares an inductive type")),
  (fun decl _ ~depth hyps constraints state ->
     let state, (me, record_info), gls = lp2inductive_entry ~depth hyps constraints state decl in
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
         let _, sigma = get_global_env_sigma state in
         let kinds, sp_projs =
           Record.declare_projections rsp ~kind:Decl_kinds.Definition
             (Evd.univ_entry ~poly:false sigma)
             (Names.Id.of_string "record")
             is_coercion is_implicit fields_as_relctx
         in
         Recordops.declare_structure
           (cstr, List.rev kinds, List.rev sp_projs);
     end;
     let state = grab_global_state state in
     state, !: (mind,0), gls)),
  DocAbove);

  LPDoc "Interactive module construction";

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  MLCode(Pred("coq.env.begin-module",
    In(id, "Name",
    In(unspec modtypath, "ModTyPath",
    Full "Starts a module, the modtype can be unspecified *E*")),
  (fun name mp ~depth _ _ state ->
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
     state, (), [])),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  MLCode(Pred("coq.env.end-module",
    Out(modpath, "ModPath",
    Full "end the current module that becomes known as ModPath *E*"),
  (fun _ ~depth _ _ state ->
     let mp = Declaremods.end_module () in
     let state = grab_global_state state in
     state, !: mp, [])),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  MLCode(Pred("coq.env.begin-module-type",
    In(id, "Name",
    Full "Starts a module type *E*"),
  (fun id ~depth _ _ state ->
     let id = Id.of_string id in
     let _mp =
       Declaremods.start_modtype Modintern.interp_module_ast id [] [] in
     let state = grab_global_state state in
      state, (), [])),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  MLCode(Pred("coq.env.end-module-type",
    Out(modtypath, "ModTyPath",
    Full "end the current module type that becomes known as ModPath *E*"),
  (fun _ ~depth _ _ state ->
     let mp = Declaremods.end_modtype () in
     let state = grab_global_state state in
     state, !: mp, [])),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  MLCode(Pred("coq.env.include-module",
    In(modpath, "ModPath",
    Full "is like the vernacular Include *E*"),
  (fun mp ~depth _ _ state ->
     let fpath = match mp with
       | ModPath.MPdot(mp,l) ->
           Libnames.make_path (ModPath.dp mp) (Label.to_id l)
       | _ -> nYI "functors" in
     let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
     let i = CAst.make tname, Declaremods.DefaultInline in
     Declaremods.declare_include Modintern.interp_module_ast [i];
     let state = grab_global_state state in
     state, (), [])),
  DocAbove);

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  MLCode(Pred("coq.env.include-module-type",
    In(modtypath, "ModTyPath",
    Full "is like the vernacular Include *E*"),
  (fun mp ~depth _ _ state ->
     let fpath = Nametab.path_of_modtype mp in
     let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
     let i = CAst.make tname, Declaremods.DefaultInline in
     Declaremods.declare_include Modintern.interp_module_ast [i];
     let state = grab_global_state state in
     state, (), [])),
  DocAbove);

  LPDoc "-- Universes --------------------------------------------------------";

  MLData univ;

  MLData universe; 

  MLCode(Pred("coq.univ.print",
    Read "prints the set of universe constraints",
  (fun ~depth _ _ state ->
    let _, sigma = get_global_env_sigma state in
    let uc = Evd.evar_universe_context sigma in
    let uc = Termops.pr_evar_universe_context uc in
    Feedback.msg_info Pp.(str "Universe constraints: " ++ uc);
    ())),
  DocAbove);

  MLCode(Pred("coq.univ.leq",
    In(univ, "U1",
    In(univ, "U2",
    Full "constrains U1 <= U2")),
  (fun u1 u2 ~depth _ _ state ->
    add_universe_constraint state (constraint_leq u1 u2), (),[])),
  DocAbove);

  MLCode(Pred("coq.univ.eq",
    In(univ, "U1",
    In(univ, "U2",
    Full "constrains U1 = U2")),
  (fun u1 u2 ~depth _ _ state ->
    add_universe_constraint state (constraint_eq u1 u2),(), [])),
  DocAbove);

  MLCode(Pred("coq.univ.new",
    In(unspec (B.list id), "Names",
    Out(univ, "U",
    Full "fresh universe *E*")),
  (fun nl _ ~depth _ _ state ->
     if not (nl = Unspec || nl = Given []) then nYI "named universes";
     let state, u = mk_fresh_univ state in
     state, !: u, [])),
  DocAbove);

  MLCode(Pred("coq.univ.sup",
    In(univ, "U1",
    In(univ, "U2",
    Full "constrains U2 = U1 + 1")),
  (fun u1 u2 ~depth _ _ state ->
    univ_super state u1 u2, (), [])),
  DocAbove);

  MLCode(Pred("coq.univ.max",
    In(univ, "U1",
    In(univ, "U2",
    Out(univ, "U3",
    Full "constrains U3 = max U1 U2"))),
  (fun u1 u2 _ ~depth _ _ state ->
    let state, u3 = univ_max state u1 u2 in
    state, !: u3, [])),
  DocAbove);

  LPDoc "Very low level, don't use";

  MLCode(Pred("coq.univ.algebraic-max",
    In(univ, "U1",
    In(univ, "U2",
    Out(univ, "U3",
    Full "constrains U3 = Max(U1,U2) *E*"))),
  (fun u1 u2 _ ~depth _ _ state ->
    state, !: (mk_algebraic_max u1 u2), [])),
  DocAbove);

  MLCode(Pred("coq.univ.algebraic-sup",
    In(univ, "U1",
    Out(univ, "U2",
    Full "constrains U2 = Sup(U1) *E*")),
  (fun u1 _ ~depth _ _ state ->
    state, !: (mk_algebraic_super u1), [])),
  DocAbove);

  LPDoc "-- Databases (TC, CS, Coercions) ------------------------------------";

  MLData cs_pattern;
  MLData cs_instance;

  MLCode(Pred("coq.CS.declare-instance",
    In(gref, "GR",
    Full "declares GR as a canonical structure instance"),
  (fun gr ~depth _ _ state ->
     Recordops.declare_canonical_structure gr;
     let state = grab_global_state state in
     state, (), [])),
  DocAbove);

  MLCode(Pred("coq.CS.db",
    Out(B.list cs_instance, "Db",
    Easy "reads all instances"),
  (fun _ ~depth ->
     !: (Recordops.canonical_projections ()))),
  DocAbove);

  MLData tc_instance;

  MLCode(Pred("coq.TC.declare-instance",
    In(gref, "GR",
    In(B.int,  "Priority",
    In(flag "@global?", "Global",
    Full "declare GR as a Global type class instance with Priority"))),
  (fun gr priority global ~depth _ _ state ->
     let global = global = Given true in
     let hint_priority = Some priority in
     let qualid =
       Nametab.shortest_qualid_of_global Names.Id.Set.empty gr in
     Classes.existing_instance global qualid
          (Some { Hints.empty_hint_info with Typeclasses.hint_priority });
     let state = grab_global_state state in
     state, (), [])),
  DocAbove);

  MLCode(Pred("coq.TC.db",
    Out(B.list tc_instance, "Db",
    Easy "reads all instances"),
  (fun _ ~depth -> !: (Typeclasses.all_instances ()))),
  DocAbove);

  MLCode(Pred("coq.TC.db-for",
    In(gref, "GR",
    Out(B.list tc_instance, "Db",
    Read "reads all instances of the given class GR")),
  (fun gr _ ~depth _ _ state ->
    !: (Typeclasses.instances gr))),
  DocAbove);

  MLCode(Pred("coq.TC.class?",
    In(gref, "GR",
    Easy "checks if GR is a class"),
  (fun gr ~depth ->
     if Typeclasses.is_class gr then () else raise Pr.No_clause)),
  DocAbove);

  MLData class_;
  MLData coercion;

  MLCode(Pred("coq.coercion.declare",
    In(coercion, "C",
    In(flag "@global?", "Global",
    Full ("declares C = (coercion GR _ From To) as a coercion From >-> To. "))),
  (fun (gr, _, source, target) global ~depth _ _ state ->
     let local = not (global = Given true) in
     let poly = false in
     Class.try_add_new_coercion_with_target gr ~local poly ~source ~target;
     let state = grab_global_state state in
     state, (), [])),
  DocAbove);

  MLCode(Pred("coq.coercion.db",
    Out(B.list coercion, "L",
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
    Out(B.list (Elpi.Builtin.pair gref B.int), "L",
    Easy ("reads all declared coercions")))),
  (fun source target _ ~depth ->
    let source,_ = Classops.class_info source in
    let target,_ = Classops.class_info target in
    let path = Classops.lookup_path_between_class (source,target) in
    let coercions = path |> List.map (fun c ->
     c.Classops.coe_value, c.Classops.coe_param) in
   !: coercions)),
  DocAbove);

  LPDoc "-- Coq's pretyper ---------------------------------------------------";

  MLCode(Pred("coq.sigma.print",
    Read "Prints Coq's Evarmap and the mapping to/from Elpi's unification variables",
    (fun ~depth hyps constraints state ->
      let state, env, sigma, coq_proof_ctx_names, _ = get_current_env_sigma ~depth hyps constraints state in
      Feedback.msg_info Pp.(
        str (Format.asprintf "%a" API.Pp.constraints constraints) ++ spc () ++
        str (show_engine state));
      ())),
  DocAbove);

  MLCode(Pred("coq.typecheck",
    In(term,  "T",
    Out(term, "Ty",
    Full ("typchecks a closed term (no holes, no context). This "^
          "limitation shall be lifted in the future. Inferred universe "^
          "constraints are put in the constraint store"))),
  (fun t _ ~depth hyps constraints state ->
     try
       let state, env, sigma, coq_proof_ctx_names, gls = get_current_env_sigma ~depth hyps constraints state in
       let sigma, ty = Typing.type_of env sigma t in
       let state, assignments = set_current_sigma ~depth state sigma in
       state, !: ty, gls @ assignments
     with Pretype_errors.PretypeError _ -> raise Pr.No_clause)),
  DocAbove);

  MLCode(Pred("coq.elaborate",
    In(term,  "T",
    Out(term,  "ETy",
    Out(term,  "E",
    Full ("elabotares terms that can contain \"hole\".  It is able to "^
          "work in a proof and hypothetical context, as long as all bound "^
          "variables are accompanied by a decl or def hypothesis. "^
          "Limitation: the resulting term has to be evar free (no "^
          "unresolved holes), shall be lifted in the future")))),
  (fun t _ _ ~depth hyps constraints state ->
     let state, env, sigma, coq_proof_ctx_names, gls = get_current_env_sigma ~depth hyps constraints state in
     let gt =
       (* To avoid turning named universes into unnamed ones *)
       Flags.with_option Constrextern.print_universes
         (Detyping.detype Detyping.Now false Id.Set.empty env sigma) t in
     let gt =
       let c, _ = EConstr.destConst sigma (in_coq_hole ()) in
       let rec map x = match DAst.get x with
         | GRef(Globnames.ConstRef x,None)
           when Constant.equal c x ->
              mkGHole
         | _ -> Glob_ops.map_glob_constr map x in
       map gt in
     let sigma, uj_val, uj_type =
       Pretyping.understand_tcc_ty env sigma gt in
     let state, assignments = set_current_sigma ~depth state sigma in
     state, !: uj_type +! uj_val, gls @ assignments)),
  DocAbove);

  LPDoc "-- Coq's tactics --------------------------------------------";

  MLCode(Pred("coq.ltac1.call",
    In(B.string, "Tac",
    In(B.list term,  "Args",
    In(raw_goal, "G",
    Out(B.list raw_goal,"GL",
    Full "Calls Ltac1 tactic named Tac with arguments Args on goal G")))),
    (fun tac_name tac_args goal _ ~depth hyps constraints state ->
       let open Ltac_plugin in
       let state, env, sigma, coq_proof_ctx_names, gls1 = get_current_env_sigma ~depth hyps constraints state in
       let tactic =
         let ist, args =
           List.fold_right (fun t (ist,args) ->
             let arg = Tacinterp.Value.of_constr t in
             let arg_id = Id.of_string (Printf.sprintf "elpi_arg_%d" (List.length args)) in
             let garg = DAst.make @@ Glob_term.GVar arg_id, None in
             let targ = Tacexpr.TacGeneric Genarg.(in_gen (glbwit Stdarg.wit_open_constr) garg) in
             let ist = { ist with Tacinterp.lfun = Id.Map.add arg_id arg ist.Tacinterp.lfun } in
             ist, targ :: args)
             tac_args (Tacinterp.default_ist (), []) in
         let tac_name = Tacenv.locate_tactic (Libnames.qualid_of_string tac_name) in
         let tacref = Locus.ArgArg (Loc.tag @@ tac_name) in  
         let tacexpr = Tacexpr.TacCall (CAst.make @@ (tacref, args)) in
         Tacinterp.eval_tactic_ist ist (Tacexpr.TacArg (CAst.make @@ tacexpr)) in
       let goal =
         match get_goal_ref ~depth constraints state goal with
         | None -> raise CP.(TypeErr (TyName"goal",depth,goal))
         | Some k -> k in
       let subgoals, sigma =
         let open Proofview in let open Notations in
         let focused_tac =
           Unsafe.tclSETGOALS [with_empty_state goal] <*> tactic in
         let _, pv = init sigma [] in
         let (), pv, _, _ =
           apply ~name:(Id.of_string "elpi") ~poly:false env focused_tac pv in
         proofview pv in
       let state, assignments = set_current_sigma ~depth state sigma in
       let state, subgoals, gls2 =
         API.Utils.map_acc (embed_goal ~depth) state subgoals in
       state, !: subgoals, gls1 @ assignments @ gls2
      )),
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
     | _ -> err Pp.(str "coq.name-suffix: suffix is not int|string|@name"))),
  DocAbove);

  MLCode(Pred("coq.string->name",
    In(B.string, "Hint",
    Out(name,  "Name",
    Easy "creates a name hint")),
  (fun s _ ~depth -> !: (Name.mk_name (Id.of_string s)))),
  DocAbove);

  MLCode(Pred("coq.gr->id",
    In(gref, "GR",
    Out(id, "Id",
    Read ("extracts the label (last component of a full kernel name). "^
          "Accepts also as @id in input, in this case it is the identity"))),
  (fun gr _ ~depth h c state ->
    let open Globnames in
    match gr with
    | VarRef v ->
        !: (Id.to_string v)
    | ConstRef c ->
        !: (Id.to_string (Label.to_id (Constant.label c)))
    | IndRef (i,0) ->
        let open Declarations in
        let env, sigma = get_global_env_sigma state in
        let { mind_packets } = Environ.lookup_mind i env in
        !: (Id.to_string (mind_packets.(0).mind_typename))
    | ConstructRef ((i,0),j) ->
        let open Declarations in
        let env, sigma = get_global_env_sigma state in
        let { mind_packets } = Environ.lookup_mind i env in
        !: (Id.to_string (mind_packets.(0).mind_consnames.(j-1)))
    | IndRef _  | ConstructRef _ ->
          nYI "mutual inductive (make-derived...)")),
   DocAbove);

  MLCode(Pred("coq.gr->string",
    In(gref, "GR",
    Out(B.string, "FullPath",
    Read "extract the full kernel name. GR can be a @gref or @id")),
  (fun gr _ ~depth h c state ->
    let open Globnames in
    match gr with
    | VarRef v -> !: (Id.to_string v)
    | ConstRef c -> !: (Constant.to_string c)
    | IndRef (i,0) -> !: (MutInd.to_string i)
    | ConstructRef ((i,0),j) ->
        let env, sigma = get_global_env_sigma state in
        let open Declarations in
        let { mind_packets } = Environ.lookup_mind i env in
        let klbl = Id.to_string (mind_packets.(0).mind_consnames.(j-1)) in
        !: (MutInd.to_string i^"."^klbl)
    | IndRef _  | ConstructRef _ ->
          nYI "mutual inductive (make-derived...)")),
  DocAbove);

  MLCode(Pred("coq.term->string",
    In(raw_term,"T",
    Out(B.string, "S",
    Full("prints a term T to a string S using Coq's pretty printer"))),
  (fun t _ ~depth hyps constraints state ->
     let state, t, _gls =
       lp2constr ~tolerate_undef_evar:true ~depth hyps constraints state t in
     let state, env, sigma, coq_proof_ctx_names, gls = get_current_env_sigma ~depth hyps constraints state in
     let s = Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma t) in
     state, !: s, gls)),
  DocAbove);

  LPDoc "-- Access to Elpi's data --------------------------------------------";

   (* Self modification *)
  MLData clause;
  MLData grafting;

  MLCode(Pred("coq.elpi.accumulate",
    In(id, "DbName",
    In(clause, "Clause",
    Full ("Declare that, once the program is over, the given clause has to "^
          "be added to the given db (see Elpi Db)" ))),
  (fun dbname (name,graft,clause) ~depth _ _ state ->
     let loc = API.Ast.Loc.initial "(elpi.add_clause)" in
     CS.update clauses_for_later state (fun l ->
        (dbname,API.Utils.clause_of_term ?name ?graft ~depth loc clause) :: l), (), [])),
  DocAbove);

  ]
;;



