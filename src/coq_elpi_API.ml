(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi_API
module E = API.Extend.Data
module U = API.Extend.Utils
module CS = API.Extend.CustomConstraint
module CP = API.Extend.CustomPredicate
module P = API.Extend.Pp

module G = Globnames

open Names
open Glob_term

open Coq_elpi_utils
open Coq_elpi_HOAS

open API.Data

(* ******************** Constraints ************************************** *)

(* Wrappers *)

let assert_command state name =
  if not (command_mode state) then
    err Pp.(str("API " ^ name ^ " is not available in tactics"))

let add_universe_constraint csts u1 x u2 =
  let open Universes in
  let u1, u2 = univout u1, univout u2 in
  try add_constraints csts (Constraints.singleton (u1,x,u2))
  with
  | Univ.UniverseInconsistency p ->
      Feedback.msg_debug
        (Univ.explain_universe_inconsistency pr_with_global_universes p);
      raise CP.No_clause
  | Evd.UniversesDiffer | UState.UniversesDiffer ->
      Feedback.msg_debug Pp.(str"UniversesDiffer");
      raise CP.No_clause

let mk_fresh_univ csts =
  let csts, v = new_univ csts in
  csts, univin v
  
let mk_algebraic_super x = univin (Univ.super (univout x))
let mk_algebraic_max x y = univin (Univ.Universe.sup (univout x) (univout y))

(* Utils *)

(* I don't want the user to even know that algebraic universes exist *)
let purge_algebraic_univs csts t =
  (* no map_fold iterator :-/ *)      
  let csts = ref csts in
  let rec aux t =
    match Constr.kind t with
    | Constr.Sort (Sorts.Type u) when not (Univ.Universe.is_level u) ->
        let new_csts, v = mk_fresh_univ !csts in
        csts := add_universe_constraint new_csts (univin u) Universes.ULe v;
        Constr.mkSort (Sorts.Type (univout v))
    | _ -> Term.map_constr aux t in
  let t = aux t in
  !csts, t

let univ_super csts u =
  let csts, v = mk_fresh_univ csts in
  let csts, u =
    let x = univout u in
    if Univ.Universe.is_level x then csts, u
    else 
      let csts, w = mk_fresh_univ csts in
      add_universe_constraint csts u Universes.ULe w, w in
  let csts =
    add_universe_constraint csts (mk_algebraic_super u) Universes.ULe v in
  csts, v

let univ_max csts u1 u2 =
  let csts, v = mk_fresh_univ csts in
  let csts =
    add_universe_constraint csts (mk_algebraic_max u1 u2) Universes.ULe v in
  csts, v

let constr2lp ?proof_ctx csts depth t =
  let csts, t = purge_algebraic_univs csts t in
  constr2lp csts ?proof_ctx ~depth t

let type_of_global_in_context csts depth r = 
  let csts, ty = type_of_global csts r in
  constr2lp csts depth ty

let normalize_restrict_univs csts u = normalize_univs (restrict_univs csts u)

let assign a b = E.App (E.Constants.eqc, a, [b])

(* pre-process arguments of a custom predicate turning UVars into fresh
 * universes *)
let rec to_univ n csts gs us = function
  | [] -> csts, List.rev gs, List.rev us
  | (E.UVar _ | E.AppUVar _) as x :: xs when n > 0 ->
      let csts, u = mk_fresh_univ csts in
      let u = E.CData u in
      let g = assign x u in
      to_univ (n-1) csts (g::gs) (u::us) xs
  | x :: xs -> to_univ (n-1) csts gs (x::us) xs

let clauses_for_later =
  CS.declare ~name:"coq-elpi:clauses_for_later"
    ~init:(CS.Other (fun () -> []))
    ~pp:(fun fmt l ->
       List.iter (fun (dbname, code) ->
         Format.fprintf fmt "db:%s code:%a\n" dbname
            Elpi_API.Pp.Ast.program code) l)
;;

(* ***************** $custom Coq predicates  ***************************** *)
          
let is_bool x = x = in_elpi_tt || x = in_elpi_ff

let to_coercion_class err depth = function
  | E.App(c,E.CData gr,[]) when is_globalc c && isgr gr ->
       Class.class_of_global (grout gr)
  | x when is_prod ~depth x -> Classops.CL_FUN
  | x when is_sort ~depth x -> Classops.CL_SORT
  | x -> err ()

let error pp api args nexpected expected () =
 err Pp.(str"Illtyped call to Coq API " ++ str api ++ spc () ++
         str"got " ++ int (List.length args) ++ str" arguments, namely: " ++
         prlist_with_sep (fun () -> str", ") str (List.map pp args) ++
         str" but " ++ int nexpected ++
         str " arguments are expected: " ++ str expected)

type error = { error : 'a. int -> string -> unit -> 'a }
type pp = Format.formatter -> E.term -> unit

type builtin =
  | Pure of (depth:int -> error:error -> kind:(E.term -> E.term) -> pp:pp -> E.term list -> E.term list)
  | Constraints of (depth:int -> error:error -> kind:(E.term -> E.term) -> pp:pp -> CS.t -> E.term list -> E.term list * E.custom_constraints)
  | Tactic of (depth:int -> error:error -> kind:(E.term -> E.term) -> pp:pp -> Environ.env -> Evd.evar_map -> proof_ctx -> CS.t -> E.term list -> E.term list * E.custom_constraints)
  | Global of (depth:int -> error:error -> kind:(E.term -> E.term) -> pp:pp -> CS.t -> E.term list -> E.term list * E.custom_constraints)

let declare_api (name, f) =
  let name = "coq." ^ name in
  CP.declare_full name (fun ~depth hyps solution args ->
    let args = List.map (kind ~depth) args in
    let pp = P.term depth [] 0 [||] in
    match f with
    | Pure f ->
        f ~depth ~error:{ error = error (pp2string pp) name args }
          ~kind:(kind ~depth)
          ~pp args, solution.custom_constraints
    | Constraints f ->
        f ~depth ~error:{ error = error (pp2string pp) name args }
          ~kind:(kind ~depth)
          ~pp solution.custom_constraints args
    | Tactic f ->
        let csts, env, evd, proof_ctx = get_current_env_evd hyps solution in
        f ~depth ~error:{ error = error (pp2string pp) name args }
          ~kind:(kind ~depth)
          ~pp env evd proof_ctx csts args
    | Global f ->
        assert_command solution.custom_constraints name;
        let goal, csts =
        f ~depth ~error:{ error = error (pp2string pp) name args }
          ~kind:(kind ~depth)
          ~pp solution.custom_constraints args in
        let csts = grab_global_env csts in
        goal, csts)
;;

let () = List.iter declare_api [

  (* Print (debugging) **************************************************** *)
  "say", Pure (fun ~depth ~error ~kind ~pp args ->
    Feedback.msg_info Pp.(str (pp2string (P.list ~boxed:true pp " ") args));
    []);
  "warn", Pure (fun ~depth ~error ~kind ~pp args ->
    Feedback.msg_warning Pp.(str (pp2string (P.list ~boxed:true pp " ") args));
    []);

  (* Nametab access ******************************************************* *)
  "locate", Pure (fun ~depth ~error ~kind ~pp args ->
    let error = error.error 2 "string out" in
    match args with
    | [E.CData c;ret] when E.C.is_string c ->
        let qualid = Libnames.qualid_of_string (E.C.to_string c) in
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
        [assign (in_elpi_gr gr) ret]
    | _ -> error ());

  "locate-module",Pure (fun ~depth ~error ~kind ~pp args ->
    let error = error.error 2 "string out" in
    match args with
    | [E.CData s;ret] when E.C.is_string s ->
        let qualid = Libnames.qualid_of_string (E.C.to_string s) in
        let mp =
          try Nametab.locate_module qualid
          with Not_found ->
            err Pp.(str "Module not found: " ++ Libnames.pr_qualid qualid) in
        [assign (in_elpi_modpath ~ty:false mp) ret]
    | _ -> error ());

  "locate-module-type",Pure (fun ~depth ~error ~kind ~pp args ->
    let error = error.error 2 "string out" in
    match args with
    | [E.CData s;ret] when E.C.is_string s ->
        let qualid = Libnames.qualid_of_string (E.C.to_string s) in
        let mp =
          try Nametab.locate_modtype qualid
          with Not_found ->
            err Pp.(str "Module type not found: " ++ Libnames.pr_qualid qualid) in
        [assign (in_elpi_modpath ~ty:true mp) ret]
    | _ -> error ());

  (* Kernel's environment read access ************************************* *)

  (* TODO: if the ret_* term is Discard, the corresponding term should not
   * be generated *)

  "env.const", Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 3 "const-reference out out out" in
    match args with
    | [E.CData gr; ret_bo; ret_ty] when isgr gr ->
        let gr = grout gr in
        begin match gr with
        | G.ConstRef c ->
             let csts, ty = type_of_global_in_context csts depth gr in
             let csts, bo = 
               let opaque = Declareops.is_opaque (Global.lookup_constant c) in
               if opaque then csts, in_elpi_implicit
               else match Global.body_of_constant c with
                 | Some bo -> constr2lp csts depth bo
                 | None -> csts, in_elpi_implicit in
             [ assign ty ret_ty; assign bo ret_bo ], csts
        | G.VarRef v ->
             let csts, ty = type_of_global_in_context csts depth gr in
             let csts, bo = match Global.lookup_named v with
               | Context.Named.Declaration.LocalDef(_,bo,_) ->
                   constr2lp csts depth bo
               | Context.Named.Declaration.LocalAssum _ ->
                   csts, in_elpi_implicit in
             [ assign ty ret_ty; assign bo ret_bo ], csts
        | _ -> error () end
    | _ -> error ());

  "env.const-opaque?", Pure (fun ~depth ~error ~kind ~pp args ->
    let error = error.error 1 "const-reference" in
    match args with
    | [E.CData gr] when isgr gr ->
        let gr = grout gr in
        begin match gr with
        | G.ConstRef c ->
             let open Declareops in
             let cb = Global.lookup_constant c in
             if is_opaque cb || not(constant_has_body cb)  then []
             else raise CP.No_clause
        | G.VarRef v ->
             begin match Global.lookup_named v with
             | Context.Named.Declaration.LocalDef _ -> raise CP.No_clause
             | Context.Named.Declaration.LocalAssum _ -> [] end
        | _ -> error () end
    | _ -> error ());

  "env.const-body", Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 2 "const-reference out" in
    match args with
    | [E.CData gr; ret_bo] when isgr gr ->
        let gr = grout gr in
        begin match gr with
        | G.ConstRef c ->
             let csts, bo = 
               match Global.body_of_constant c with
               | Some bo -> constr2lp csts depth bo
               | None -> csts, in_elpi_implicit in
             [ assign bo ret_bo ], csts
        | G.VarRef v ->
             let csts, bo = match Global.lookup_named v with
               | Context.Named.Declaration.LocalDef(_,bo,_) ->
                   constr2lp csts depth bo
               | Context.Named.Declaration.LocalAssum _ ->
                   csts, in_elpi_implicit in
             [ assign bo ret_bo ], csts
        | _ -> error () end
    | _ -> error ());

  "env.indt", Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 7 "indt-reference out^6" in
    match args with
    | [E.CData gr;ret_co;ret_lno;ret_luno;ret_ty;ret_kn;ret_kt] when isgr gr ->
        let gr = grout gr in
        begin match gr with
        | G.IndRef i ->
            let open Declarations in
            let mind, indbo as ind = Global.lookup_inductive i in
            if Array.length mind.mind_packets <> 1 then
              nYI "API(env) mutual inductive";
            if Declareops.inductive_is_polymorphic mind then
              nYI "API(env) poly mutual inductive";
            if mind.mind_finite = Decl_kinds.CoFinite then
              nYI "API(env) co-inductive";
             
            let co  = in_elpi_tt in
            let lno = E.C.of_int (mind.mind_nparams) in
            let luno = E.C.of_int (mind.mind_nparams_rec) in
            let ty =
              Inductive.type_of_inductive
                (Global.env()) (ind,Univ.Instance.empty) in
            let csts, ty = constr2lp csts depth ty in
            let kt =
              Inductive.type_of_constructors (i,Univ.Instance.empty) ind in
            let kn =
              CList.init
                Declarations.(indbo.mind_nb_constant + indbo.mind_nb_args)
                (fun k -> G.ConstructRef (i,k+1)) in
            let csts, kt =
              List.fold_right (fun t (csts,acc) ->
                let csts, t = constr2lp csts depth t in
                csts, t :: acc)
              (Array.to_list kt) (csts,[]) in

             [ 
              assign co ret_co;
              assign lno ret_lno;
              assign luno ret_luno;
              assign ty ret_ty;
              assign (U.list_to_lp_list (List.map in_elpi_gr kn)) ret_kn;
              assign (U.list_to_lp_list kt) ret_kt;
             ], csts
        | _ -> error () end
    | _ -> error ());

  "env.indc", Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 5 "indc-reference out^3" in
    match args with
    | [E.CData gr;ret_lno;ret_luno;ret_ki;ret_ty] when isgr gr ->
        let gr = grout gr in
        begin match gr with
        | G.ConstructRef (i,k as kon) ->
            let open Declarations in
            let mind, indbo as ind = Global.lookup_inductive i in
            let lno = E.C.of_int (mind.mind_nparams) in
            let luno = E.C.of_int (mind.mind_nparams_rec) in
            let ty =
              Inductive.type_of_constructor (kon,Univ.Instance.empty) ind in
            let csts, ty = constr2lp csts depth ty in
            [ 
              assign lno ret_lno;
              assign luno ret_luno;
              assign (E.C.of_int (k-1)) ret_ki;
              assign ty ret_ty;
            ], csts

        | _ -> error () end
    | _ -> error ());

  "env.typeof-gr", Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 2 "global-reference out" in
    match args with
    | [E.CData gr;ret_ty] when isgr gr ->
        let gr = grout gr in
        let csts, ty = type_of_global_in_context csts depth gr in
        [ assign ty ret_ty ], csts
    | _ -> error ());

  "env.module", Pure (fun ~depth ~error ~kind ~pp args ->
    let error = error.error 2 "@modpath out" in
    match args with
    | [mp;ret] when is_modpath mp ->
        let mp = in_coq_modpath mp in
        let me = Global.lookup_module mp in
        [assign (in_elpi_module me) ret]
    | _ -> error ());

  "env.module-type", Pure (fun ~depth ~error ~kind ~pp args ->
    let error = error.error 2 "@modtypath out" in
    match args with
    | [mp;ret] when is_modtypath mp ->
        let mp = in_coq_modpath mp in
        let me = Global.lookup_modtype mp in
        [assign (in_elpi_module_type me) ret]
    | _ -> error ());

  (* Kernel's environment write access ************************************ *)
  "env.add-const", Global (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 5 "string term term opaque? out" in
    let is_unspecified = is_unspecified ~depth in
    match args with
    | [E.CData gr;bo;ty;opaque;ret_gr] when E.C.is_string gr ->
        if is_unspecified bo then begin
          if is_unspecified ty then
            err Pp.(str "coq-add-const: both Type and Body are unspecified");
          let csts, ty = lp2constr [] ~depth csts ty in
          let used = Univops.universes_of_constr ty in
          let csts = normalize_restrict_univs csts used in
          let _env, evd = get_env_evd csts in
          let dk = Decl_kinds.(Global, false, Logical) in
          let gr, _, _ =
            Command.declare_assumption false dk
              (ty, Evd.universe_context_set evd)
              [] [] false Vernacexpr.NoInline
              (None, Id.of_string (E.C.to_string gr)) in 
          [assign (in_elpi_gr gr) ret_gr], csts
        end else
          let csts, ty, used_ty =
            if is_unspecified ty then csts, None, Univ.LSet.empty
            else
              let csts, ty = lp2constr [] ~depth csts ty in
              csts, Some ty, Univops.universes_of_constr ty in
          let csts, bo = lp2constr [] csts ~depth bo in
          let transparent = is_unspecified opaque || opaque = in_elpi_ff in
          let used =
            Univ.LSet.union used_ty (Univops.universes_of_constr bo) in
          let csts = normalize_restrict_univs csts used in
          let env, evd = get_env_evd csts in
          let ce = Entries.({
            const_entry_opaque = not transparent;
            const_entry_body = Future.from_val
              ((bo, Univ.ContextSet.empty),
               Safe_typing.empty_private_constants) ;
            const_entry_secctx = None;
            const_entry_feedback = None;
            const_entry_type = ty;
            const_entry_polymorphic = false;
            const_entry_universes = snd (Evd.universe_context evd);
            const_entry_inline_code = false; }) in
          let dk = Decl_kinds.(Global, false, Definition) in
          let gr =
            DeclareDef.declare_definition
             (Id.of_string (E.C.to_string gr)) dk ce
             [] [] Lemmas.(mk_hook (fun _ x -> x)) in
          [assign (in_elpi_gr gr) ret_gr], csts
    | _ -> error ());

  "env.add-indt", Global (fun  ~depth ~error ~kind ~pp csts args ->
    let error = error.error 2 "indt-decl out" in
    match args with
    | [decl;ret_gr] ->
        let csts, me, record_info = lp2inductive_entry ~depth csts decl in
        let mind =
          Command.declare_mutual_inductive_with_eliminations me [] [] in
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
            let kinds, sp_projs =
              Record.declare_projections rsp ~kind:Decl_kinds.Definition
                (Names.Id.of_string "record")
                is_coercion is_implicit fields_as_relctx
            in
            Recordops.declare_structure
              (rsp,cstr,List.rev kinds,List.rev sp_projs);
        end;
        [assign ret_gr (in_elpi_gr (Globnames.IndRef(mind,0)))], csts
    | _ -> error ());

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  "env.begin-module", Global (fun  ~depth ~error ~kind ~pp csts args ->
    let error = error.error 2 "string @modtypath" in
    let is_unspecified = is_unspecified ~depth in
    match args with
    | [E.CData name; mp]
      when E.C.is_string name && (is_unspecified mp || is_modtypath mp) -> 
         let ty =
           if is_unspecified mp then Vernacexpr.Check []
           else
             let fpath = Nametab.path_of_modtype (in_coq_modpath mp) in
             let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
             Vernacexpr.(Enforce (CAst.make tname, DefaultInline)) in
         let id = Id.of_string (E.C.to_string name) in
         let _mp = Declaremods.start_module Modintern.interp_module_ast
           None id [] ty in
         [], csts
    | _ -> error ());

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  "env.end-module", Global (fun  ~depth ~error ~kind ~pp csts args ->
    let error = error.error 1 "out" in
    match args with
    | [ret_mp] ->
         let mp = Declaremods.end_module () in
         [assign (in_elpi_modpath ~ty:false mp) ret_mp], csts
    | _ -> error ());

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  "env.begin-module-type", Global (fun  ~depth ~error ~kind ~pp csts args ->
    let error = error.error 1 "string" in
    match args with
    | [E.CData name] when E.C.is_string name -> 
         let id = Id.of_string (E.C.to_string name) in
         let _mp =
           Declaremods.start_modtype Modintern.interp_module_ast id [] [] in
         [], csts
    | _ -> error ());

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  "env.end-module-type", Global (fun  ~depth ~error ~kind ~pp csts args ->
    let error = error.error 1 "out" in
    match args with
    | [ret_mp] ->
         let mp = Declaremods.end_modtype () in
         [assign (in_elpi_modpath ~ty:true mp) ret_mp], csts
    | _ -> error ());

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  "env.include-module", Global (fun  ~depth ~error ~kind ~pp csts args ->
    let error = error.error 1 "@modtypath" in
    match args with
    | [mp] when is_modpath mp ->
        let mp = in_coq_modpath mp in
        let fpath = match mp with
          | ModPath.MPdot(mp,l) ->
              Libnames.make_path (ModPath.dp mp) (Label.to_id l)
          | _ -> nYI "functors" in
        let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
        let i = CAst.make tname, Vernacexpr.DefaultInline in
        Declaremods.declare_include Modintern.interp_module_ast [i];
        [], csts 
    | _ -> error());

  (* XXX When Coq's API allows it, call vernacentries directly *) 
  "env.include-module-type", Global (fun  ~depth ~error ~kind ~pp csts args ->
    let error = error.error 1 "@modtypath" in
    match args with
    | [mp] when is_modtypath mp ->
        let fpath = Nametab.path_of_modtype (in_coq_modpath mp) in
        let tname = Constrexpr.CMident (Libnames.qualid_of_path fpath) in
        let i = CAst.make tname, Vernacexpr.DefaultInline in
        Declaremods.declare_include Modintern.interp_module_ast [i];
        [], csts 
    | _ -> error());


  (* DBs write access ***************************************************** *)
  "TC.declare-instance", Global (fun ~depth ~error ~kind ~pp cc args ->
    let error = error.error 3 "@gref int bool" in
    match args with
    | [E.CData gr;E.CData priority;global]
      when isgr gr && E.C.is_int priority && is_bool global ->
        let reference = grout gr in
        let global = if global = in_elpi_tt then true else false in
        let hint_priority = Some (E.C.to_int priority) in
        let qualid =
          Nametab.shortest_qualid_of_global Names.Id.Set.empty reference in
        Classes.existing_instance global (Libnames.Qualid (None, qualid))
          (Some { Hints.empty_hint_info with Vernacexpr.hint_priority });
        [], cc
    | _ -> error ());

  "CS.declare-instance", Global (fun ~depth ~error ~kind ~pp cc args ->
    let error = error.error 1 "@gref" in
    match args with
    | [E.CData gr] when isgr gr ->
        let gr = grout gr in
        Recordops.declare_canonical_structure gr;
        [], cc
    | _ -> error ());

  "coercion.declare", Global (fun ~depth ~error ~kind ~pp cc args ->
    let error = error.error 4 "@gref class class bool" in
    match args with
    | [E.CData gr;from;to_;global] when isgr gr ->
        let gr = grout gr in
        let local = if global = in_elpi_tt then false else true in
        let poly = false in
        let source = to_coercion_class error depth from in
        let target = to_coercion_class error depth to_ in
        Class.try_add_new_coercion_with_target gr ~local poly ~source ~target;
        [], cc
    | _ -> error ());

  (* DBs read access ****************************************************** *)

  "CS.db", Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 1 "out" in
    match args with
    | [db] ->
        let l = Recordops.canonical_projections () in
        let csts, l = CList.fold_map (canonical_solution2lp ~depth) csts l in
        [ assign (U.list_to_lp_list l) db ], csts         
    | _ -> error ());

  "TC.db", Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 1 "out" in
    match args with
    | [db] ->
        let l = Typeclasses.all_instances () in
        let csts, l = CList.fold_map (instance2lp ~depth) csts l in
        [ assign (U.list_to_lp_list l) db ], csts         
    | _ -> error ());

  "TC.db-for", Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 1 "out" in
    match args with
    | [E.CData gr; db] when isgr gr ->
        let l = Typeclasses.instances (grout gr) in
        let csts, l = CList.fold_map (instance2lp ~depth) csts l in
        [ assign (U.list_to_lp_list l) db ], csts         
    | _ -> error ());

  "TC.class?", Pure (fun ~depth ~error ~kind ~pp args ->
    let error = error.error 1 "@gref" in
    match args with
    | [E.CData gr] when isgr gr ->
       if Typeclasses.is_class (grout gr) then [] else raise CP.No_clause
    | _ -> error ());

  (* TODO: coercion-db *)

  (* Kernel's type checker ************************************************ *)
  "typecheck", Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 2 "term out" in
    match args with
    | [t;ret] ->
        begin try
          let csts, t = lp2constr [] ~depth csts t in
          let senv, evd = get_senv_evd csts in
          let j = Safe_typing.typing senv t in
          let csts, ty = constr2lp csts depth (Safe_typing.j_type j) in
          [assign ty ret], csts
        with Type_errors.TypeError _ -> raise CP.No_clause end
    | _ -> error ());
  
  (* Pretyper ************************************************************* *)
  "elaborate", Tactic(fun ~depth ~error ~kind ~pp env evd proof_ctx csts args ->
    let error = error.error 3 "term out out" in
    match args with
    | [t;ret_t;ret_ty] ->
                    (* TODO: ifa free variable is missing, print a nicer error *)
        let csts, t = lp2constr [] ~depth ~proof_ctx csts t in
        let gt =
          (* To avoid turning named universes into unnamed ones *)
          Flags.with_option Constrextern.print_universes
            (Detyping.detype false [] env evd) (EConstr.of_constr t) in
        let gt =
          let c, _ = Term.destConst (in_coq_hole ()) in
          let rec map = function
            | { CAst.v = GRef(Globnames.ConstRef x,None) }
              when Constant.equal c x ->
                 mkGHole
            | x -> Glob_ops.map_glob_constr map x in
          map gt in
        let evd = ref evd in
        let { Environ.uj_val; uj_type } =
          Pretyping.understand_judgment_tcc env evd gt in
        let csts = set_evd csts !evd in
        let csts, t  =
          constr2lp ~proof_ctx csts depth (EConstr.to_constr !evd uj_val)  in
        let csts, ty =
          constr2lp ~proof_ctx csts depth (EConstr.to_constr !evd uj_type) in
        let csts = normalize_univs csts in
        [assign t ret_t; assign ty ret_ty], csts

    | _ -> error ());

  (* Universe constraints ************************************************* *)
  "univ.print-constraints", Constraints (fun ~depth ~error ~kind ~pp csts _ ->
    let _, evd = get_env_evd csts in
    let uc = Evd.evar_universe_context evd in
    let uc = Termops.pr_evar_universe_context uc in
    Feedback.msg_info Pp.(str "Universe constraints: " ++ uc);
    [],csts);
  "univ.leq", Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 2 "@univ @univ" in
    let csts, assignments, args = to_univ 2 csts [] [] args in
    match args with
    | [E.CData u1;E.CData u2] when isuniv u1 && isuniv u2 ->
      assignments, add_universe_constraint csts u1 Universes.ULe u2
    | _ -> error ());
  "univ.eq", Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 2 "@univ @univ" in
    let csts, assignments, args = to_univ 2 csts [] [] args in
    match args with
    | [E.CData u1;E.CData u2] when isuniv u1 && isuniv u2 ->
      assignments, add_universe_constraint csts u1 Universes.UEq u2
    | _ -> error ());
  "univ.new", Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 2 "(list string) out" in
    match args with
    | [nl;out] ->
        let l = U.lp_list_to_list ~depth nl in
        if l <> [] then nYI "named universes";
        let csts, assignments, _args = to_univ 1 csts [] [] [out] in
        assignments, csts
    | _ -> error ());
  "univ.sup",Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 2 "@univ out" in
    let csts, assignments, args = to_univ 1 csts [] [] args in
    match args with
    | [E.CData u;out_super] when isuniv u ->
        let csts, u1 = univ_super csts u in
        assign (E.CData u1) out_super :: assignments, csts
    | _ -> error ());
  "univ.max",Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 3 "@univ @univ out" in
    let csts, assignments, args = to_univ 2 csts [] [] args in
    match args with
    | [E.CData u1;E.CData u2;out] when isuniv u1 && isuniv u2 ->
        let csts, u3 = univ_max csts u1 u2 in
        assign (E.CData u3) out :: assignments, csts
    | _ -> error ());
  "univ.algebraic-sup",Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 2 "@univ out" in
    let csts, assignments, args = to_univ 1 csts [] [] args in
    match args with
    | [E.CData u;out_super] when isuniv u ->
        assign (E.CData(mk_algebraic_super u)) out_super ::
        assignments, csts
    | _ -> error ());
  "univ.algebraic-max",Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 3 "@univ @univ out" in
    let csts, assignments, args = to_univ 2 csts [] [] args in
    match args with
    | [E.CData u1;E.CData u2;out] when isuniv u1 && isuniv u2 ->
         assign (E.CData(mk_algebraic_max u1 u2)) out ::
         assignments, csts
    | _ -> error ());

  (* Misc ***************************************************************** *)
  "error", Pure (fun ~depth ~error ~kind ~pp args ->
     match args with
     | [] -> error.error 1 "at least one argument" ()
     | l ->
         let msg = List.map (pp2string pp) l in
         err Pp.(str (String.concat " " msg)));

  "name-suffix", Pure (fun ~depth ~error ~kind ~pp args ->
     let error = error.error 3 "@name suffix out" in
     match args with
     | [n;E.CData i;ret]
       when is_coq_name n && E.C.(is_string i || is_int i || isname i) ->
         let s = Pp.string_of_ppcmds (Nameops.pr_name (in_coq_name n)) in
         let suffix =
           if E.C.is_string i then E.C.to_string i
           else if E.C.is_int i then string_of_int (E.C.to_int i)
           else Pp.string_of_ppcmds (Nameops.pr_name (nameout i)) in
         let s = s ^ suffix in
         [ assign ret (in_elpi_name (Name.mk_name (Id.of_string s))) ]
     | _ -> error ());

  "string->name", Pure (fun ~depth ~error ~kind ~pp args ->
     let error = error.error 2 "string out" in
     match args with
     | [E.CData s; ret_name] when E.C.is_string s ->
         let name = Name.mk_name (Id.of_string (E.C.to_string s)) in
         [assign (in_elpi_name name) ret_name]
     | _ -> error());

  "gr->id", Pure (fun ~depth ~error ~kind ~pp args ->
     let error = error.error 2 "(@gref|@id) out" in
     match args with
     | [E.CData id as x;ret_gr] when E.C.is_string id -> [assign x ret_gr]
     | [E.CData gr; ret_name] when isgr gr ->
          let open Globnames in
          let gr = grout gr in
          begin match gr with
          | VarRef v ->
              let n = Id.to_string v in
              [assign (E.C.of_string n) ret_name]
          | ConstRef c ->
              let n = Id.to_string (Label.to_id (Constant.label c)) in
              [assign (E.C.of_string n) ret_name]
          | IndRef (i,0) ->
              let open Declarations in
              let { mind_packets } = Environ.lookup_mind i (Global.env()) in
              let n = Id.to_string (mind_packets.(0).mind_typename) in
              [assign (E.C.of_string n) ret_name]
          | ConstructRef ((i,0),j) ->
              let open Declarations in
              let { mind_packets } = Environ.lookup_mind i (Global.env()) in
              let n = Id.to_string (mind_packets.(0).mind_consnames.(j-1)) in
              [assign (E.C.of_string n) ret_name]
          | IndRef _  | ConstructRef _ ->
               nYI "mutual inductive (make-derived...)" end
     | _ -> error());

  "gr->string", Pure (fun ~depth ~error ~kind ~pp args ->
     let error = error.error 2 "(@gref|string) out" in
     match args with
     | [E.CData s as t;ret_gr] when E.C.is_string s -> [assign t ret_gr]
     | [E.CData gr;ret_gr] when isgr gr ->
          let open Globnames in
          let gr = grout gr in
          begin match gr with
          | VarRef v ->
              [assign (E.C.of_string (Id.to_string v)) ret_gr]
          | ConstRef c ->
              [assign (E.C.of_string (Constant.to_string c)) ret_gr]
          | IndRef (i,0) ->
              [assign (E.C.of_string (MutInd.to_string i)) ret_gr]
          | ConstructRef ((i,0),j) ->
              let open Declarations in
              let { mind_packets } = Environ.lookup_mind i (Global.env()) in
              let klbl = Id.to_string (mind_packets.(0).mind_consnames.(j-1)) in
              [assign (E.C.of_string (MutInd.to_string i^"."^klbl)) ret_gr]
          | IndRef _  | ConstructRef _ ->
               nYI "mutual inductive (make-derived...)" end
     | _ -> error ());

   (* Self modification *)
  "elpi.accumulate", Global (fun ~depth ~error ~kind ~pp csts args ->
    let error = error.error 2 "@id prop" in
    match args with
    | [E.CData name;t] when E.C.is_string name ->
        let dbname = E.C.to_string name in
        let p = in_elpi_clause ~depth t in
        [], CS.update clauses_for_later csts (fun l -> (dbname,p) :: l)
    | _ -> error ());

  ]
;;

