(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module G = Globnames
module E = Elpi_API.Extend.Data
module U = Elpi_API.Extend.Utils
module CC = Elpi_API.Extend.CustomConstraint
module CP = Elpi_API.Extend.CustomPredicate
module P = Elpi_API.Extend.Pp
module C = Constr

open Names
open Glob_term

open Coq_elpi_utils
open Coq_elpi_HOAS

(* ******************** Constraints ************************************** *)

let pp_ucst fmt cs =
  Pp.pp_with fmt (Termops.pr_evar_universe_context cs)

let empty_ucst () = UState.make (Environ.universes (Global.env ()))

let univ_constraints : UState.t CC.constraint_type =
  CC.declare ~name:"Universe constraints"
    ~pp:pp_ucst ~empty:empty_ucst
;;

let cc_update_univ x f y = CC.update x univ_constraints (fun a -> f a y)
let cc_update_return_univ x f = CC.update_return x univ_constraints f

(* Wrappers *)

(* (s)env and evar_map with the current constraints *)
let get_env_evd c =
  let ustate = CC.read c univ_constraints in
  let ustate_cset = UState.context_set ustate in
  let env = Global.env () in
  Environ.push_context_set ustate_cset env, Evd.from_ctx ustate

let get_senv_evd c =
  let ustate = CC.read c univ_constraints in
  let ustate_cset = UState.context_set ustate in
  let senv = Global.safe_env () in
  Safe_typing.push_context_set true ustate_cset senv, Evd.from_ctx ustate

(* lp2constr turns (type X) into (type fresh-univ-variable), hence it needs
 * to see the constraints *)      
let lp2constr csts y =
  CC.update_return csts univ_constraints (fun csts -> lp2constr csts y)

let add_universe_constraint csts u1 x u2 =
  let u1, u2 = univout u1, univout u2 in
  let x = Universes.(Constraints.singleton (u1,x,u2)) in
  try cc_update_univ csts UState.add_universe_constraints x
  with Univ.UniverseInconsistency p ->
   Feedback.msg_debug
     (Univ.explain_universe_inconsistency Universes.pr_with_global_universes p);
   raise CP.No_clause

let mk_fresh_univ csts =
  let csts, v = cc_update_return_univ csts new_univ in
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

let constr2lp csts depth t =
  let csts, t = purge_algebraic_univs csts t in
  csts, constr2lp depth t

let type_of_global_in_context csts depth r = 
  let env, _ = get_env_evd csts in
  let ty, _u = Global.type_of_global_in_context env r in
  constr2lp csts depth ty

let normalize_csts csts used_set =
  CC.update csts univ_constraints
    (fun u -> UState.normalize (UState.restrict u used_set))

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

(* ***************** $custom Coq predicates  ***************************** *)

let error pp api args nexpected expected () =
 err Pp.(str"Illtyped call to Coq API " ++ str api ++ spc () ++
         str"got " ++ int (List.length args) ++ str" arguments, namely: " ++
         prlist_with_sep (fun () -> str", ") str (List.map pp args) ++
         str" but " ++ int nexpected ++
         str " arguments are expected: " ++ str expected)

let declare_api (name, f) =
  let name = "$coq-" ^ name in
  CP.declare_full name (fun ~depth ~env _s c args ->
    let args = List.map (kind ~depth) args in
    let pp = P.term depth [] 0 env in
    match f with
    | `Pure f ->
        f ~depth ~error:(error (pp2string pp) name args)
          ~kind:(kind ~depth)
          ~pp args, c
    | `Constraints f ->
        f ~depth ~error:(error (pp2string pp) name args)
          ~kind:(kind ~depth)
          ~pp c args)
;;

let () = List.iter declare_api [

  (* Print (debugging) **************************************************** *)
  "say", `Pure (fun ~depth ~error ~kind ~pp args ->
    Feedback.msg_info Pp.(str (pp2string (P.list ~boxed:true pp " ") args));
    []);
  "warn", `Pure (fun ~depth ~error ~kind ~pp args ->
    Feedback.msg_warning Pp.(str (pp2string (P.list ~boxed:true pp " ") args));
    []);

  (* Nametab access ******************************************************* *)
  "locate", `Pure (fun ~depth ~error ~kind ~pp args ->
    let error = error 2 "string out" in
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

  (* Kernel's environment read access ************************************* *)
  "env-const", `Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 3 "const-reference out out" in
    match args with
    | [E.CData gr; ret_bo; ret_ty] when isgr gr ->
        let gr = grout gr in
        begin match gr with
        | G.ConstRef c ->
             let csts, ty = type_of_global_in_context csts depth gr in
             let csts, bo = match Global.body_of_constant c with
               | Some bo -> constr2lp csts depth bo
               | None -> csts, in_elpi_axiom in
             [ assign ty ret_ty; assign bo ret_bo ], csts
        | G.VarRef v ->
             let csts, ty = type_of_global_in_context csts depth gr in
             let csts, bo = match Global.lookup_named v with
               | Context.Named.Declaration.LocalDef(_,bo,_) ->
                   constr2lp csts depth bo
               | Context.Named.Declaration.LocalAssum _ ->
                   csts, in_elpi_axiom in
             [ assign ty ret_ty; assign bo ret_bo ], csts
        | _ -> error () end
    | _ -> error ());

  "env-indt", `Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 7 "indt-reference out^6" in
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

  "env-indc", `Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 5 "indc-reference out^3" in
    match args with
    | [E.CData gr;ret_lno;ret_ki;ret_ty] when isgr gr ->
        let gr = grout gr in
        begin match gr with
        | G.ConstructRef (i,k as kon) ->
            let open Declarations in
            let mind, indbo as ind = Global.lookup_inductive i in
            let lno = E.C.of_int (mind.mind_nparams) in
            let ty =
              Inductive.type_of_constructor (kon,Univ.Instance.empty) ind in
            let csts, ty = constr2lp csts depth ty in
            [ 
              assign lno ret_lno;
              assign (E.C.of_int (k-1)) ret_ki;
              assign ty ret_ty;
            ], csts

        | _ -> error () end
    | _ -> error ());

  "env-typeof-gr", `Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 2 "global-reference out" in
    match args with
    | [E.CData gr;ret_ty] when isgr gr ->
        let gr = grout gr in
        let csts, ty = type_of_global_in_context csts depth gr in
        [ assign ty ret_ty ], csts
    | _ -> error ());

  (* Kernel's environment write access ************************************ *)
  "env-add-const", `Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 4 "@gref term term out" in
    match args with
    | [E.CData gr;bo;ty;ret_gr] when E.C.is_string gr ->
        let open Globnames in
        let csts, ty, used_ty =
          if ty = in_elpi_implicit then csts, None, Univ.LSet.empty
          else
            let csts, ty = lp2constr csts ty in
            csts, Some ty, Univops.universes_of_constr ty in
        let csts, bo = lp2constr csts bo in
        let used = Univ.LSet.union used_ty (Univops.universes_of_constr bo) in
        let csts = normalize_csts csts used in
        let env, evd = get_env_evd csts in
        let open Constant in
        let ce = Entries.({
          const_entry_opaque = false;
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
          DeclareDef.declare_definition (Id.of_string (E.C.to_string gr)) dk ce
         [] [] Lemmas.(mk_hook (fun _ x -> x)) in
        [assign (in_elpi_gr gr) ret_gr], csts
    | _ -> error ());

  "env-add-axiom", `Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 3 "@gref term out" in
    match args with
    | [E.CData gr;ty;ret_gr] when E.C.is_string gr ->
        let open Globnames in
        let csts, ty = lp2constr csts ty in
        let used = Univops.universes_of_constr ty in
        let csts = normalize_csts csts used in
        let _env, evd = get_env_evd csts in
        let dk = Decl_kinds.(Global, false, Logical) in
        let gr, _, _ =
          Command.declare_assumption false dk (ty, Evd.universe_context_set evd)
            [] [] false Vernacexpr.NoInline
            (None, Id.of_string (E.C.to_string gr)) in 
        [assign (in_elpi_gr gr) ret_gr], csts
    | _ -> error ());

  (* TODO: env-add-inductive *)

  (* DBs write access ***************************************************** *)
  "TC-declare-instance", `Pure (fun ~depth ~error ~kind ~pp args ->
    let error () = error 3 "@gref int bool" () in
    match args with
    | [E.CData gr;E.CData priority;global]
      when isgr gr && E.C.is_int priority && 
           (global = in_elpi_tt || global = in_elpi_ff) ->
        let open Globnames in
        let reference = grout gr in
        let global =
          if global = in_elpi_tt then true
          else if global = in_elpi_ff then false
          else false in
        let hint_priority = Some (E.C.to_int priority) in
        let qualid =
          Nametab.shortest_qualid_of_global Names.Id.Set.empty reference in
        Classes.existing_instance global (Libnames.Qualid (None, qualid))
          (Some { Hints.empty_hint_info with Vernacexpr.hint_priority });
        []
    | _ -> error ());

  "CS-declare-instance", `Pure (fun ~depth ~error ~kind ~pp args ->
    let error () = error 1 "@gref" () in
    match args with
    | [E.CData gr] when isgr gr ->
        let open Globnames in
        let gr = grout gr in
        Recordops.declare_canonical_structure gr;
        []
    | _ -> error ());

  (* TODO: coercion-declare *)

  (* DBs read access ****************************************************** *)

  (* TODO: TC-db *)
  (* TODO: CS-db *)
  (* TODO: coercion-db *)

  (* Kernel's type checker ************************************************ *)
  "typecheck", `Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 2 "term out" in
    match args with
    | [t;ret] ->
        let csts, t = lp2constr csts t in
        let senv, evd = get_senv_evd csts in
        let j = Safe_typing.typing senv t in
        let csts, ty = constr2lp csts depth (Safe_typing.j_type j) in
        [assign ty ret], csts
    | _ -> error ());
  
  (* Pretyper ************************************************************* *)
  "elaborate", `Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 3 "term out out" in
    match args with
    | [t;ret_t;ret_ty] ->
        let csts, t = lp2constr csts t in
        let env, evd = get_env_evd csts in
        let evd = ref evd in
        let gt = Detyping.detype false [] env !evd (EConstr.of_constr t) in
        let gt =
          let rec map = function
            | { CAst.v = GEvar _ } -> mkGHole
            | x -> Glob_ops.map_glob_constr map x in
          map gt in
        let evd = ref (Evd.from_env env) in
        let j = Pretyping.understand_judgment_tcc env evd gt in
        let csts, t  =
          constr2lp csts depth (EConstr.Unsafe.to_constr (Environ.j_val j))  in
        let csts, ty =
          constr2lp csts depth (EConstr.Unsafe.to_constr (Environ.j_type j)) in
        let csts = CC.update csts univ_constraints
          (fun _ -> UState.normalize (Evd.evar_universe_context !evd)) in
        [E.App (E.Constants.eqc, t, [ret_t]);
         E.App (E.Constants.eqc, ty, [ret_ty])], csts
    | _ -> error ());

  (* Universe constraints ************************************************* *)
  "univ-print-constraints", `Constraints (fun ~depth ~error ~kind ~pp csts _ ->
    let uc =
      Termops.pr_evar_universe_context (CC.read csts univ_constraints) in
    Feedback.msg_info Pp.(str "Universe constraints: " ++ uc);
    [],csts);
  "univ-leq", `Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 2 "@univ @univ" in
    let csts, assignments, args = to_univ 2 csts [] [] args in
    match args with
    | [E.CData u1;E.CData u2] when isuniv u1 && isuniv u2 ->
      assignments, add_universe_constraint csts u1 Universes.ULe u2
    | _ -> error ());
  "univ-eq", `Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 2 "@univ @univ" in
    let csts, assignments, args = to_univ 2 csts [] [] args in
    match args with
    | [E.CData u1;E.CData u2] when isuniv u1 && isuniv u2 ->
      assignments, add_universe_constraint csts u1 Universes.UEq u2
    | _ -> error ());
  "univ-new", `Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 2 "(list @name) out" in
    match args with
    | [nl;out] ->
        let l = U.lp_list_to_list ~depth nl in
        if l <> [] then nYI "named universes";
        let csts, assignments, _args = to_univ 1 csts [] [] [out] in
        assignments, csts
    | _ -> error ());
  "univ-sup",`Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 2 "@univ out" in
    let csts, assignments, args = to_univ 1 csts [] [] args in
    match args with
    | [E.CData u;out_super] when isuniv u ->
        let csts, u1 = univ_super csts u in
        assign (E.CData u1) out_super :: assignments, csts
    | _ -> error ());
  "univ-max",`Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 3 "@univ @univ out" in
    let csts, assignments, args = to_univ 2 csts [] [] args in
    match args with
    | [E.CData u1;E.CData u2;out] when isuniv u1 && isuniv u2 ->
        let csts, u3 = univ_max csts u1 u2 in
        assign (E.CData u3) out :: assignments, csts
    | _ -> error ());
  "univ-algebraic-sup",`Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 2 "@univ out" in
    let csts, assignments, args = to_univ 1 csts [] [] args in
    match args with
    | [E.CData u;out_super] when isuniv u ->
        assign (E.CData(mk_algebraic_super u)) out_super ::
        assignments, csts
    | _ -> error ());
  "univ-algebraic-max",`Constraints (fun ~depth ~error ~kind ~pp csts args ->
    let error = error 3 "@univ @univ out" in
    let csts, assignments, args = to_univ 2 csts [] [] args in
    match args with
    | [E.CData u1;E.CData u2;out] when isuniv u1 && isuniv u2 ->
         assign (E.CData(mk_algebraic_max u1 u2)) out ::
         assignments, csts
    | _ -> error ());

  (* Misc ***************************************************************** *)
  "error", `Pure (fun ~depth ~error ~kind ~pp args ->
     match args with
     | [] -> error 1 "at least one argument" ()
     | l ->
         let msg = List.map (pp2string pp) l in
         err Pp.(str (String.concat " " msg)));

  "string-of-gr", `Pure (fun ~depth ~error ~kind ~pp args ->
     let error = error 2 "@gref out" in
     match args with
     | [E.CData gr;ret_gr]
       when isgr gr ->
          let open Globnames in
          let gr = grout gr in
          begin match gr with
          | VarRef v ->
              let lbl = Id.to_string v in
              [assign (E.C.of_string lbl) ret_gr]
          | ConstRef c ->
              let _, _, lbl = Constant.repr3 c in
              let lbl = Id.to_string (Label.to_id lbl) in
              [assign (E.C.of_string lbl) ret_gr]
          | IndRef (i,0)
          | ConstructRef ((i,0),_) ->
              let mp, dp, lbl = MutInd.repr3 i in
              let lbl = Id.to_string (Label.to_id lbl) in
              [assign (E.C.of_string lbl) ret_gr]
          | IndRef _  | ConstructRef _ ->
               nYI "mutual inductive (make-derived...)" end
     | _ -> error ());

  "mk-name", `Pure (fun ~depth ~error ~kind ~pp args ->
     let error = error 2 "string out" in
     match args with
     | [E.CData s; ret_name] when E.C.is_string s ->
         let name = Names.(Name.mk_name (Id.of_string (E.C.to_string s))) in
         [assign (in_elpi_name name) ret_name]
     | _ -> error());
  ]
;;

