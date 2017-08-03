(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module G = Globnames
module E = Elpi_API.Extend.Data
module U = Elpi_API.Extend.Utils
module R = Elpi_API.Extend
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

let univ_constraints : UState.t R.CustomConstraint.constraint_type =
  R.CustomConstraint.declare ~name:"Universe constraints"
    ~pp:pp_ucst ~empty:empty_ucst
;;

let get_env_evd c =
  let ustate = R.CustomConstraint.read c univ_constraints in
  Environ.push_context_set (UState.context_set ustate) (Global.env ()), Evd.from_ctx ustate
let get_senv_evd c =
  let ustate = R.CustomConstraint.read c univ_constraints in
  Safe_typing.push_context_set true (UState.context_set ustate) (Global.safe_env ()), Evd.from_ctx ustate
        
let lp2constr csts y = R.CustomConstraint.update_return csts univ_constraints (fun x -> lp2constr x y)
let new_univ csts =
  let csts, v = R.CustomConstraint.update_return csts univ_constraints new_univ in
  csts, E.CData (univin v)

let add_universe_constraints csts u1 x u2 =
  try
    R.CustomConstraint.update csts univ_constraints (fun u ->
      UState.add_universe_constraints u Universes.(Constraints.singleton (univout u1,x,univout u2)))
  with Univ.UniverseInconsistency _ -> raise R.CustomPredicate.No_clause

(* ***************** $custom Coq predicates  ***************************** *)

let type_err pp api args nexpected expected () =
 err Pp.(str"Illtyped call to Coq API " ++ str api ++ spc () ++
         str"got " ++ int (List.length args) ++ str" arguments, namely: " ++
         prlist_with_sep (fun () -> str", ") str (List.map pp args) ++
         str" but " ++ int nexpected ++
         str " arguments are expected: " ++ str expected)

let declare_api (name, f) =
  let name = "$coq-" ^ name in
  R.CustomPredicate.declare_full name (fun ~depth ~env _s c args ->
    let args = List.map (kind ~depth) args in
    let pp = P.term depth [] 0 env in
    match f with
    | `Pure f ->
        f ~depth ~type_err:(type_err (pp2string pp) name args)
          ~kind:(kind ~depth)
          ~pp args, c
    | `Constraints f ->
        f ~depth ~type_err:(type_err (pp2string pp) name args)
          ~kind:(kind ~depth)
          ~pp c args)
;;
let assign a b = E.App (E.Constants.eqc, a, [b])

let rec to_univ n csts gs us = function
  | [] -> csts, List.rev gs, List.rev us
  | (E.UVar _ | E.AppUVar _) as x :: xs when n > 0 ->
      let csts, u = new_univ csts in
      let g = assign x u in
      to_univ (n-1) csts (g::gs) (u::us) xs
  | x :: xs -> to_univ (n-1) csts gs (x::us) xs


let () = List.iter declare_api [

  (* Print (debugging) *)  
  "say", `Pure (fun ~depth ~type_err ~kind ~pp args ->
    Feedback.msg_info Pp.(str (pp2string (P.list ~boxed:true pp " ") args));
    []);
  "warn", `Pure (fun ~depth ~type_err ~kind ~pp args ->
    Feedback.msg_warning Pp.(str (pp2string (P.list ~boxed:true pp " ") args));
    []);

  (* Nametab access *)  
  "locate", `Pure (fun ~depth ~type_err ~kind ~pp args ->
    let type_err = type_err 2 "string out" in
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
    | _ -> type_err ());

  (* Kernel's environment access *)  
  "env-const", `Pure (fun ~depth ~type_err ~kind ~pp args -> (* XXX no pure *)
    let type_err = type_err 3 "const-reference out out" in
    match args with
    | [E.CData gr; ret_bo; ret_ty] when isgr gr ->
        let gr = grout gr in
        begin match gr with
        | G.ConstRef c ->
             let ty,_u = Global.type_of_global_in_context (Global.env()) gr in
             let bo = match Global.body_of_constant c with
               | Some bo -> constr2lp depth bo
               | None -> in_elpi_axiom in
             [ assign (constr2lp depth ty) ret_ty; assign bo ret_bo ]
        | G.VarRef v ->
             let ty,_u = Global.type_of_global_in_context (Global.env()) gr in
             let bo = match Global.lookup_named v with
               | Context.Named.Declaration.LocalDef(_,bo,_) -> constr2lp depth bo
               | Context.Named.Declaration.LocalAssum _ -> in_elpi_axiom in
             [ assign (constr2lp depth ty) ret_ty; assign bo ret_bo ]
        | _ -> type_err () end
    | _ -> type_err ());

  "env-indt", `Pure (fun ~depth ~type_err ~kind ~pp args -> (* XXX no pure *)
    let type_err = type_err 7 "indt-reference out^6" in
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
            let kt =
              Inductive.type_of_constructors (i,Univ.Instance.empty) ind in
            let kt = Array.to_list kt in
            let kn =
              CList.init
                Declarations.(indbo.mind_nb_constant + indbo.mind_nb_args)
                (fun k -> G.ConstructRef (i,k+1)) in

             [ 
              assign co ret_co;
              assign lno ret_lno;
              assign luno ret_luno;
              assign (constr2lp depth ty) ret_ty;
              assign (U.list_to_lp_list (List.map in_elpi_gr kn)) ret_kn;
              assign (U.list_to_lp_list (List.map (constr2lp ~depth) kt)) ret_kt;
             ]
        | _ -> type_err () end
    | _ -> type_err ());

  "env-indc", `Pure (fun ~depth ~type_err ~kind ~pp args -> (* XXX no pure *)
    let type_err = type_err 5 "indc-reference out^3" in
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
            [ 
              assign lno ret_lno;
              assign (E.C.of_int (k-1)) ret_ki;
              assign (constr2lp depth ty) ret_ty;
            ]

        | _ -> type_err () end
    | _ -> type_err ());

  "env-typeof-gr", `Pure (fun ~depth ~type_err ~kind ~pp args -> (* XXX no pure *)
    let type_err = type_err 2 "global-reference out" in
    match args with
    | [E.CData gr;ret_ty] when isgr gr ->
        let gr = grout gr in
        let ty,_u = Global.type_of_global_in_context (Global.env()) gr in
        [ assign (constr2lp depth ty) ret_ty; ]
    | _ -> type_err ());

  "env-add-const", `Constraints (fun ~depth ~type_err ~kind ~pp csts args ->
    let type_err = type_err 4 "@gref term term out" in
    match args with
    | [E.CData gr;bo;ty;ret_gr] when E.C.is_string gr ->
        let open Globnames in
        let csts, ty =
          if ty = Coq_elpi_HOAS.in_elpi_implicit then csts, None
          else
            let csts, ty = lp2constr csts ty in
            csts, Some ty in
        let csts, bo = lp2constr csts bo in
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
    | _ -> type_err ());
  "env-add-axiom", `Constraints (fun ~depth ~type_err ~kind ~pp csts args ->
    let type_err = type_err 3 "@gref term out" in
    match args with
    | [E.CData gr;ty;ret_gr] when E.C.is_string gr ->
        let open Globnames in
        let csts, ty = lp2constr csts ty in
        let _env, evd = get_env_evd csts in
        let dk = Decl_kinds.(Global, false, Logical) in
        let gr, _, _ =
          Command.declare_assumption false dk (ty, Evd.universe_context_set evd)
            [] [] false Vernacexpr.NoInline (None, Id.of_string (E.C.to_string gr)) in 
        [assign (in_elpi_gr gr) ret_gr], csts
    | _ -> type_err ());
  "TC-declare-instance", `Pure (fun ~depth ~type_err ~kind ~pp args ->
    let type_err () = type_err 3 "@gref int bool" () in
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
        let priority = E.C.to_int priority in
        let qualid = Nametab.shortest_qualid_of_global Names.Id.Set.empty reference in
        Classes.existing_instance global (Libnames.Qualid (None, qualid))
          (Some { Hints.empty_hint_info with Vernacexpr.hint_priority = Some priority });
        []
    | _ -> type_err ());
  "CS-declare-instance", `Pure (fun ~depth ~type_err ~kind ~pp args ->
    let type_err () = type_err 1 "@gref" () in
    match args with
    | [E.CData gr] when isgr gr ->
        let open Globnames in
        let gr = grout gr in
        Recordops.declare_canonical_structure gr;
        []
    | _ -> type_err ());

  (* Kernel's type checker *)  
  "typecheck", `Constraints (fun ~depth ~type_err ~kind ~pp csts args ->
    let type_err = type_err 2 "term out" in
    match args with
    | [t;ret] ->
        let csts, t = lp2constr csts t in
        let senv, evd = get_senv_evd csts in
        let j = Safe_typing.typing senv t in
        let ty = constr2lp depth (Safe_typing.j_type j) in
        [assign ty ret], csts
    | _ -> type_err ());
  
  (* Type inference *)  
  "elaborate", `Constraints (fun ~depth ~type_err ~kind ~pp csts args ->
    let type_err = type_err 3 "term out out" in
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
        let t  = constr2lp depth (EConstr.Unsafe.to_constr (Environ.j_val j))  in
        let ty = constr2lp depth (EConstr.Unsafe.to_constr (Environ.j_type j)) in
        let csts = R.CustomConstraint.update csts univ_constraints
          (fun _ -> UState.normalize (Evd.evar_universe_context !evd)) in
        [E.App (E.Constants.eqc, t, [ret_t]);
         E.App (E.Constants.eqc, ty, [ret_ty])], csts
    | _ -> type_err ());

  (* Universe constraints *)
  "univ-print-constraints", `Constraints (fun ~depth ~type_err ~kind ~pp csts args ->
    let uc =
      Termops.pr_evar_universe_context (R.CustomConstraint.read csts univ_constraints) in
    Feedback.msg_info Pp.(str "Universe constraints: " ++ uc);
    [],csts);
  "univ-leq", `Constraints (fun ~depth ~type_err ~kind ~pp csts args ->
    let type_err = type_err 2 "@univ @univ" in
    let csts, assignments, args = to_univ 2 csts [] [] args in
    match args with
    | [E.CData u1;E.CData u2] when isuniv u1 && isuniv u2 ->
      assignments, add_universe_constraints csts u1 Universes.ULe u2
    | _ -> type_err ());
  "univ-eq", `Constraints (fun ~depth ~type_err ~kind ~pp csts args ->
    let type_err = type_err 2 "@univ @univ" in
    let csts, assignments, args = to_univ 2 csts [] [] args in
    match args with
    | [E.CData u1;E.CData u2] when isuniv u1 && isuniv u2 ->
      assignments, add_universe_constraints csts u1 Universes.UEq u2
    | _ -> type_err ());
  "univ-new", `Constraints (fun ~depth ~type_err ~kind ~pp csts args ->
    let type_err = type_err 2 "(list @name) out" in
    match args with
    | [nl;out] ->
        let l = U.lp_list_to_list ~depth nl in
        if l <> [] then nYI "named universes";
        let csts, assignments, _args = to_univ 1 csts [] [] [out] in
        assignments, csts
    | _ -> type_err ());
  "univ-sup", `Constraints (fun ~depth ~type_err ~kind ~pp csts args ->
    let type_err = type_err 2 "@univ out" in
    let csts, assignments, args = to_univ 1 csts [] [] args in
    match args with
    | [E.CData u;out_super] when isuniv u ->
        assign (E.CData(univin (Univ.super (univout u)))) out_super ::
        assignments, csts
    | _ -> type_err ());
  "univ-max", `Constraints (fun ~depth ~type_err ~kind ~pp csts args ->
    let type_err = type_err 3 "@univ @univ out" in
    let csts, assignments, args = to_univ 2 csts [] [] args in
    match args with
    | [E.CData u1;E.CData u2;out] when isuniv u1 && isuniv u2 ->
         assign (E.CData(univin (Univ.Universe.sup (univout u1) (univout u2)))) out ::
         assignments, csts
    | _ -> type_err ());

  (* Misc *)
  "err", `Pure (fun ~depth ~type_err ~kind ~pp args ->
     match args with
     | [] -> type_err 1 "at least one argument" ()
     | l ->
         let msg = List.map (pp2string pp) l in
         err Pp.(str (String.concat " " msg)));

  "string-of-gr", `Pure (fun ~depth ~type_err ~kind ~pp args ->
     let type_err = type_err 2 "gref out" in
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
     | _ -> type_err ());

  "mk-name", `Pure (fun ~depth ~type_err ~kind ~pp args ->
     let type_err = type_err 2 "gref out" in
     match args with
     | [E.CData s; ret_name]
       when E.C.is_string s ->
         let name = Names.(Name.mk_name (Id.of_string (E.C.to_string s))) in
         [assign (in_elpi_name name) ret_name]
     | _ -> type_err());
  ]
;;

