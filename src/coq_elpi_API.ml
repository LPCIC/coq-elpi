(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module G = Globnames
module E = Elpi_API.Data
module R = Elpi_API.Runtime
module P = Elpi_API.Pp
module C = Constr

open Names
open Glob_term

open Coq_elpi_utils
open Coq_elpi_HOAS

(* ***************** $custom Coq predicates  ***************************** *)

let type_err pp api args nexpected expected () =
 err Pp.(str"Illtyped call to Coq API " ++ str api ++ spc () ++
         str"got " ++ int (List.length args) ++ str" arguments, namely: " ++
         prlist_with_sep (fun () -> str", ") str (List.map pp args) ++
         str" but " ++ int nexpected ++
         str " arguments are expected: " ++ str expected)

let declare_api (name, f) =
  let name = "$coq-" ^ name in
  R.register_custom name (fun ~depth ~env _ args ->
    let args = List.map (kind ~depth) args in
    let pp = P.uppterm depth [] 0 env in
    f ~depth ~type_err:(type_err (pp2string pp) name args)
      ~kind:(kind ~depth)
      ~pp args)
;;
let assign a b = E.App (E.Constants.eqc, a, [b])

let () = List.iter declare_api [

  (* Print (debugging) *)  
  "say", (fun ~depth ~type_err ~kind ~pp args ->
    Feedback.msg_info Pp.(str (pp2string (Elpi_util.pplist pp " ") args));
    []);
  "warn", (fun ~depth ~type_err ~kind ~pp args ->
    Feedback.msg_warning Pp.(str (pp2string (Elpi_util.pplist pp " ") args));
    []);

  (* Nametab access *)  
  "locate", (fun ~depth ~type_err ~kind ~pp args ->
    let type_err = type_err 2 "string out" in
    match args with
    | [E.CData c;ret] when E.CD.is_string c ->
        let qualid = Libnames.qualid_of_string (E.CD.to_string c) in
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
  "env-const", (fun ~depth ~type_err ~kind ~pp args ->
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

  "env-indt", (fun ~depth ~type_err ~kind ~pp args ->
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
            if mind.mind_polymorphic then
              nYI "API(env) poly mutual inductive";
            if mind.mind_finite = Decl_kinds.CoFinite then
              nYI "API(env) co-inductive";
             
            let co  = in_elpi_tt in
            let lno = E.CD.of_int (mind.mind_nparams) in
            let luno = E.CD.of_int (mind.mind_nparams_rec) in
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
              assign (R.list_to_lp_list (List.map in_elpi_gr kn)) ret_kn;
              assign (R.list_to_lp_list (List.map (constr2lp ~depth) kt)) ret_kt;
             ]
        | _ -> type_err () end
    | _ -> type_err ());

  "env-indc", (fun ~depth ~type_err ~kind ~pp args ->
    let type_err = type_err 5 "indc-reference out^3" in
    match args with
    | [E.CData gr;ret_lno;ret_ki;ret_ty] when isgr gr ->
        let gr = grout gr in
        begin match gr with
        | G.ConstructRef (i,k as kon) ->
            let open Declarations in
            let mind, indbo as ind = Global.lookup_inductive i in
            let lno = E.CD.of_int (mind.mind_nparams) in
            let ty =
              Inductive.type_of_constructor (kon,Univ.Instance.empty) ind in
            [ 
              assign lno ret_lno;
              assign (E.CD.of_int (k-1)) ret_ki;
              assign (constr2lp depth ty) ret_ty;
            ]

        | _ -> type_err () end
    | _ -> type_err ());

  "env-typeof-gr", (fun ~depth ~type_err ~kind ~pp args ->
    let type_err = type_err 2 "global-reference out" in
    match args with
    | [E.CData gr;ret_ty] when isgr gr ->
        let gr = grout gr in
        let ty,_u = Global.type_of_global_in_context (Global.env()) gr in
        [ assign (constr2lp depth ty) ret_ty; ]
    | _ -> type_err ());

  "env-add-const", (fun ~depth ~type_err ~kind ~pp args ->
    let type_err = type_err 4 "@gref term term out" in
    match args with
    | [E.CData gr;bo;ty;ret_gr] when E.CD.is_string gr ->
        let open Globnames in
        let ty =
          if ty = Coq_elpi_HOAS.in_elpi_implicit then None
          else Some (lp2constr ty) in
        let open Constant in
        let ce = Entries.({
          const_entry_opaque = false;
          const_entry_body = Future.from_val
            ((lp2constr bo, Univ.ContextSet.empty), (* FIXME *)
             Safe_typing.empty_private_constants) ;
          const_entry_secctx = None;
          const_entry_feedback = None;
          const_entry_type = ty;
          const_entry_polymorphic = false;
          const_entry_universes = Univ.UContext.empty; (* FIXME *)
          const_entry_inline_code = false; }) in
        let dk = Decl_kinds.(Global, false, Definition) in
        let gr =
          Command.declare_definition (Id.of_string (E.CD.to_string gr)) dk ce
         [] [] Lemmas.(mk_hook (fun _ x -> x)) in
        [assign (in_elpi_gr gr) ret_gr]
    | _ -> type_err ());
  "env-add-axiom", (fun ~depth ~type_err ~kind ~pp args ->
    let type_err = type_err 3 "@gref term out" in
    match args with
    | [E.CData gr;ty;ret_gr] when E.CD.is_string gr ->
        let open Globnames in
        let ty = lp2constr ty in
        let dk = Decl_kinds.(Global, false, Logical) in
        let gr, _, _ =
          Command.declare_assumption false dk (ty, Univ.ContextSet.empty)
            [] [] false Vernacexpr.NoInline (None, Id.of_string (E.CD.to_string gr)) in 
        [assign (in_elpi_gr gr) ret_gr]
    | _ -> type_err ());

  (* Kernel's type checker *)  
  "typecheck", (fun ~depth ~type_err ~kind ~pp args ->
    let type_err = type_err 2 "term out" in
    match args with
    | [t;ret] ->
        let t = lp2constr t in
        let j = Safe_typing.typing (Global.safe_env ()) t in
        let ty = constr2lp depth (Safe_typing.j_type j) in
        [assign ty ret]
    | _ -> type_err ());
  
  (* Type inference *)  
  "elaborate", (fun ~depth ~type_err ~kind ~pp args ->
    let type_err = type_err 3 "term out out" in
    match args with
    | [t;ret_t;ret_ty] ->
        let t = lp2constr t in
        let env = Global.env () in
        let gt = Detyping.detype false [] env Evd.empty (EConstr.of_constr t) in
        let gt =
          let rec map = function
            | { CAst.v = GEvar _ } -> mkGHole
            | x -> Glob_ops.map_glob_constr map x in
          map gt in
        let evd = ref (Evd.from_env env) in
        let j = Pretyping.understand_judgment_tcc env evd gt in
        let t  = constr2lp depth (EConstr.Unsafe.to_constr (Environ.j_val j))  in
        let ty = constr2lp depth (EConstr.Unsafe.to_constr (Environ.j_type j)) in
        [E.App (E.Constants.eqc, t, [ret_t]);
         E.App (E.Constants.eqc, ty, [ret_ty])]
    | _ -> type_err ());

  (* Misc *)
  "err", (fun ~depth ~type_err ~kind ~pp args ->
     match args with
     | [] -> type_err 1 "at least one argument" ()
     | l ->
         let msg = List.map (pp2string pp) l in
         err Pp.(str (String.concat " " msg)));

  "string-of-gr", (fun ~depth ~type_err ~kind ~pp args ->
     let type_err = type_err 2 "gref out" in
     match args with
     | [E.CData gr;ret_gr]
       when isgr gr ->
          let open Globnames in
          let gr = grout gr in
          begin match gr with
          | VarRef v ->
              let lbl = Id.to_string v in
              [assign (E.CD.of_string lbl) ret_gr]
          | ConstRef c ->
              let _, _, lbl = Constant.repr3 c in
              let lbl = Id.to_string (Label.to_id lbl) in
              [assign (E.CD.of_string lbl) ret_gr]
          | IndRef (i,0)
          | ConstructRef ((i,0),_) ->
              let mp, dp, lbl = MutInd.repr3 i in
              let lbl = Id.to_string (Label.to_id lbl) in
              [assign (E.CD.of_string lbl) ret_gr]
          | IndRef _  | ConstructRef _ ->
               nYI "mutual inductive (make-derived...)" end
     | _ -> type_err ());

  "mk-name", (fun ~depth ~type_err ~kind ~pp args ->
     let type_err = type_err 2 "gref out" in
     match args with
     | [E.CData s; ret_name]
       when E.CD.is_string s ->
         let name = Names.(Name.mk_name (Id.of_string (E.CD.to_string s))) in
         [assign (in_elpi_name name) ret_name]
     | _ -> type_err());
  ]
;;


