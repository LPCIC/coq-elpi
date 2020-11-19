(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module E = API.RawData
module U = API.Utils
module S = API.State
module Q = API.Quotation
module F = API.FlexibleData

open Coq_elpi_HOAS

open Names
open Coq_elpi_utils

let debug () = !Flags.debug

(* ***************** {{ quotation }} for Glob_terms ********************** *)

open Glob_term

(* Set by the parser that declares an ARGUMENT EXTEND to Coq *)
let is_elpi_code = ref (fun _ -> assert false)
let get_elpi_code = ref (fun _ -> assert false)
let is_elpi_code_appArg = ref (fun _ -> assert false)
let get_elpi_code_appArg = ref (fun _ -> assert false)

let get_ctx, set_ctx, _update_ctx =
  let bound_vars =
    S.declare ~name:"coq-elpi:glob-quotation-bound-vars"
      ~init:(fun () -> None)
      ~pp:(fun fmt -> function Some (x,_) -> () | None -> assert false)
      ~start:(fun x -> x)
       in
  S.(get bound_vars, set bound_vars, update bound_vars)

let set_coq_ctx_hyps s (x,h) = set_ctx s (Some (upcast @@ x, h))

let glob_intros ctx bo =
  List.fold_right (fun (name,_,ov,ty) bo ->
     DAst.make
     (match ov with
     | None -> GLambda(name,Explicit,ty,bo)
     | Some v -> GLetIn(name,v,Some ty,bo)))
   ctx bo
;;
let glob_intros_prod ctx bo =
  List.fold_right (fun (name,_,ov,ty) bo ->
     DAst.make
     (match ov with
     | None -> GProd(name,Explicit,ty,bo)
     | Some v -> GLetIn(name,v,Some ty,bo)))
   ctx bo
;;

(* HACK: names not visible by evars *)
let mk_restricted_name i = Printf.sprintf "_elpi_restricted_%d_" i
let is_restricted_name =
  let rex = Str.regexp "_elpi_restricted_[0-9]+_" in
  fun s -> Str.(string_match rex (Id.to_string s) 0)

(* XXX: I don't get why we use a coq_ctx here *)
let under_ctx name ty bo gterm2lp ~depth state x =
  let coq_ctx, hyps as orig_ctx = Option.default (upcast @@ mk_coq_context state,[]) (get_ctx state) in
  let state, name =
    let id =
      match name with
      | Name id -> id
      | Anonymous ->
          Id.of_string_soft
            (Printf.sprintf "_elpi_ctx_entry_%d_" (Id.Map.cardinal coq_ctx.name2db)) in
    let name2db = Id.Map.add id depth coq_ctx.name2db in
    let state, ctx_entry =
      let lift1 = U.move ~from:depth ~to_:(depth+1) in
      match bo with
      | None ->
          state, mk_decl ~depth name ~ty:(lift1 ty) 
      | Some bo ->
          state, mk_def ~depth name ~bo:(lift1 bo) ~ty:(lift1 ty) in
    let new_hyp = { ctx_entry; depth = depth+1 } in
    set_coq_ctx_hyps state ({ coq_ctx with name2db }, new_hyp :: hyps), Name id in
  let state, y = gterm2lp ~depth:(depth+1) (push_env state name) x in
  let state = set_coq_ctx_hyps state orig_ctx in
  let state = pop_env state in
  state, y

let rec gterm2lp ~depth state x =
  if debug () then
    Feedback.msg_debug Pp.(str"gterm2lp: depth=" ++ int depth ++
      str " term=" ++Printer.pr_glob_constr_env (get_global_env state) x);
  match (DAst.get x) (*.CAst.v*) with
  | GRef(gr,Some i) ->
      let state, i = CList.fold_left_map interp_ulevel state i in
      let i = Univ.Instance.of_array (Array.of_list i) in
      let state, instance, _ = uinstance.API.Conversion.embed ~depth state i in
      state, in_elpi_gr ~depth state gr ~instance
  | GRef(gr,None) ->
      let state, uv = F.Elpi.make state in
      let instance = E.mkUnifVar uv ~args:[] state in
      state, in_elpi_gr ~depth state gr ~instance
  | GVar(id) ->
      let ctx, _ = Option.default (upcast @@ mk_coq_context state, []) (get_ctx state) in
      if not (Id.Map.mem id ctx.name2db) then
        CErrors.user_err ~hdr:"elpi quotation"
          Pp.(str"Free Coq variable " ++ Names.Id.print id ++ str " in context " ++
            prlist_with_sep spc Id.print (Id.Map.bindings ctx.name2db |> List.map fst));
      state, E.mkConst (Id.Map.find id ctx.name2db)
  | GSort(UAnonymous {rigid=true}) ->
      let state, uv = F.Elpi.make state in
      let s = E.mkUnifVar uv ~args:[] state in
      state, in_elpi_flex_sort s
  | GSort(UNamed [name,0]) ->
      let env = get_global_env state in
      state, in_elpi_sort (Sorts.sort_of_univ @@ Univ.Universe.make @@ Pretyping.interp_known_glob_level (Evd.from_env env) name)
  | GSort(_) -> nYI "(glob)HOAS for Type@{i j}"

  | GProd(name,_,s,t) ->
      let state, s = gterm2lp ~depth state s in
      let state, t = under_ctx name s None gterm2lp ~depth state t in
      state, in_elpi_prod name s t
  | GLambda(name,_,s,t) ->
      let state, s = gterm2lp ~depth state s in
      let state, t = under_ctx name s None gterm2lp ~depth state t in
      state, in_elpi_lam name s t
  | GLetIn(name,bo , oty, t) ->
      let state, bo = gterm2lp ~depth state bo in
      let state, ty =
        match oty with
        | None ->
            let state, uv = F.Elpi.make state in
            let ctx, _ = Option.default (upcast @@ mk_coq_context state, []) (get_ctx state) in
            let args = List.map (fun (_,x) -> E.mkBound x) (Id.Map.bindings ctx.name2db) in
            state, E.mkUnifVar uv ~args state
        | Some ty -> gterm2lp ~depth state ty in
      let state, t = under_ctx name ty (Some bo) gterm2lp ~depth state t in
      state, in_elpi_let name bo ty t

  | GHole(_,_,Some arg) when !is_elpi_code arg ->
      let loc, text = !get_elpi_code arg in
      let s, x = Q.lp ~depth state loc text in
      let s, x =
        match E.look ~depth x with
        | E.App(c,call,[]) when c == E.Constants.spillc ->
          let _, hyps = Option.default (upcast @@ mk_coq_context state, []) (get_ctx state) in
          let hyps = List.map (fun { ctx_entry = t; depth = from } ->
            U.move ~from ~to_:depth t) hyps in
          s, E.mkApp c (E.mkApp E.Constants.implc (U.list_to_lp_list hyps) [call]) []
        | _ -> s, x
      in
(*       Format.eprintf "unquote: %a\n" (Elpi_API.Extend.Pp.term depth) x; *)
        s, x
  | GHole(_,_,Some arg) when !is_elpi_code_appArg arg ->
      begin match !get_elpi_code_appArg arg with
      | _, [] -> assert false
      | loc, hd :: vars ->
          let state, hd = Q.lp ~depth state loc hd in
          let state, args =
            CList.fold_left_map (gterm2lp ~depth) state
              (List.map (fun x -> DAst.make (GVar (Id.of_string x))) vars) in
          if API.RawQuery.is_Arg state hd then
            state, in_elpi_app_Arg ~depth hd args
          else
            state, mkApp ~depth hd args
      end

  | GHole (_,_,None) ->
      let state, uv = F.Elpi.make state in
      let ctx, _ = Option.default (upcast @@ mk_coq_context state, []) (get_ctx state) in
      let args =
        Id.Map.bindings ctx.name2db |>
        List.filter (fun (n,_) -> not(is_restricted_name n)) |>
        List.map snd |>
        List.sort Pervasives.compare |>
        List.map E.mkBound
      in
      state, E.mkUnifVar uv ~args state

  | GHole _ -> nYI "(glob)HOAS for GHole"

  | GCast(t,(Glob_term.CastConv c_ty | Glob_term.CastVM c_ty | Glob_term.CastNative c_ty)) ->
      let state, t = gterm2lp ~depth state t in
      let state, c_ty = gterm2lp ~depth state c_ty in
      let self = E.mkConst depth in
      state, in_elpi_let Names.Name.Anonymous t c_ty self
  | GCast _ -> nYI "(glob)HOAS for GCast"

  | GEvar(_k,_subst) -> nYI "(glob)HOAS for GEvar"
  | GPatVar _ -> nYI "(glob)HOAS for GPatVar"
(*   | GProj _ -> nYI "(glob)HOAS for GProj" *)

  | GApp(hd,args) ->
      let state, hd = gterm2lp ~depth state hd in
      let state, args = CList.fold_left_map (gterm2lp ~depth) state args in
        state, in_elpi_appl hd args
  
  | GCases(_, oty, [ t, (as_name, oind) ], bs) ->
      let open Declarations in
      let env = get_global_env state in
      let ind, args_name =
        match oind with
        | Some {CAst.v=ind, arg_names} -> ind, arg_names
        | None ->
            match bs with
            | {CAst.v=(_,[x],_)} :: _ ->
                begin match DAst.get x with
                | PatCstr((ind,_),_,_) -> ind, []
                | _ -> nYI "(glob)HOAS match oty ind" end
            | _ -> nYI "(glob)HOAS match oty ind" in
      let { mind_packets; mind_nparams }, { mind_consnames } as indspecif =
        Inductive.lookup_mind_specif env ind in
      let no_constructors = Array.length mind_consnames in
      if Array.length mind_packets <> 1 then nYI "(glob)HOAS mutual inductive";
      let state, t = gterm2lp ~depth state t in
      let state, rt =
        (* We try hard to stick in there the inductive type, so that
         * the term can be read back (mkCases needs the ind) *)
        (* TODO: add whd reduction in spine *)
        let state, (ty,_) = type_of_global (GlobRef.IndRef ind) None state in
        let ty = EConstr.to_constr (get_sigma state) ty in
        let safe_tail = function [] -> [] | _ :: x -> x in
        let best_name n l = match n, l with
          | _, (Name x) :: rest -> Name x,DAst.make (GVar x), rest
          | Name x, _ :: rest -> Name x,DAst.make (GVar x), rest
          | Anonymous, Anonymous :: rest -> Anonymous,mkGHole, rest
          | Name x, [] -> Name x,DAst.make (GVar x), []
          | Anonymous, [] -> Anonymous,mkGHole, [] in
        let rec spine n names args ty =
          let open Constr in
          match kind ty with
          | Sort _ ->
             DAst.make (GLambda(as_name,Explicit,
               Glob_ops.mkGApp (DAst.make (GRef(GlobRef.IndRef ind,None))) (List.rev args),
               Option.default mkGHole oty))
          | Prod (name, src, tgt) when n = 0 ->
             let name, var, names = best_name name.Context.binder_name names in
             DAst.make (GLambda(name,Explicit,
               mkGHole,spine (n-1) (safe_tail names) (var :: args) tgt))
          | LetIn (name, v, _, b) ->
              spine n names args (Vars.subst1 v b)
          |  Cast (t, _, _) -> spine n names args t
          | Prod (_, _, t) ->
              spine (n-1) (safe_tail names) (mkGHole :: args) t 
          | _ -> assert false in
        gterm2lp ~depth state (spine mind_nparams args_name [] ty) in
      let bs =
        List.map (fun {CAst.v=(fv,pat,bo)} ->
          match List.map DAst.get pat with
          | [PatCstr((indc,cno as k),cargs,Name.Anonymous)] ->
               assert(Names.eq_ind indc ind);
               let cargs = List.map (fun x -> match DAst.get x with
                 | PatVar n -> n
                 | _ -> nYI "(glob)HOAS match deep pattern") cargs in
               `Case(k,cargs,bo)
          | [PatVar Name.Anonymous] ->
               `Def bo
          | _ -> nYI "(glob)HOAS match complex pattern") bs in
      let def,bs = List.partition (function `Def _ -> true | _ -> false) bs in
      assert(List.length def <= 1);
      let bs = CList.init no_constructors (fun i ->
        let cno = i + 1 in
        try CList.find_map (function
             | `Case((_,n as k),vars,bo) when n = cno -> Some (k,vars,bo)
             | `Case _ -> None
             | `Def _ -> assert false) bs
        with Not_found ->
          match bs with
          | [`Def bo] ->
             let missing_k = ind,cno in
             let k_args = Inductiveops.constructor_nallargs (Global.env()) missing_k in
             missing_k, CList.make k_args Name.Anonymous, bo
          | _ ->
             err Pp.(str"Missing constructor "++Id.print mind_consnames.(i))) in
      let state, bs = CList.fold_left_map (fun state (k,vars,bo) ->
        let bo =
          List.fold_right (fun name bo ->
            DAst.make (GLambda(name,Explicit,mkGHole,bo)))
            vars bo in
        let state, bo = gterm2lp ~depth state bo in
        state, bo) state bs in
      state, in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs
  | GCases _ -> nYI "(glob)HOAS complex match expression"
  | GLetTuple _ -> nYI "(glob)HOAS destructuring let"
  | GIf  _ -> nYI "(glob)HOAS if-then-else"

  | GRec(GFix([|Some rno|],0),[|name|],[|tctx|],[|ty|],[|bo|]) ->
      let ty = glob_intros_prod tctx ty in
      let state, ty = gterm2lp ~depth state ty in
      let bo = glob_intros tctx bo in
      let state, bo = under_ctx (Name name) ty None gterm2lp ~depth state bo in
      state, in_elpi_fix (Name name) rno ty bo
  | GRec _ -> nYI "(glob)HOAS mutual/non-struct fix"
  | GInt i -> in_elpi_uint63 ~depth state i
  | GFloat f -> in_elpi_float64 ~depth state f
;;

let coq_quotation ~depth state _loc src =
  let ce = Pcoq.parse_string Pcoq.Constr.lconstr src in
  gterm2lp ~depth state (Constrintern.intern_constr (get_global_env state) (get_sigma state) ce)

(* Install the quotation *)
let () = Q.set_default_quotation coq_quotation
let () = Q.register_named_quotation ~name:"coq" coq_quotation

let under_ctx name ty bo f ~depth state =
  under_ctx name ty bo (fun ~depth state () -> f ~depth state) ~depth state ()

let do_term t ~depth state = gterm2lp ~depth state t

let rec do_params params kont ~depth state =
  match params with
  | [] -> kont ~depth state
  | (name,imp,ob,src) :: params ->
      if ob <> None then Coq_elpi_utils.nYI "defined parameters in a record/inductive declaration";
      let state, src = gterm2lp ~depth state src in
      let state, tgt = under_ctx name src None (do_params params kont) ~depth state in
      let state, imp = in_elpi_imp ~depth state imp in
      state, in_elpi_parameter name ~imp src tgt

let do_arity t ~depth state =
  let state, t = do_term t ~depth state in
  state, in_elpi_arity t

let rec do_fields fields ~depth state =
  match fields with
  | [] -> state, in_elpi_indtdecl_endrecord ()
  | (f,({ name; is_coercion; is_canonical } as att)) :: fields ->
      let state, f = do_term f ~depth state in
      let state, fields = under_ctx name f None (do_fields fields) ~depth state in
      in_elpi_indtdecl_field ~depth state att f fields

let do_record ~name ~constructorname arity fields ~depth state =
  let space, record_name = name in
  let qrecord_name = Id.of_string_soft @@ String.concat "." (space @ [Id.to_string record_name]) in
  let state, arity = do_term arity ~depth state in
  let state, fields = do_fields fields ~depth state in
  let constructor = match constructorname with
    | None -> Name.Name (Id.of_string ("Build_" ^ Id.to_string record_name))
    | Some x -> Name.Name x in
  state, in_elpi_indtdecl_record (Name.Name qrecord_name) arity constructor fields

