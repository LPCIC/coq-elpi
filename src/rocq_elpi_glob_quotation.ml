(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi.API
module E = API.RawData
module U = API.Utils
module S = API.State
module Q = API.Quotation
module F = API.FlexibleData
module A = API.Ast

open Rocq_elpi_HOAS

open Names
open Rocq_elpi_utils

(* ***************** {{ quotation }} for Glob_terms ********************** *)

open Glob_term

(* HACK: names not visible by evars *)
let mk_restricted_name i = Printf.sprintf "_elpi_restricted_%d_" i
let is_restricted_name =
  let rex = Str.regexp "_elpi_restricted_[0-9]+_" in
  fun s -> Str.(string_match rex (Id.to_string s) 0)

let section_ids env =
  let named_ctx = Environ.named_context env in
  Context.Named.fold_inside
    (fun acc x -> Names.Id.Set.add (Context.Named.Declaration.get_id x) acc)
    ~init:Names.Id.Set.empty named_ctx

type glob_ctx = {
  taken : Names.Id.Set.t; (* union of the two below *)
  section : Names.Id.Set.t;
  bound : Names.Id.Set.t;
  bound_list : Names.Id.t list;
    (* the set above, but with the order in which they pccur in the Coq context (head one is last intro) *)
  env : Environ.env;
  hyps : A.Term.t list;
}

let empty_glob_ctx env : glob_ctx =
  { env; bound = Names.Id.Set.empty; bound_list = []; taken = section_ids env; section = section_ids env; hyps = [] }

let glob_ctx : glob_ctx option S.component =
  S.declare_component ~name:"rocq-elpi:glob-environment" ~descriptor:interp_state
    ~pp:(fun _ _ -> ()) ~init:(fun () -> None)
                        ~start:(fun _ -> Some (empty_glob_ctx (Global.env ()))) ()

let set_glob_ctx state e = S.set glob_ctx state (Some e)


let ensure_some f = function
 | None -> Some (f (empty_glob_ctx (Global.env ())))
 | Some x -> Some (f x)

let push_glob_ctx state name ctxast =
  S.update glob_ctx state (ensure_some (fun { env; bound; bound_list; section; hyps; taken } ->
    assert(not(Names.Id.Set.mem name taken));
    let d = Context.Named.Declaration.LocalAssum(Context.make_annot name Sorts.Relevant,Constr.mkProp) in
    let env = Environ.push_named d env in
    let bound = Names.Id.Set.add (*Environ.push_named_context_val*) name bound in
    let bound_list = name :: bound_list in
    let hyps = match ctxast with Some h -> h :: hyps | None -> hyps in
    let taken = Names.Id.Set.add name taken in
    { env; bound; bound_list; section; hyps; taken }
  ))
  
let glob_ctx_of_coq_ctx { names; env } =
  let genv = Global.env () in
  let section = section_ids genv in
  let bound_list = Environ.named_context env |> List.map Context.Named.Declaration.get_id in
  let bound_list = List.filter (fun x -> not @@ Names.Id.Set.mem x section) bound_list in
  { env = genv;
    bound = Names.Id.Set.of_list bound_list;
    bound_list;
    section;
    hyps = [];
    taken = names;
  }

  
let get_glob_env state = Option.get @@ ensure_some (fun x -> x) @@ S.get glob_ctx state

let update_subst l na =
  let in_range id l = List.exists (fun (_,id') -> Id.equal id id') l in
  let l' = Nameops.Name.fold_right Id.List.remove_assoc na l in
  Nameops.Name.fold_right
    (fun id _ ->
     if in_range id l' then
       let id' = Namegen.next_ident_away_from id (fun id' -> in_range id' l') in
       (id,id')::l, Name id'
     else l,na)
    na (l,na)

let update_subst_id l na =
  let in_range id l = List.exists (fun (_,id') -> Id.equal id id') l in
  let l' = Id.List.remove_assoc na l in
  if in_range na l' then
    let id' = Namegen.next_ident_away_from na (fun id' -> in_range id' l') in
    (na,id')::l, id'
  else l,na
    

let rename_var l id =
  try
    let id' = Id.List.assoc id l in
    id'
  with Not_found ->
    id

let rec rename_glob_vars l c = DAst.map_with_loc (fun ?loc -> function
  | GVar id as r ->
      let id' = rename_var l id in
      if id == id' then r else GVar id'
  | GRef (GlobRef.VarRef _,_) as r -> r
  | GProd (na,r,bk,t,c) ->
      let l',na' = update_subst l na in
      GProd (na',r,bk,rename_glob_vars l t,rename_glob_vars l' c)
  | GLambda (na,r,bk,t,c) ->
      let l',na' = update_subst l na in
      GLambda (na',r,bk,rename_glob_vars l t,rename_glob_vars l' c)
  | GLetIn (na,r,b,t,c) ->
      let l',na' = update_subst l na in
      GLetIn (na',r,rename_glob_vars l b,Option.map (rename_glob_vars l) t,rename_glob_vars l' c)
  (* Lazy strategy: we fail if a collision with renaming occurs, rather than renaming further *)
  | GCases (ci,po,tomatchl,cls)->
      (* TODO
      let test_pred_pat (na,ino) =
        test_na l na; Option.iter (fun {v=(_,nal)} -> List.iter (test_na l) nal) ino in
      let test_clause idl = List.iter (test_id l) idl in *)
      let po = Option.map (rename_glob_vars l) po in
      let tomatchl = Util.List.map_left (fun (tm,x) -> (rename_glob_vars l tm,x)) tomatchl in
      let cls = Util.List.map_left (CAst.map (fun (idl,p,c) -> (idl,p,rename_glob_vars l c))) cls in
      GCases (ci,po,tomatchl,cls)
  | GLetTuple (nal,(na,po),c,b) ->
    let l',na' = update_subst l na in
    let l'', nal = CList.fold_left_map update_subst l nal in
     GLetTuple (nal,(na',Option.map (rename_glob_vars l') po),
                rename_glob_vars l c,rename_glob_vars l'' b)
  | GIf (c,(na,po),b1,b2) ->
    let l',na' = update_subst l na in
    GIf (rename_glob_vars l c,(na',Option.map (rename_glob_vars l') po),
          rename_glob_vars l b1,rename_glob_vars l b2)
  | GRec (k,idl,decls,bs,ts) ->
      let l', idl = CArray.fold_left_map update_subst_id l idl in
      let decls, bs, ts = CArray.split3 @@ CArray.map3 (fun dl ty bo ->
        let l'', dl = CList.fold_left_map (fun l (na,r,k,bbd,bty) ->
          let l, na = update_subst l na in
          l, (na,r,k,Option.map (rename_glob_vars l) bbd, rename_glob_vars l bty)) l' dl in
        dl, rename_glob_vars l'' ty, rename_glob_vars l'' bo) decls bs ts in
      GRec (k,idl,decls,bs,ts)
  | _ -> DAst.get (Glob_ops.map_glob_constr (rename_glob_vars l) c)
  ) c

let under_glob_ctx name ~tyast ~k t state =
  match name with
  | Names.Name.Anonymous -> k name t state
  | Names.Name.Name id ->
    (* let () = Printf.eprintf " intro %s\n" (Id.to_string id) in *)
      let { taken } = get_glob_env state in
      let t, id =
        if Names.Id.Set.mem id taken then
          let new_id = Names.Id.of_string_soft (Format.asprintf "_elpi_renamed_%s_%d" (Id.to_string id) (Names.Id.Set.cardinal taken)) in
          (* let () = Printf.eprintf "%s -> %s\n" (Id.to_string id) (Id.to_string new_id) in *)
          rename_glob_vars [id,new_id] t, new_id
        else t, id in
      let state = push_glob_ctx state id (Some (tyast id)) in
      k (Names.Name.Name id) t state
  
(* Set by the parser that declares an ARGUMENT EXTEND to Coq *)
let get_ctx, set_ctx, _update_ctx =
  let bound_vars =
    S.declare_component ~name:"rocq-elpi:glob-quotation-bound-vars" ~descriptor:interp_state
      ~init:(fun () -> None)
      ~pp:(fun fmt -> function Some (x,_) -> () | None -> ())
      ~start:(fun x -> x) ()
       in
  S.(get bound_vars, set bound_vars, update bound_vars)

let set_coq_ctx_hyps s (x,h) =
  let s = set_ctx s (Some (upcast @@ x, h)) in
  set_glob_ctx s (glob_ctx_of_coq_ctx (upcast x))

let under_ctx name ty bo ~k ~depth state =
  let coq_ctx, hyps as orig_ctx = Option.default (upcast @@ mk_coq_context ~options:(default_options ()) state,[]) (get_ctx state) in
  let orig_glob_ctx = S.get glob_ctx state in
  let state =
    let id =
      match name with
      | Name id -> id
      | Anonymous ->
          Id.of_string_soft
            (Printf.sprintf "_elpi_ctx_entry_%d_" (Id.Map.cardinal coq_ctx.name2db)) in
    let name2db = Id.Map.add id depth coq_ctx.name2db in
    let state, ctx_entry =
      match bo with
      | None -> state, mk_decl ~depth name ~ty
      | Some bo -> state, mk_def ~depth name ~bo ~ty in
    let new_hyp = { ctx_entry; depth } in
    let state = set_coq_ctx_hyps state ({ coq_ctx with name2db }, new_hyp :: hyps) in
    let state = push_glob_ctx state id None in
    state in
  let state, y, gl = k ~depth:(depth+1) state in
  let state = set_coq_ctx_hyps state orig_ctx in
  let state = S.set glob_ctx state orig_glob_ctx in
  state, y, gl

let is_hole x = match DAst.get x with GHole _ -> true | _ -> false

let universe_level_name evd ({CAst.v=id} as lid) =
  try Evd.universe_of_name evd id
  with Not_found ->
    CErrors.user_err ?loc:lid.CAst.loc
      (Pp.(str "Undeclared universe: " ++ Id.print id ++ str "."))

let sort_name env sigma l = match l with
| [] -> assert false
| [u, 0] ->
  begin match u with
  | GSet -> Sorts.set
  | GSProp -> Sorts.sprop
  | GProp -> Sorts.prop
  | GUniv u -> Sorts.sort_of_univ (Univ.Universe.make u)
  | GLocalUniv l ->
    let u = universe_level_name sigma l in
    Sorts.sort_of_univ (Univ.Universe.make u)
  | GRawUniv _ -> nYI "GRawUniv"
  end
| [_] | _ :: _ :: _ ->
  nYI "(glob)HOAS for Type@{i j}"

let glob_level loc state = function
  | UAnonymous _ -> nYI "UAnonymous"
  | UNamed s ->
      match s with
      | GSProp 
      | GProp ->
        CErrors.user_err ?loc
          Pp.(str "Universe instances cannot contain non-Set small levels, polymorphic" ++
              str " universe instances must be greater or equal to Set.");
      | GSet -> Univ.Level.set
      | GUniv u -> u
      | GRawUniv u -> nYI "GRawUniv"
      | GLocalUniv l -> universe_level_name (get_sigma state) l

let nogls f ~depth state = let state, x = f ~depth state in state, x, ()

let rigid_anon_type = function GSort(None, UAnonymous {rigid=UnivRigid}) -> true | _ -> false
let named_type = function GSort(None, UNamed _) -> true | _ -> false
let name_of_type = function GSort(None, UNamed u) -> u | _ -> assert false
let dest_GProd = function GProd(n,_,_,s,t) -> n,s,t | _ -> assert false
let dest_GLambda = function GLambda(n,_,_,s,t) -> n,s,t | _ -> assert false
let dest_GLetIn = function GLetIn(n,_,bo,s,t) -> n,bo,s,t | _ -> assert false
let mkGLambda (n,b,s,t) = GLambda(n,None,b,s,t)
 
let dummy_loc = Loc.make_loc (0,0)

let fresh_uv = 
  let i = ref 0 in
  let aux () =
    incr i;
    let candidate = A.Name.from_string @@ "X" ^ string_of_int !i ^ "_" in
    candidate
  in
    aux

let glob_intros ctx bo =
  List.fold_right (fun (name,r,_,ov,ty) bo ->
      DAst.make
      (match ov with
      | None -> GLambda(name,r,Explicit,ty,bo)
      | Some v -> GLetIn(name,r,v,Some ty,bo)))
    ctx bo

let glob_intros_prod ctx bo =
  List.fold_right (fun (name,r,_,ov,ty) bo ->
      DAst.make
      (match ov with
      | None -> GProd(name,r,Explicit,ty,bo)
      | Some v -> GLetIn(name,r,v,Some ty,bo)))
    ctx bo
    
    

let name_of_id id = A.Name.from_string (Names.Id.to_string id)

let name_of = function
  | Names.Name.Anonymous -> None
  | Names.Name.Name id -> Some (name_of_id id)

let is_elpi_code = ref (fun _ -> assert false)
let get_elpi_code = ref (fun _ -> assert false)
let is_elpi_code_appArg = ref (fun _ -> assert false)
let get_elpi_code_appArg = ref (fun _ -> assert false)


let gterm2lpast ~pattern ~language state glob =

  let rec lookup_bound ~loc ~coqloc name state =
    let { env; bound; section } = get_glob_env state in
    match Names.Id.Set.mem name bound with
    | _ -> A.Term.mkBound ~loc ~language @@ name_of_id name
    | exception Not_found ->
        if Id.Set.mem name section then
          in_elpiast_gr ~loc (GlobRef.VarRef name)
        else
          CErrors.user_err ~loc:coqloc
            Pp.(str"Free Coq variable " ++ Id.print name ++ str " in context: " ++
            prlist_with_sep spc Id.print (Environ.named_context env |> Termops.ids_of_named_context));

  and under_binder ~loc name ty bo state t ~k =
    under_glob_ctx name ~tyast:(mk_tyast ~loc ~ty ~bo) ~k state t
            
  and mk_tyast ~loc ~ty ~bo id =
    match bo with
    | None -> mk_decl state ~loc id ~ty
    | Some bo -> mk_def state ~loc id ~ty ~bo

  and mk_decl state ~loc name ~ty =
    let v = A.Term.mkBound ~loc ~language @@ name_of_id name in
    in_elpiast_decl ~loc ~v (Name.Name name) ~ty

  and mk_def state ~loc name ~ty ~bo =
    let v = A.Term.mkBound ~loc ~language @@ name_of_id name in
    in_elpiast_def ~loc ~v (Name.Name name) ~ty ~bo

  and gterm2lp state ({ CAst.loc; v } as x) : A.Term.t =
  debug Pp.(fun () ->
      str"gterm2lp:" ++ str " term=" ++Printer.pr_glob_constr_env (get_glob_env state).env (get_sigma state) x);
  let coqloc = Option.default dummy_loc loc in
  let loc = Rocq_elpi_utils.of_coq_loc coqloc in
  match (DAst.get_thunk v) (*.CAst.v*) with
  | GRef(GlobRef.ConstRef p,_ul) when Structures.PrimitiveProjections.mem p ->
      let p = Option.get @@ Structures.PrimitiveProjections.find_opt p in
      let hd = in_elpiast_gr ~loc (GlobRef.ConstRef (Projection.Repr.constant p)) in
      hd
  | GRef(gr, ul) when Global.is_polymorphic gr ->
    begin match ul with
    | None ->
      let s = A.Term.mkVar ~loc (fresh_uv ()) [] in
      in_elpiast_poly_gr ~loc gr s
    | Some (ql,l) ->
      let () = if not (CList.is_empty ql) then nYI "sort poly" in
      let l' = List.map (glob_level x.CAst.loc state) l in
      in_elpiast_poly_gr_instance ~loc gr (UVars.Instance.of_array ([||], Array.of_list l'))
    end
  | GRef(gr,_ul) -> in_elpiast_gr ~loc gr
  | GVar(id) -> lookup_bound ~loc ~coqloc id state
  | GSort _ as t when rigid_anon_type t ->
      let s = A.Term.mkVar ~loc (fresh_uv ()) [] in
      in_elpiast_flex_sort ~loc s
  | GSort _ as t when named_type t ->
      let u = name_of_type t in
      let env = get_glob_env state in
      in_elpiast_sort ~loc state (sort_name env (get_sigma state) u)
  | GSort(_) -> nYI "(glob)HOAS for Type@{i j}"

  | GProd _ as t ->
      let (name,s,t) = dest_GProd t in
      let s = gterm2lp state s in
      under_binder ~loc name s None t state ~k:(fun name t state ->
        in_elpiast_prod ~loc name s (gterm2lp state t))
  | GLambda _ as t ->
      let (name,s,t) = dest_GLambda t in
      let s = gterm2lp state s in
      under_binder ~loc name s None t state ~k:(fun name t state ->
        in_elpiast_lam ~loc name s (gterm2lp state t))
  | GLetIn _ as t ->
      let (name,bo , oty, t) = dest_GLetIn t in
      let bo = gterm2lp state bo in
      let ty =
        match oty with
        | None ->
            let { bound_list = args } = get_glob_env state in
            A.Term.mkVar ~loc (fresh_uv ())
              (List.map (fun x -> A.Term.mkBound ~loc ~language (name_of_id x)) args)
        | Some ty -> gterm2lp state ty in
      under_binder ~loc name ty (Some bo) t state ~k:(fun name t state ->
        in_elpiast_let ~loc name ~ty ~bo (gterm2lp state t))
  
  | GGenarg arg when !is_elpi_code arg ->
      let loc, text = !get_elpi_code arg in
      let ast = Q.elpi ~language:Q.elpi_language state loc text in
      if A.Term.is_spill_from_quotation ast then
        let { hyps } = get_glob_env state in
        if hyps = [] then ast
        else A.Term.extend_spill_hyp_from_quotation ast hyps
      else ast
  | GGenarg arg when !is_elpi_code_appArg arg ->
      begin match !get_elpi_code_appArg arg with
      | _, [] -> assert false
      | loc, hd :: stuff ->
          let stuff = List.map (fun s -> DAst.make ~loc:coqloc @@ GVar(Id.of_string s)) stuff in
          let stuff = List.map (gterm2lp state) stuff in
          let ast = Q.elpi ~language:Q.elpi_language state loc hd in
          A.Term.apply_elpi_var_from_quotation ast stuff
      end

  | GGenarg _ -> nYI "(glob)HOAS for GGenarg"

  | GHole GImpossibleCase ->  nYI "(glob)HOAS for GHole GImpossibleCase"
  | GHole (GNamedHole _) -> CErrors.user_err ~loc:coqloc Pp.(str"elpi: ?[name] syntax not supported")

  | GHole (GImplicitArg _|GInternalHole|GQuestionMark _|GBinderType _|GCasesType) when pattern -> A.Term.mkDiscard ~loc

  | GHole (GImplicitArg _) 
     (*A.Term.mkDiscard ~loc (* since the user did not write it, can override with @ *)*)
  | GHole (GBinderType _)
  | GHole GInternalHole
  | GHole GCasesType 
  | GHole (GQuestionMark _) ->
      let { bound_list = args } = get_glob_env state in
      let args = List.filter (fun n -> not(is_restricted_name n)) args in
      A.Term.mkVar ~loc (fresh_uv ())
        (List.map (fun x -> A.Term.mkBound ~loc ~language (name_of_id x)) (List.rev args))

  | GCast(t,_,c_ty) ->
      let t = gterm2lp state t in
      let c_ty = gterm2lp state c_ty in
      let id = Id.of_string "self" in
      let name = Names.Name.Name id in
      let self = A.Term.mkBound ~loc ~language (name_of_id id) in
      in_elpiast_let ~loc name ~bo:t ~ty:c_ty self

  | GEvar(_k,_subst) -> nYI "(glob)HOAS for GEvar"
  | GPatVar _ -> nYI "(glob)HOAS for GPatVar"
  
  | GProj ((ref,us),args,c) when
      Structures.PrimitiveProjections.mem ref &&
      List.for_all is_hole args ->
        let p = Option.get (Structures.PrimitiveProjections.find_opt ref) in
        let c = gterm2lp state c in
        let p = in_elpiast_primitive ~loc (Projection (Names.Projection.make p false)) in
        in_elpiast_appl ~loc p [c]

  | GProj ((ref,us),args,c) ->
      let hd = gterm2lp state (DAst.make (GRef (GlobRef.ConstRef ref,us))) in
      let args = CList.map (gterm2lp state) args in
      let c = gterm2lp state c in
      in_elpiast_appl ~loc hd (args@[c])

  | GApp(hd,args) ->
      let hd = gterm2lp state hd in
      let args = CList.map (gterm2lp state) args in
      in_elpiast_appl ~loc hd args

  | GLetTuple(kargs,(as_name,oty),t,b) ->
      let t = gterm2lp state t in
      let rt =
        match oty with
        | Some oty -> gterm2lp state DAst.(make (mkGLambda(as_name,Explicit,mkGHole,oty)))
        | None -> gterm2lp state mkGHole in
      let b =
        List.fold_right (fun name bo ->
          DAst.make (mkGLambda(name,Explicit,mkGHole,bo)))
        kargs b in
      let b = gterm2lp state b in
     in_elpiast_match ~loc t rt [b]

  | GCases(_, oty, [ t, (as_name, oind) ], bs) ->
      let open Declarations in
      let { env } = get_glob_env state in
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
      let t = gterm2lp state t in
      let rt =
        (* We try hard to stick in there the inductive type, so that
         * the term can be read back (mkCases needs the ind) *)
        (* TODO: add whd reduction in spine *)
        let ty =
          Inductive.type_of_inductive (indspecif,UVars.Instance.empty) in
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
             DAst.make (mkGLambda(as_name,Explicit,
               Glob_ops.mkGApp (DAst.make (GRef(GlobRef.IndRef ind,None))) (List.rev args),
               Option.default mkGHole oty))
          | Prod (name, src, tgt) when n = 0 ->
             let name, var, names = best_name name.Context.binder_name names in
             DAst.make (mkGLambda(name,Explicit,
               mkGHole,spine (n-1) (safe_tail names) (var :: args) tgt))
          | LetIn (name, v, _, b) ->
              spine n names args (Vars.subst1 v b)
          |  Cast (t, _, _) -> spine n names args t
          | Prod (_, _, t) ->
              spine (n-1) (safe_tail names) (mkGHole :: args) t 
          | _ -> assert false in
        gterm2lp state (spine mind_nparams args_name [] ty) in
      let bs =
        List.map (fun {CAst.v=(fv,pat,bo)} ->
          match List.map DAst.get pat with
          | [PatCstr((indc,cno as k),cargs,Name.Anonymous)] ->
               assert(Names.Ind.CanOrd.equal indc ind);
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
        match CList.find_map (function
             | `Case((_,n as k),vars,bo) when n = cno -> Some (k,vars,bo)
             | `Case _ -> None
             | `Def _ -> assert false) bs
        with
        | Some v -> v
        | None ->
          match def with
          | [`Def bo] ->
             let missing_k = ind,cno in
             let k_args = Inductiveops.constructor_nallargs (Global.env()) missing_k in
             missing_k, CList.make k_args Name.Anonymous, bo
          | _ ->
             err Pp.(str"Missing constructor "++Id.print mind_consnames.(i))) in
      let bs = CList.map (fun (k,vars,bo) ->
        let bo =
          List.fold_right (fun name bo ->
            DAst.make (mkGLambda(name,Explicit,mkGHole,bo)))
            vars bo in
        let bo = gterm2lp state bo in
        bo) bs in
      in_elpiast_match ~loc (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs
  | GCases _ -> nYI "(glob)HOAS complex match expression"
  | GIf  _ -> nYI "(glob)HOAS if-then-else"

  | GRec(GFix([|Some rno|],0),[|name|],[|tctx|],[|ty|],[|bo|]) ->
      let ty = glob_intros_prod tctx ty in
      let  ty = gterm2lp state ty in
      let bo = glob_intros tctx bo in
      under_binder ~loc (Name.Name name) ty None bo state ~k:(fun name t state ->
        in_elpiast_fix ~loc name rno ty (gterm2lp state bo))
  | GRec _ -> nYI "(glob)HOAS mutual/non-struct fix"
  | GInt i -> in_elpiast_primitive ~loc (Uint63 i)
  | GFloat f -> in_elpiast_primitive ~loc (Float64 f)
  | GString s -> in_elpiast_primitive ~loc (Pstring s)
  | GArray _ -> nYI "HOAS for persistent arrays"
  in
    gterm2lp state glob

let lconstr_eoi = Pcoq.eoi_entry Pcoq.Constr.lconstr

let parse_string f ?loc x =
  let offset = Option.map (fun l -> l.Loc.bp) loc in
  let strm = Gramlib.Stream.of_string ?offset x in
  Pcoq.Entry.parse f (Pcoq.Parsable.make ?loc strm)

let coq_quotation ~language state loc src =
  let cloc = to_coq_loc loc in
  let ce = parse_string ~loc:cloc lconstr_eoi src in
  (* Format.eprintf "quotation: %s in %s\n%!" src (Pp.string_of_ppcmds (Printer.pr_named_context_of (get_glob_env state).env (get_sigma state))); *)
  let glob = Constrintern.intern_constr (get_glob_env state).env (get_sigma state) ce in
  gterm2lpast ~language state glob

let coq = Q.register_named_quotation ~name:"coq" (coq_quotation ~pattern:false) ~descriptor:interp_quotations
let () = Rocq_elpi_HOAS.set_coq coq

let _coqpat = Q.register_named_quotation ~name:"pat" (coq_quotation ~pattern:true) ~descriptor:interp_quotations

let coq_quotation ~language:_ state loc src = coq_quotation ~language:coq state loc src 

(* Install the quotation *)
let () = Q.set_default_quotation (coq_quotation ~pattern:false) ~descriptor:interp_quotations

let _ = API.Quotation.register_named_quotation ~name:"gref" ~descriptor:interp_quotations
  (fun ~language state loc src ->
    let gr = locate_gref src in
    in_elpiast_gref ~loc gr)
;;
   
let gterm2lp ~loc ~base glob ~depth state =
  let t = gterm2lpast ~pattern:false ~language:coq state glob in
  let coq_ctx, _ = Option.default (upcast @@ mk_coq_context ~options:(default_options ()) state,[]) (get_ctx state) in
  let ctx = Names.Id.Map.fold (fun id i m ->
    API.Ast.Scope.Map.add (API.Ast.Name.from_string @@ Names.Id.to_string id,coq) i m
    ) coq_ctx.name2db API.Ast.Scope.Map.empty in
  handle_elpi_compiler_errors ~loc (fun () ->
    API.RawQuery.term_to_raw_term ~ctx state base ~depth t)

let runtime_gterm2lp ~loc ~base glob ~depth state =
  let t = gterm2lpast ~pattern:false ~language:coq state glob in
  let coq_ctx, _ = Option.default (upcast @@ mk_coq_context ~options:(default_options ()) state,[]) (get_ctx state) in
  let ctx = Names.Id.Map.fold (fun id i m ->
    API.Ast.Scope.Map.add (API.Ast.Name.from_string @@ Names.Id.to_string id,coq) i m
    ) coq_ctx.name2db API.Ast.Scope.Map.empty in
  handle_elpi_compiler_errors ~loc (fun () ->
    API.Utils.term_to_raw_term ~ctx state base ~depth t)

let rec gparams2lp ~loc ~base inp params (kont : depth:int -> S.t -> S.t * _) ~depth state =
  match params with
  | [] -> kont ~depth state
  | (name,imp,ob,src) :: params ->
      if ob <> None then Rocq_elpi_utils.nYI "defined parameters in a record/inductive declaration";
      let state, src = gterm2lp ~loc ~depth ~base src state in
      let k = nogls (gparams2lp ~loc ~base inp params kont) in
      let state, tgt, () = under_ctx name src None ~k ~depth state in
      let state, imp = in_elpi_imp ~depth state imp in
      state, inp name ~imp src tgt

let drop_relevance (a,_,c,d,e) = (a,c,d,e)
    
let gindparams2lp ~loc ~base params ~k ~depth s =
  gparams2lp ~loc ~base in_elpi_inductive_parameter (List.map drop_relevance params) k ~depth s
let garityparams2lp ~loc ~base params ~k ~depth s =
  gparams2lp ~loc ~base in_elpi_arity_parameter(List.map drop_relevance params) k ~depth s
  
let garity2lp ~loc ~base t ~depth state =
  let state, t = gterm2lp ~loc t ~depth ~base state in
  state, in_elpi_arity t

let rec gfields2lp ~loc ~base fields ~depth state =
  match fields with
  | [] -> state, in_elpi_indtdecl_endrecord ()
  | (f,({ name; is_coercion; is_canonical } as att)) :: fields ->
      let state, f = gterm2lp ~loc ~base f ~depth state in
      let state, fields, () = under_ctx name f None ~k:(nogls (gfields2lp ~loc ~base fields)) ~depth state in
      in_elpi_indtdecl_field ~depth state att f fields

let grecord2lp ~loc ~base ~name ~constructorname arity fields ~depth state =
  let space, record_name = name in
  let qrecord_name = Id.of_string_soft @@ String.concat "." (space @ [Id.to_string record_name]) in
  let state, arity = gterm2lp ~loc ~base arity ~depth state in
  let state, fields = gfields2lp ~loc ~base fields ~depth state in
  let constructor = match constructorname with
    | None -> Name.Name (Id.of_string ("Build_" ^ Id.to_string record_name))
    | Some x -> Name.Name x in
  state, in_elpi_indtdecl_record (Name.Name qrecord_name) arity constructor fields


 let gterm2lpast = gterm2lpast ~language:coq
