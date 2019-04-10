(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module E = Elpi_API.Extend.Data
module EC = Elpi_API.Extend.Compile
open Coq_elpi_HOAS

open Names
open Coq_elpi_utils

(* ***************** {{ quotation }} for Glob_terms ********************** *)

open Glob_term

(* Set by the parser that declares an ARGUMENT EXTEND to Coq *)
let is_elpi_code = ref (fun _ -> assert false)
let get_elpi_code = ref (fun _ -> assert false)

let pp_qctx fmt m =
  Id.Map.iter (fun name d ->
    Format.fprintf fmt "%s |-> %d" (Id.to_string name) d) m

let get_ctx, set_ctx, update_ctx =
  let bound_vars =
    EC.State.declare ~name:"coq-elpi:glob-quotation-bound-vars"
      ~init:(fun () -> Id.Map.empty) ~pp:pp_qctx in
  EC.State.(get bound_vars, set bound_vars, update bound_vars)

let set_glob_ctx = set_ctx

let glob_intros ctx bo =
  List.fold_right (fun (name,_,ov,ty) bo ->
     DAst.make
     (match ov with
     | None -> GLambda(name,Decl_kinds.Explicit,ty,bo)
     | Some v -> GLetIn(name,v,Some ty,bo)))
   ctx bo
;;
let glob_intros_prod ctx bo =
  List.fold_right (fun (name,_,ov,ty) bo ->
     DAst.make
     (match ov with
     | None -> GProd(name,Decl_kinds.Explicit,ty,bo)
     | Some v -> GLetIn(name,v,Some ty,bo)))
   ctx bo
;;


let under_ctx name f depth state x =
  let orig_ctx = get_ctx state in
  let state =
    match name with
    | Name id -> update_ctx state (Id.Map.add id depth)
    | Anonymous -> state in
  let state, y = f (depth+1) (cc_push_env state (Context.make_annot name Sorts.Relevant)) x in
  let state = set_ctx state orig_ctx in
  state, y

let rec gterm2lp depth state x = match (DAst.get x) (*.CAst.v*) with
  | GRef(gr,_ul) -> state, in_elpi_gr gr
  | GVar(id) ->
      let ctx = get_ctx state in
      if not (Id.Map.mem id ctx) then
        CErrors.user_err ~hdr:"elpi quatation" Pp.(str"Unknown Coq global " ++ Names.Id.print id);
      state, E.mkConst (Id.Map.find id ctx)
  | GSort GSProp -> state, in_elpi_sort Sorts.sprop
  | GSort(GProp) -> state, in_elpi_sort Sorts.prop
  | GSort(GSet) -> state, in_elpi_sort Sorts.set
  | GSort(GType []) ->
      let state, _, s = EC.fresh_Arg state ~name_hint:"type" ~args:[] in
      state, in_elpi_flex_sort s
  | GSort(GType _) -> nYI "(glob)HOAS for Type@{i j}"

  | GProd(name,_,s,t) ->
      let state, s = gterm2lp depth state s in
      let state, t =  under_ctx name gterm2lp depth state t in
      state, in_elpi_prod name s t
  | GLambda(name,_,s,t) ->
      let state, s = gterm2lp depth state s in
      let state, t = under_ctx name gterm2lp depth state t in
      state, in_elpi_lam name s t
  | GLetIn(name,bo , oty, t) ->
      let state, bo = gterm2lp depth state bo in
      let state, ty =
        match oty with
        | None -> state, in_elpi_implicit
        | Some ty -> gterm2lp depth state ty in
      let state, t = under_ctx name gterm2lp depth state t in
      state, in_elpi_let name bo ty t

  | GHole(_,_,Some arg) when !is_elpi_code arg ->
      EC.lp ~depth state (!get_elpi_code arg)
  | GHole _ -> state, in_elpi_implicit

  | GCast(t,(Glob_term.CastConv c_ty | Glob_term.CastVM c_ty | Glob_term.CastNative c_ty)) ->
      let state, t = gterm2lp depth state t in
      let state, c_ty = gterm2lp depth state c_ty in
      let self = E.mkConst depth in
      state, in_elpi_let Names.Name.Anonymous t c_ty self
  | GCast _ -> nYI "(glob)HOAS for GCast"
      

  | GEvar(_k,_subst) -> nYI "(glob)HOAS for GEvar"
  | GPatVar _ -> nYI "(glob)HOAS for GPatVar"
(*   | GProj _ -> nYI "(glob)HOAS for GProj" *)

  | GApp(hd,args) ->
      let state, hd = gterm2lp depth state hd in
      let state, args = CList.fold_left_map (gterm2lp depth) state args in
      if EC.is_Arg state hd then
        state, in_elpi_app_Arg ~depth hd args
      else
        state, in_elpi_appl hd args
  
  | GCases(_, oty, [ t, (as_name, oind) ], bs) ->
      let open Declarations in
      let env = cc_get_env state in
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
      let state, t = gterm2lp depth state t in
      let state, rt =
        (* We try hard to stick in there the inductive type, so that
         * the term can be read back (mkCases needs the ind) *)
        (* XXX fixme reduction *)
        let ty =
          Inductive.type_of_inductive env (indspecif,Univ.Instance.empty) in
        let safe_tail = function [] -> [] | _ :: x -> x in
        let best_name n l = match n, l with
          | _, (Name x) :: rest -> Name x,DAst.make (GVar x), rest
          | Name x, _ :: rest -> Name x,DAst.make (GVar x), rest
          | Anonymous, Anonymous :: rest -> Anonymous,mkGHole, rest
          | Name x, [] -> Name x,DAst.make (GVar x), []
          | Anonymous, [] -> Anonymous,mkGHole, [] in
        let mkGapp hd args =
          List.fold_left (Glob_ops.mkGApp ?loc:None) (DAst.make hd) args in
        let rec spine n names args ty =
          match Term.kind_of_type ty with
          | Term.SortType _ ->
             DAst.make (GLambda(as_name,Decl_kinds.Explicit,
               mkGapp (GRef(Globnames.IndRef ind,None)) (List.rev args),
               Option.default mkGHole oty))
          | Term.ProdType(name,src,tgt) when n = 0 -> 
             let name, var, names = best_name name.Context.binder_name names in
             DAst.make (GLambda(name,Decl_kinds.Explicit,
               mkGHole,spine (n-1) (safe_tail names) (var :: args) tgt))
          | Term.LetInType(name,v,_,b) ->
              spine n names args (Vars.subst1 v b)
          | Term.CastType(t,_) -> spine n names args t
          | Term.ProdType(_,_,t) ->
              spine (n-1) (safe_tail names) (mkGHole :: args) t 
          | Term.AtomicType _ -> assert false in
        gterm2lp depth state (spine mind_nparams args_name [] ty) in
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
             let k_args = Inductiveops.constructor_nallargs env missing_k in
             missing_k, CList.make k_args Name.Anonymous, bo
          | _ ->
             err Pp.(str"Missing constructor "++Id.print mind_consnames.(i))) in
      let state, bs = CList.fold_left_map (fun state (k,vars,bo) ->
        let bo =
          List.fold_right (fun name bo ->
            DAst.make (GLambda(name,Decl_kinds.Explicit,mkGHole,bo)))
            vars bo in
        let state, bo = gterm2lp depth state bo in
        state, bo) state bs in
      state, in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs
  | GCases _ -> nYI "(glob)HOAS complex match expression"
  | GLetTuple _ -> nYI "(glob)HOAS destructuring let"
  | GIf  _ -> nYI "(glob)HOAS if-then-else"

  | GRec(GFix([|Some rno,GStructRec|],0),[|name|],[|tctx|],[|ty|],[|bo|]) ->
      let ty = glob_intros_prod tctx ty in
      let state, ty = gterm2lp depth state ty in
      let bo = glob_intros tctx bo in
      let ctx = get_ctx state in
      let state = update_ctx state (Id.Map.add name depth) in
      let state, bo = gterm2lp (depth+1) state bo in
      let state = set_ctx state ctx in
      state, in_elpi_fix (Name name) rno ty bo
  | GRec _ -> nYI "(glob)HOAS mutual/non-struct fix"
  | GInt _ -> nYI "(glob)HOAS primitive machine integers"
;;

(* Install the quotation *)
let () = EC.set_default_quotation (fun ~depth state src ->
  let ce = Pcoq.parse_string Pcoq.Constr.lconstr src in
  gterm2lp depth state (Constrintern.intern_constr (cc_get_env state) (cc_get_evd state) ce))
;;

let gterm2lp ~depth state t = gterm2lp depth state t

