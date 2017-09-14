(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module E = Elpi_API.Extend.Data
module EC = Elpi_API.Extend.Compile
module C = Constr
open Coq_elpi_HOAS

open Names
open Coq_elpi_utils

(* ***************** {{ quotation }} for Glob_terms ********************** *)

open Glob_term
open Misctypes

(* Set by the parser that declares an ARGUMENT EXTEND to Coq *)
let is_coq_string = ref (fun _ -> assert false)
let get_coq_string = ref (fun _ -> assert false)

let pp_qctx fmt m =
  Id.Map.iter (fun name d ->
    Format.fprintf fmt "%s |-> %d" (Id.to_string name) d) m

let get_ctx, set_ctx, update_ctx =
  let bound_vars =
    EC.State.declare ~name:"coq-elpi:glob-quotation-bound-vars"
      ~init:(fun () -> Id.Map.empty) ~pp:pp_qctx in
  EC.State.(get bound_vars, set bound_vars, update bound_vars)

let glob_intros ctx bo =
  List.fold_right (fun (name,_,ov,ty) bo ->
     CAst.make
     (match ov with
     | None -> GLambda(name,Decl_kinds.Explicit,ty,bo)
     | Some v -> GLetIn(name,v,Some ty,bo)))
   ctx bo
;;

let under_ctx name f depth state x =
  let orig_ctx = get_ctx state in
  let state =
    match name with
    | Name id -> update_ctx state (Id.Map.add id depth)
    | Anonymous -> state in
  let state, y = f (depth+1) (push_env state name) x in
  let state = set_ctx state orig_ctx in
  state, y

let rec gterm2lp depth state x = match x.CAst.v with
  | GRef(gr,_ul) -> state, in_elpi_gr gr
  | GVar(id) ->
      let ctx = get_ctx state in
      if not (Id.Map.mem id ctx) then
        CErrors.anomaly Pp.(str"Unknown Coq global " ++ Names.Id.print id);
      state, E.Constants.of_dbl (Id.Map.find id ctx)
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

  | GHole(_,_,Some arg) when !is_coq_string arg ->
      EC.lp ~depth state (!get_coq_string arg)
  | GHole _ -> state, in_elpi_implicit

  | GCast(t,(CastConv c_ty | CastVM c_ty | CastNative c_ty)) ->
      let state, t = gterm2lp depth state t in
      let state, c_ty = gterm2lp depth state c_ty in
      let self = E.Constants.of_dbl depth in
      state, in_elpi_let Names.Name.Anonymous t c_ty self
  | GCast _ -> nYI "(glob)HOAS for GCast"
      

  | GEvar(_k,_subst) -> nYI "(glob)HOAS for GEvar"
  | GPatVar _ -> nYI "(glob)HOAS for GPatVar"

  | GApp(hd,args) ->
      let state, hd = gterm2lp depth state hd in
      let state, args = CList.fold_map (gterm2lp depth) state args in
      if EC.is_Arg state hd then
        state, in_elpi_app_Arg hd args
      else
        state, in_elpi_appl hd args
  
  | GCases(_, oty, [ t, (as_name, oind) ], bs) ->
      let open Declarations in
      let env = get_env state in
      let ind, args_name =
        match oind with
        | Some(_,(ind, arg_names)) -> ind, arg_names
        | None ->
            match bs with
            | (_,(_,[{CAst.v = PatCstr((ind,_),_,_)}],_)) :: _ -> ind, []
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
          | _, (Name x) :: rest -> Name x,CAst.make (GVar x), rest
          | Name x, _ :: rest -> Name x,CAst.make (GVar x), rest
          | Anonymous, Anonymous :: rest -> Anonymous,mkGHole, rest
          | Name x, [] -> Name x,CAst.make (GVar x), []
          | Anonymous, [] -> Anonymous,mkGHole, [] in
        let mkGapp hd args =
          List.fold_left (Glob_ops.mkGApp ?loc:None) (CAst.make hd) args in
        let rec spine n names args ty =
          match Term.kind_of_type ty with
          | Term.SortType _ ->
             CAst.make (GLambda(as_name,Decl_kinds.Explicit,
               mkGapp (GRef(Globnames.IndRef ind,None)) (List.rev args),
               Option.default mkGHole oty))
          | Term.ProdType(name,src,tgt) when n = 0 -> 
             let name, var, names = best_name name names in
             CAst.make (GLambda(name,Decl_kinds.Explicit,
               mkGHole,spine (n-1) (safe_tail names) (var :: args) tgt))
          | Term.LetInType(name,v,_,b) ->
              spine n names args (Vars.subst1 v b)
          | Term.CastType(t,_) -> spine n names args t
          | Term.ProdType(_,_,t) ->
              spine (n-1) (safe_tail names) (mkGHole :: args) t 
          | Term.AtomicType _ -> assert false in
        gterm2lp depth state (spine mind_nparams args_name [] ty) in
      let bs =
        List.map (fun (_,(fv,pat,bo)) ->
          match pat with
          | [{CAst.v = PatCstr((indc,cno as k),cargs,Name.Anonymous)}] ->
               assert(Names.eq_ind indc ind);
               let cargs = List.map (function
                 | {CAst.v = PatVar n} -> n
                 | _ -> nYI "(glob)HOAS match deep pattern") cargs in
               `Case(k,cargs,bo)
          | [{CAst.v = PatVar Name.Anonymous}] ->
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
             let k_args = Inductiveops.constructor_nallargs missing_k in
             missing_k, CList.make k_args Name.Anonymous, bo
          | _ ->
             err Pp.(str"Missing constructor "++Id.print mind_consnames.(i))) in
      let state, bs = CList.fold_map (fun state (k,vars,bo) ->
        let bo =
          List.fold_right (fun name bo ->
            CAst.make (GLambda(name,Decl_kinds.Explicit,mkGHole,bo)))
            vars bo in
        let state, bo = gterm2lp depth state bo in
        state, bo) state bs in
      state, in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs
  | GCases _ -> nYI "(glob)HOAS complex match expression"
  | GLetTuple _ -> nYI "(glob)HOAS destructuring let"
  | GIf  _ -> nYI "(glob)HOAS if-then-else"

  | GRec(GFix([|Some rno,GStructRec|],0),[|name|],[|tctx|],[|ty|],[|bo|]) ->
      let state, ty = gterm2lp depth state ty in
      let bo = glob_intros tctx bo in
      let ctx = get_ctx state in
      let state = update_ctx state (Id.Map.add name depth) in
      let state, bo = gterm2lp (depth+1) state bo in
      let state = set_ctx state ctx in
      state, in_elpi_fix (Name name) rno ty bo
  | GRec _ -> nYI "(glob)HOAS mutual/non-struct fix"
;;

(* Install the quotation *)
let () = EC.set_default_quotation (fun ~depth state src ->
  let ce = Pcoq.parse_string Pcoq.Constr.lconstr src in
  gterm2lp depth state (Constrintern.intern_constr (get_env state) ce))
;;

