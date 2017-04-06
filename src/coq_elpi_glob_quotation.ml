(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module E = Elpi_runtime
module C = Constr
open Coq_elpi_HOAS

open Names
open Coq_elpi_utils

(* ***************** {{ quotation }} for Glob_terms ********************** *)

open Glob_term

let is_coq_string = ref (fun _ -> assert false)
let get_coq_string = ref (fun _ -> assert false)

let env = "elpi-coq:env"
let get_env, set_env =
  Elpi_util.ExtState.declare_extension env (fun () -> Global.env (), [])
;;
let push_env name depth (env, ctx) =
  Environ.(push_rel (Context.Rel.Declaration.LocalAssum(name,C.mkProp)) env),
  (name, depth) :: ctx
;;

let glob_intros ctx bo =
  List.fold_right (fun (name,_,ov,ty) bo ->
     match ov with
     | None -> GLambda(Loc.ghost,name,Decl_kinds.Explicit,ty,bo)
     | Some v -> GLetIn(Loc.ghost,name,v,Some ty,bo))
   ctx bo
;;

let rec gterm2lp depth state = function
  | GRef(_,gr,_ul) -> state, in_elpi_gr gr
  | GVar(_,id) ->
      let _, ctx = get_env state in
      if not (List.mem_assoc (Names.Name.Name id) ctx) then
        CErrors.anomaly Pp.(str"Unknown Coq global " ++ Names.Id.print id);
      state, E.Constants.of_dbl (List.assoc (Names.Name.Name id) ctx)
  | GSort(_, Misctypes.GProp) -> state, in_elpi_sort Sorts.prop
  | GSort(_, Misctypes.GSet) -> state, in_elpi_sort Sorts.set
  | GSort(_, Misctypes.GType []) ->
      let dp = Global.current_dirpath () in
      state, in_elpi_sort (Sorts.Type (Universes.new_univ dp))
  | GSort(_, Misctypes.GType _) -> nYI "(glob)HOAS for Type@{i j}"

  | GProd(_,name,_,s,t) ->
      let state, s = gterm2lp depth state s in
      let env = get_env state in
      let state = set_env state (push_env name depth) in
      let state, t = gterm2lp (depth+1) state t in
      let state = set_env state (fun _ -> env) in
      state, in_elpi_prod name s t
  | GLambda(_,name,_,s,t) ->
      let state, s = gterm2lp depth state s in
      let env = get_env state in
      let state = set_env state (push_env name depth) in
      let state, t = gterm2lp (depth+1) state t in
      let state = set_env state (fun _ -> env) in
      state, in_elpi_lam name s t
  | GLetIn(_,name,bo , oty, t) ->
      let state, bo = gterm2lp depth state bo in
      let state, ty =
        match oty with
        | None -> state, in_elpi_implicit
        | Some ty -> gterm2lp depth state ty in
      let env = get_env state in
      let state = set_env state (push_env name depth) in
      let state, t = gterm2lp (depth+1) state t in
      let state = set_env state (fun _ -> env) in
      state, in_elpi_let name bo ty t

  | GHole(_,_,_,Some arg) when !is_coq_string arg ->
      E.Quotations.lp ~depth state (!get_coq_string arg)
  | GHole _ -> state, in_elpi_implicit

  | GCast(_,t,c_ty) -> nYI "(glob)HOAS for GCast"
  | GEvar(_,_k,_subst) -> nYI "(glob)HOAS for GEvar"
  | GPatVar _ -> nYI "(glob)HOAS for GPatVar"

  | GApp(_,hd,args) ->
      let state, hd = gterm2lp depth state hd in
      let state, args = Elpi_util.map_acc (gterm2lp depth) state args in
      state, in_elpi_appl hd args
  
  | GCases(_,_, oty, [ t, (name, oind) ], bs) ->
      let ind, oty =
        match oind, oty with
        | Some(_,ind,_args), _ -> ind, oty
        | None, _ ->
            match bs with
            | (_,_,[PatCstr(_,(ind,_),_,_)],_) :: _ -> ind, oty
            | _ -> assert false in
(*
      let { C.ci_ind; C.ci_npar; C.ci_cstr_ndecls; C.ci_cstr_nargs } =
        Inductiveops.make_case_info (Global.env()) ind C.RegularStyle in
*)
      let { Declarations.mind_packets }, { Declarations.mind_consnames } =
        Inductive.lookup_mind_specif (Global.env()) ind in
      let no_constructors = Array.length mind_consnames in
      assert(Array.length mind_packets = 1);
      let state, t = gterm2lp depth state t in
      let state, rt =
        match oty with
        | None -> state, in_elpi_implicit
        | Some ty -> nYI "(glob)HOAS match oty" in
      let bs =
        List.map (fun (_,fv,pat,bo) ->
          match pat with
          | [PatCstr(_,(indc,cno as k),cargs,Name.Anonymous)] ->
               assert(Names.eq_ind indc ind);
               let cargs = List.map (function
                 | PatVar(_,n) -> n
                 | _ -> nYI "(glob)HOAS match deep pattern") cargs in
               `Case(k,cargs,bo)
          | [PatVar(_,Name.Anonymous)] ->
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
             err Pp.(str"Missing constructor " ++ Id.print mind_consnames.(i))) in
      let state, bs = Elpi_util.map_acc (fun state (k,ctx,bo) ->
        let env = get_env state in
        let bo =
          List.fold_right (fun name bo ->
            GLambda(Loc.ghost,name,Decl_kinds.Explicit,mkGHole,bo))
            ctx bo in
        let state, bo = gterm2lp depth state bo in
        let state = set_env state (fun _ -> env) in
        state, bo) state bs in
      state, in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs
  | GCases _ -> nYI "(glob)HOAS complex match expression"
  | GLetTuple _ -> nYI "(glob)HOAS destructuring let"
  | GIf  _ -> nYI "(glob)HOAS if-then-else"

  | GRec(_,GFix([|Some rno,GStructRec|],0),[|name|],[|tctx|],[|ty|],[|bo|]) ->
      let state, ty = gterm2lp depth state ty in
      let bo = glob_intros tctx bo in
      let name = Name.Name name in
      let env = get_env state in
      let state = set_env state (push_env name depth) in
      let state, bo = gterm2lp (depth+1) state bo in
      let state = set_env state (fun _ -> env) in
      state, in_elpi_fix name rno ty bo
  | GRec _ -> nYI "(glob)HOAS mutual/non-struct fix"
;;

(* Install the quotation *)
let () = E.Quotations.set_default_quotation (fun ~depth state src ->
  if !Coq_elpi_utils.debug then Feedback.msg_debug Pp.(str "Q:" ++ str src);
  let ce = Pcoq.parse_string Pcoq.Constr.lconstr src in
  try gterm2lp depth state (Constrintern.intern_constr (fst (get_env state)) ce)
  with E.Constants.UnknownGlobal s ->
    err Pp.(str"Unknown elpi global name "++str s))
;;

