(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi_API
module E = API.Extend.Data
module CD = struct
  include API.Extend.CData
  include API.Extend.Data.C
end
module U = API.Extend.Utils
module CC = API.Extend.Compile
module P = API.Extend.Pp
open Coq_elpi_utils
open Coq_elpi_HOAS
open Names

let debug = false

let declare_evc = E.Constants.from_stringc "declare-evar"
let solvec = E.Constants.from_stringc "solve"
let goalc = E.Constants.from_stringc "goal"
let nablac = E.Constants.from_stringc "nabla"
let goal_namec = E.Constants.from_stringc "goal-name"

let in_elpi_evar_concl t k (_, ctx_len as ctx) ~scope hyps ~depth state =
  let state, t = cc_constr2lp ctx ~depth state t in
  let args = CList.init scope E.mkConst in
  let state, c = cc_in_elpi_evar state k in
  let hyps = List.map (fun (t,from) -> U.move ~from ~to_:depth t) hyps in
  state, U.list_to_lp_list hyps, (Coq_elpi_utils.mkApp ~depth c args), t

let in_elpi_evar_declaration ~hyps ~ev ~ty =
  E.mkApp declare_evc hyps [ev; ty]

let mk_goal hyps ev ty attrs =
  E.mkApp goalc hyps [ev;ty; U.list_to_lp_list attrs]
let in_elpi_solve ?goal_name ~hyps ~ev ~ty ~args ~new_goals =
  let name = match goal_name with None -> Anonymous | Some x -> Name x in
  let name = E.mkApp goal_namec (in_elpi_name name) [] in
  E.mkApp solvec args [E.mkCons (mk_goal hyps ev ty [name]) E.mkNil;new_goals]

let info_of_evar evd section env k =
  let open Context.Named in
  let { Evd.evar_concl } as info =
    Evarutil.nf_evar_info evd (Evd.find evd k) in
  let filtered_hyps = Evd.evar_filtered_hyps info in
  let ctx = Environ.named_context_of_val filtered_hyps in
  let ctx = ctx |> List.filter (fun x ->
    not(CList.mem_f Id.equal (Declaration.get_id x) section)) in
  evar_concl, ctx, Environ.reset_with_named_context filtered_hyps env

let cc_info_of_evar state k =
  let evd = cc_get_evd state in
  let section = cc_get_names_ctx state in
  let env = cc_get_env state in
  info_of_evar evd section env k
let cs_info_of_evar state k =
  let evd = cs_get_evd state in
  let section = cs_get_names_ctx state in
  let env = cs_get_env state in
  info_of_evar evd section env k

let in_elpi_evar_info ~depth state k =
  let evar_concl, ctx, _ = cc_info_of_evar state k in
  cc_in_elpi_ctx ~depth state ctx (fun (ctx, ctx_len) _ hyps ~depth state ->
    let state, hyps, ev, ty =
      in_elpi_evar_concl evar_concl k (ctx,ctx_len) ~scope:ctx_len hyps ~depth state in
    state, in_elpi_evar_declaration ~hyps ~ev ~ty)

let reachable_evarmap evd goal =
  let rec aux s =
    let s'=
      Evar.Set.fold (fun k s -> Evar.Set.union s 
        (Evarutil.undefined_evars_of_evar_info evd (Evd.find evd k))) s s in
    if Evar.Set.equal s s' then s else aux s' in
  aux (Evar.Set.singleton goal)

type parsed_term =
  Ltac_plugin.Tacinterp.interp_sign * Tacexpr.glob_constr_and_expr

type arg = String of string | Int of int | Term of parsed_term

let strc = E.Constants.from_stringc "str"
let trmc = E.Constants.from_stringc "trm"
let intc = E.Constants.from_stringc "int"

let in_elpi_arg ~depth goal_env name_map evd state = function
  | String x -> state, E.mkApp strc (CD.of_string x) []
  | Int x -> state, E.mkApp intc (CD.of_int x) []
  | Term (ist,glob_or_expr) ->
      let closure = Ltac_plugin.Tacinterp.interp_glob_closure ist goal_env evd glob_or_expr in
      let g = Detyping.detype_closed_glob false [] goal_env evd closure in
      let state =
        Coq_elpi_glob_quotation.set_glob_ctx state name_map in
      let state, t =
        Coq_elpi_glob_quotation.gterm2lp ~depth state g in
      state, E.mkApp trmc t []

let goal2query evd goal ?main args ~depth state =
  let state = cc_set_command_mode state false in (* tactic mode *)
  let state = cc_set_evd state evd in
  if not (Evd.is_undefined evd goal) then
    err Pp.(str (Printf.sprintf "Evar %d is not a goal" (Evar.repr goal)));
  let evar_concl, goal_ctx, goal_env = cc_info_of_evar state goal in
  let goal_name = Evd.evar_ident goal evd in
  let state, query =
    cc_in_elpi_ctx ~depth state goal_ctx
     ~mk_ctx_item:(fun _ t -> E.mkApp E.Constants.pic (E.mkLam t) [])
     (fun (ctx, ctx_len) name_nmap hyps ~depth state ->
      match main with
      | None ->
          let state, hyps, ev, goal_ty =
            in_elpi_evar_concl evar_concl goal
              (ctx, ctx_len) ~scope:ctx_len hyps ~depth state in
          let state, new_goals_name, new_goals =
            cc_mkArg ~name_hint:"NewGoals" ~lvl:ctx_len state in
          let state = cc_set_new_goals state new_goals_name in
          let state, args =
            CList.fold_map (in_elpi_arg ~depth goal_env name_nmap evd) state args in
          let args = U.list_to_lp_list args in
          let q = in_elpi_solve ?goal_name ~hyps ~ev ~ty:goal_ty ~args ~new_goals in
          state, q
      | Some text -> CC.lp ~depth state text) in
  let state, evarmap_query = Evar.Set.fold (fun k (state, q) ->
     let state, e = in_elpi_evar_info ~depth state k in
     state, E.mkApp E.Constants.andc e [q])
    (reachable_evarmap evd goal) (state, query) in
  state, evarmap_query

let in_elpi_global_arg ~depth global_env state arg =
  in_elpi_arg ~depth global_env Names.Id.Map.empty
    (Evd.from_env global_env) state arg

let eat_n_lambdas ~depth t upto =
  let open E in
  let rec aux n t =
    if n = upto then t
    else match look ~depth:(depth+n) t with
      | Lam t -> aux (n+1) t
      | UVar(r,d,a) -> aux (n+1) (mkUVar r d (a+1))
      | AppUVar(r,d,a) -> aux (n+1) (mkAppUVar r d (a@[mkConst n]))
      | _ -> assert false
  in
    aux 0 t

open API.Data
         
let rec get_goal_ref depth t =
  match E.look ~depth t with
  | E.App(c,_,[ev;_;_]) when c == goalc ->
     begin match E.look ~depth ev with
     | (E.UVar(r,_,_)|E.AppUVar(r,_,_)) -> r
     | _ -> err Pp.(str"Not a variable " ++ str(pp2string (P.term depth) ev))
     end
  | E.App(c,g,[]) when c == nablac ->
     begin match E.look ~depth g with
     | E.Lam g -> get_goal_ref (depth+1) g
     | _ -> err Pp.(str"Not a lambda " ++ str(pp2string (P.term depth) g))
     end
  | _ -> err Pp.(str"Not a goal " ++ str(pp2string (P.term depth) t))

let no_list_given = function
  | E.Discard | E.UVar _ | E.AppUVar _ -> true
  | _ -> false

let rec skip_lams ~depth d t = match E.look ~depth t with
  | E.Lam t -> skip_lams ~depth:(depth+1) (d+1) t
  | x -> x, d

let in_coq_solution {
   assignments; custom_constraints; constraints
 } =
   let solution2ev = cs_get_solution2ev custom_constraints in
   let syntactic_constraints = E.constraints constraints in
   let state = custom_constraints in
   let state = cs_set_ref2evk state [] in
   let state =
     CString.Map.fold (fun name k state ->
       let t = StrMap.find name assignments in
       let _, ctx, _ = cs_info_of_evar state k in 
       let names, n_names = 
         Context.Named.fold_inside
           (fun (acc,n) x ->
              Name (Context.Named.Declaration.get_id x) :: acc, n+1)
           ~init:([],0) ctx in
      if debug then
        Feedback.msg_debug Pp.(str"solution: ctx=" ++
          pr_sequence Name.print names ++ str" depth=" ++ int n_names ++
          str " term=" ++ str(pp2string (P.term 0)
            (E.of_term t)));
       let t = eat_n_lambdas ~depth:0 (E.of_term t) n_names in
       let state, t =
         cs_lp2constr syntactic_constraints state (names, n_names) ~depth:n_names t in
       let evd = cs_get_evd state in
       if debug then
         Feedback.msg_debug Pp.(str"solution: constr=" ++ Printer.pr_constr t
           ++ spc()++str "evd=" ++ Termops.pr_evar_map None evd);
       let evd = Evd.define k t evd in
       if debug then
         Feedback.msg_debug Pp.(str"solution: constr=" ++ Printer.pr_constr t
           ++ spc()++str "evd=" ++ Termops.pr_evar_map None evd);
       cs_set_evd state evd)
     solution2ev state in
   let ref2evk = cs_get_ref2evk state in
   let all_goals = List.map snd ref2evk in
   let declared_goals, shelved_goals =
     match cs_get_new_goals state with
     | None -> all_goals, [] 
     | Some arg_name ->
         let t = StrMap.find arg_name assignments in
         let l, depth = skip_lams ~depth:0 0 (E.of_term t) in
         if no_list_given l then all_goals, []
         else
           let l = U.lp_list_to_list ~depth (E.kool l) in
           let declared = List.map (get_goal_ref depth) l in
           let declared = List.map (fun x -> List.assq x ref2evk) declared in
           let declared_set =
             List.fold_right Evar.Set.add declared Evar.Set.empty in
           declared,
           List.filter (fun x -> not(Evar.Set.mem x declared_set)) all_goals
   in
   cs_get_evd state, declared_goals, shelved_goals

let tclSOLUTION2EVD solution =
   let evd, declared_goals, shelved_goals = in_coq_solution solution in
   let open Proofview.Unsafe in
   let open Tacticals.New in
   tclTHEN
     (tclEVARS evd)
     (tclTHEN (tclSETGOALS declared_goals)
              (Proofview.shelve_goals shelved_goals))


