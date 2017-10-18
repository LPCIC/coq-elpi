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
open Names
open Coq_elpi_utils
open Coq_elpi_HOAS

let reachable_evarmap evd goal =
  let rec aux s =
    let s'=
      Evar.Set.fold (fun k s -> Evar.Set.union s 
        (Evarutil.undefined_evars_of_evar_info evd (Evd.find evd k))) s s in
    if Evar.Set.equal s s' then s else aux s' in
  Evar.Set.remove goal (aux (Evar.Set.singleton goal))

let on_Compile_state f = function
  | Compile s -> fun x -> let s, x = f s x in Compile s, x
  | _ -> assert false
let on_Compile_state1 f = function
  | Compile s -> fun x -> Compile(f s x)
  | _ -> assert false

type parsed_term =
  Ltac_plugin.Tacinterp.interp_sign * Tacexpr.glob_constr_and_expr

type arg = String of string | Term of parsed_term

let strc = E.Constants.from_stringc "str"
let trmc = E.Constants.from_stringc "trm"

let in_elpi_arg ~depth goal_env name_map evd state = function
  | String x -> state, E.App(strc,CD.of_string x,[])
  | Term (ist,glob_or_expr) ->
      let closure = Ltac_plugin.Tacinterp.interp_glob_closure ist goal_env evd glob_or_expr in
      let g = Detyping.detype_closed_glob false [] goal_env evd closure in
      let state =
        on_Compile_state1 Coq_elpi_glob_quotation.set_glob_ctx state name_map in
      let state, t =
        on_Compile_state (Coq_elpi_glob_quotation.gterm2lp ~depth) state g in
      state, E.App(trmc,t,[])

let goal2query evd goal ?main args ~depth state =
  let state = set_command_mode state false in (* tactic mode *)
  let state = set_evar_map state evd in
  let state = Compile state in
  if not (Evd.is_undefined evd goal) then
    err Pp.(str (Printf.sprintf "Evar %d is not a goal" (Evar.repr goal)));
  let evar_concl, goal_ctx, goal_env = info_of_evar state goal in
  let goal_name = Evd.evar_ident goal evd in
  let state, query =
    in_elpi_ctx ~depth state goal_ctx
     (fun (ctx, ctx_len) name_nmap hyps ~depth state ->
      match main with
      | None ->
          let refined_ev = E.Constants.of_dbl depth in
          let depth = depth + 1 in (* the sigma Refinedgoal\ *)
          let state, args = CList.fold_map (in_elpi_arg ~depth goal_env name_nmap evd) state args in
          let args = U.list_to_lp_list args in
          let state, hyps, ev, goal_ty =
            in_elpi_evar_concl evar_concl goal
              (ctx @ [Anonymous], ctx_len+1) ~scope:ctx_len hyps ~depth state in
          let g = in_elpi_goal_evar_declaration ~hyps ~ev ~ty:goal_ty ~refined_ev in
          let q = in_elpi_solve ?goal_name ~hyps ~ev:refined_ev ~ty:goal_ty ~args in
          state, E.App(E.Constants.sigmac,E.Lam(E.App(E.Constants.andc,g,[q])),[])
      | Some text ->
(*
          let state, args = CList.fold_map (in_elpi_arg ~depth) state args in
          let args = U.list_to_lp_list args in
*)
          let state, hyps, ev, goal_ty =
            in_elpi_evar_concl evar_concl goal (ctx, ctx_len) ~scope:ctx_len hyps ~depth state in
          let g = in_elpi_evar_declaration ~hyps ~ev ~ty:goal_ty in
          let state, q = on_Compile_state (CC.lp ~depth) state text in 
          state, E.App(E.Constants.andc,g,[q])) in
  let state, evarmap_query = Evar.Set.fold (fun k (state, q) ->
     let state, e = in_elpi_evar_info ~depth state k in
     state, E.App(E.Constants.andc, e, [q]))
    (reachable_evarmap evd goal) (state, query) in
  match state with
  | Compile state -> state, evarmap_query
  | Run _ -> assert false

