(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Util
open Names
open Typeclasses

open Elpi

module Intpart = Unionfind.Make(Evar.Set)(Evar.Map)

open Elpi_plugin
open Coq_elpi_utils

type override =
  | AllButFor of Names.GlobRef.Set.t
  | Only of Names.GlobRef.Set.t

type action =
  | Set of Coq_elpi_utils.qualified_name * override
  | Add of GlobRef.t list
  | Rm of GlobRef.t list

let elpi_solver = Summary.ref ~name:"tc_takeover" None

let takeover action =
  let open Names.GlobRef in
  match !elpi_solver, action with
  | _, Set(solver,mode) ->
    elpi_solver := Some (mode,solver)
  | None, (Add _ | Rm _) ->
    CErrors.user_err Pp.(str "Set the override program first")
  | Some(AllButFor s,solver), Add grl ->
    let s' = List.fold_right Set.add grl Set.empty in 
    elpi_solver := Some (AllButFor (Set.diff s s'),solver)
  | Some(AllButFor s,solver), Rm grl ->
    let s' = List.fold_right Set.add grl Set.empty in 
    elpi_solver := Some (AllButFor (Set.union s s'),solver)
  | Some(Only s,solver), Add grl ->
    let s' = List.fold_right Set.add grl Set.empty in 
    elpi_solver := Some (Only (Set.union s s'),solver)
  | Some(Only s,solver), Rm grl ->
    let s' = List.fold_right Set.add grl Set.empty in 
    elpi_solver := Some (Only (Set.diff s s'),solver)
 
let inTakeover =
  let cache x = takeover x in
  Libobject.(declare_object (superglobal_object_nodischarge "TC_HACK_OVERRIDE" ~cache ~subst:None))
  
let takeover isNone l solver =
  let open Names.GlobRef in
  let l = List.map Coq_elpi_utils.locate_simple_qualid l in 
  let s = List.fold_right Set.add l Set.empty in 
  let mode = if isNone then Only Set.empty else if Set.is_empty s then AllButFor s else Only s in
  Lib.add_leaf (inTakeover (Set(solver,mode)))

let takeover_add l =
  let l = List.map Coq_elpi_utils.locate_simple_qualid l in 
  Lib.add_leaf (inTakeover (Add l))

let takeover_rm l =
  let l = List.map Coq_elpi_utils.locate_simple_qualid l in 
  Lib.add_leaf (inTakeover (Rm l))

let path2str = List.fold_left (fun acc e -> Printf.sprintf "%s/%s" acc e) ""
let debug_covered_gref = CDebug.create ~name:"tc_current_gref" ()

let covered1 env sigma classes i default=
  let ei = Evd.find_undefined sigma i in
  let ty = Evd.evar_concl ei in
  match Typeclasses.class_of_constr env sigma ty with
  | Some (_,(((cl: typeclass),_),_)) -> 
    let cl_impl = cl.Typeclasses.cl_impl in
    debug_covered_gref (fun () -> Pp.(str "The current gref is: " ++ 
        Printer.pr_global cl_impl ++ str ", with path: " ++ str (path2str (gr2path cl_impl))));
    Names.GlobRef.Set.mem cl_impl classes 
  | None -> default

let covered env sigma omode s =
  match omode with
  | AllButFor blacklist ->  
     Evar.Set.for_all (fun x -> not (covered1 env sigma blacklist x false)) s
  | Only whitelist ->
     Evar.Set.for_all (fun x -> covered1 env sigma whitelist x true) s

let debug_handle_takeover = CDebug.create ~name:"handle_takeover" ()

let elpi_fails program_name =
  let open Pp in
  let kind = "tactic/command" in
  let name = show_qualified_name program_name in
  CErrors.user_err (strbrk (String.concat " " [
    "The elpi"; kind; name ; "failed without giving a specific error message.";
    "Please report this inconvenience to the authors of the program."
  ]))
let solve_TC program env sigma depth unique ~best_effort filter =
  let loc = API.Ast.Loc.initial "(unknown)" in
  let atts = [] in
  let glss, _ = Evar.Set.partition (filter sigma) (Evd.get_typeclass_evars sigma) in
  let gls = Evar.Set.elements glss in
  (* TODO: activate following row to compute new gls
     this row to make goal sort in msolve *)
  (* let evar_deps = List.map (fun e -> 
    let evar_info = Evd.find_undefined sigma e in 
    let evar_deps = Evarutil.filtered_undefined_evars_of_evar_info sigma evar_info in 
    e, Evar.Set.elements evar_deps
  ) gls in *)
  (* let g = Graph.build_graph evar_deps in  *)
  (* let gls = List.map (fun (e: 'a Graph.node) -> e.name ) (Graph.topo_sort g) in  *)
  let query ~depth state =
    let state, (loc, q), gls =
      Coq_elpi_HOAS.goals2query sigma gls loc ~main:(Coq_elpi_HOAS.Solve [])
        ~in_elpi_tac_arg:Coq_elpi_arg_HOAS.in_elpi_tac ~depth state in
    let state, qatts = Coq_elpi_vernacular.atts2impl loc Summary.Stage.Interp ~depth state atts q in
    let state = API.State.set Coq_elpi_builtins.tactic_mode state true in
    state, (loc, qatts), gls
    in
  match Coq_elpi_vernacular.Interp.get_and_compile program with
  | None -> assert false
  | Some (cprogram,_) ->
      match Coq_elpi_vernacular.Interp.run ~static_check:false cprogram (`Fun query) with
      | API.Execute.Success solution ->
          let sigma, _, _ = Coq_elpi_HOAS.solution2evd ~eta_contract_solution:true sigma solution glss in
          Some(false,sigma)
      | API.Execute.NoMoreSteps -> CErrors.user_err Pp.(str "elpi run out of steps")
      | API.Execute.Failure -> elpi_fails program
      | exception (Coq_elpi_utils.LtacFail (level, msg)) -> Some(false, sigma)

let handle_takeover coq_solver env sigma (cl: Intpart.set) =
  let t = Unix.gettimeofday () in 
  let is_elpi, res = 
    match !elpi_solver with
    | Some(omode,solver) when covered env sigma omode cl -> 
      true, solve_TC solver
    | _ -> false, coq_solver in
  let is_elpi_text = if is_elpi then "Elpi" else "Coq" in
  debug_handle_takeover (fun () ->  
    let len = (Evar.Set.cardinal cl) in  Pp.str @@ 
    Printf.sprintf "handle_takeover for %s - Class : %d - Time : %f" 
    is_elpi_text len (Unix.gettimeofday () -. t));
  res, cl

let assert_same_generated_TC = Goptions.declare_bool_option_and_ref 
        ~depr:(Deprecation.make ()) ~key:["assert_same_generated_TC"] ~value:false 

(* let same_solution evd1 evd2 i =
  let print_discrepancy a b =
     CErrors.anomaly Pp.(str 
      "Discrepancy in same solution: \n" ++ 
      str"Expected : " ++ a ++ str"\n" ++
      str"Found    : " ++ b)  
  in 
  let get_types evd t = EConstr.to_constr ~abort_on_undefined_evars:false evd t in
  try (
    let t1 = Evd.find evd1 i  in 
    let t2 = Evd.find evd2 i |> Evd.evar_body in 
    match t1, t2 with 
    | Evd.Evar_defined t1, Evd.Evar_defined t2 ->
      let t1, t2 = get_types evd1 t1, get_types evd2 t2 in 
      let b = try Constr.eq_constr_nounivs t1 t2 with Not_found ->
        CErrors.anomaly Pp.(str "Discrepancy in same solution: problem with universes") in 
      if (not b)  then
        print_discrepancy (Printer.pr_constr_env (Global.env ()) evd1 t1) (Printer.pr_constr_env (Global.env ()) evd2 t2) 
      else
        b
    | Evd.Evar_empty, Evd.Evar_empty -> true
    | Evd.Evar_defined t1, Evar_empty -> 
        let t1 = get_types evd1 t1 in 
        print_discrepancy (Printer.pr_constr_env (Global.env ()) evd1 t1) (Pp.str "Nothing")
    | Evd.Evar_empty, Evd.Evar_defined t2 ->
        let t2 = get_types evd2 t2 in 
        print_discrepancy (Pp.str "Nothing") (Printer.pr_constr_env (Global.env ()) evd2 t2)
  ) with Not_found -> 
      CErrors.anomaly Pp.(str "Discrepancy in same solution: Not found All")  *)


(* let same_solution comp evd1 evd2 =
  Evar.Set.for_all (same_solution evd1 evd2) comp *)
