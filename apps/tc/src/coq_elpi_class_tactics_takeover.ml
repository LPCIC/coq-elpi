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

let takeover_add l =
  let l = List.map Coq_elpi_utils.locate_simple_qualid l in 
  Lib.add_leaf (inTakeover (Add l))

let takeover_rm l =
  let l = List.map Coq_elpi_utils.locate_simple_qualid l in 
  Lib.add_leaf (inTakeover (Rm l))

let elpi_fails program_name =
  let open Pp in
  let kind = "tactic/command" in
  let name = show_qualified_name program_name in
  CErrors.user_err (strbrk (String.concat " " [
    "The elpi"; kind; name ; "failed without giving a specific error message.";
    "Please report this inconvenience to the authors of the program."
  ]))

let path2str = List.fold_left (fun acc e -> Printf.sprintf "%s/%s" acc e) ""

let covered1 env sigma classes i default=
  let ei = Evd.find_undefined sigma i in
  let ty = Evd.evar_concl ei in
  match Typeclasses.class_of_constr env sigma ty with
  | Some (_,(((cl: typeclass),_),_)) -> 
    let cl_impl = cl.Typeclasses.cl_impl in
    Names.GlobRef.Set.mem cl_impl classes 
  | None -> default

let covered env sigma omode s =
  match omode with
  | AllButFor blacklist ->  
     Evar.Set.for_all (fun x -> not (covered1 env sigma blacklist x false)) s
  | Only whitelist ->
     Evar.Set.for_all (fun x -> covered1 env sigma whitelist x true) s

let solve_TC program env sigma depth unique ~best_effort filter =
  let loc = API.Ast.Loc.initial "(unknown)" in
  let atts = [] in
  let glss, _ = Evar.Set.partition (filter sigma) (Evd.get_typeclass_evars sigma) in
  let gls = Evar.Set.elements glss in
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
          let sigma, _, _ = Coq_elpi_HOAS.solution2evd sigma solution glss in
          Some(false,sigma)
      | API.Execute.NoMoreSteps -> CErrors.user_err Pp.(str "elpi run out of steps")
      | API.Execute.Failure -> elpi_fails program
      | exception (Coq_elpi_utils.LtacFail (level, msg)) -> elpi_fails program

type actions = 
  | Create of bool * Libnames.qualid list
  | Activate
  | Deactivate

let action_manager (qname, x) =
  let build_observer_name (observer : qualified_name) =  String.concat "." observer in
  let name = build_observer_name qname in
  match x with
  | Create (isNone, l) ->
      Class_tactics.register_solver ~name (solve_TC qname, fun _ _ _ -> print_endline "CIAO"; true);
      Class_tactics.activate_solver ~name
  | Activate -> Class_tactics.activate_solver ~name
  | Deactivate -> Class_tactics.deactivate_solver ~name

let inTakeover = 
  Coq_elpi_lib_obj.add_obj_no_discharge "TC_Solver" action_manager
 
let takeover (isNone: bool) (l: Libnames.qualid list) (_,x,_) = 
  Lib.add_leaf (inTakeover (x, Create (isNone, l)))

let activate_solver l = 
  Lib.add_leaf (inTakeover (l, Activate))

let deactivate_solver l = 
  Lib.add_leaf (inTakeover (l, Deactivate))