(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Util
open Typeclasses
open Elpi
open Elpi_plugin
open Coq_elpi_utils

module GRSet = Names.GlobRef.Set
module CSMap = CString.Map

let qname2str observer =  String.concat "." observer
let str2gr = Coq_elpi_utils.locate_simple_qualid

let elpi_fails program_name =
  let open Pp in
  let kind = "TC_Solve" in
  let name = show_qualified_name program_name in
  CErrors.user_err (strbrk (String.concat " " [
    "The elpi"; kind; name ; "failed without giving a specific error message.";
    "Please report this inconvenience to the authors of the program."
  ]))


module Modes = struct
  
  (** override_mode *)
  type omode =
    | AllButFor of GRSet.t
    | Only of GRSet.t

  type action =
    | Set of omode
    | Add of Libnames.qualid list
    | Rm of Libnames.qualid list

  let omodes = ref (CSMap.empty : omode CSMap.t)

  let create_solver_omode solver =
    omodes := CSMap.add solver (Only GRSet.empty) !omodes

  let takeover (qname, new_mode,c) =
    let name = qname2str qname in
    if c then create_solver_omode name else
    let add_str x = GRSet.add (str2gr x) in
    let grl2set grl = List.fold_right add_str grl GRSet.empty in
    let old_mode = CSMap.find name !omodes in
    let new_mode =
      match old_mode, new_mode with
      | _, Set(mode) -> mode
      | AllButFor s, Add grl -> AllButFor (GRSet.diff s (grl2set grl))
      | AllButFor s, Rm grl -> AllButFor (GRSet.union s (grl2set grl))
      | Only s, Add grl -> Only (GRSet.union s (grl2set grl))
      | Only s, Rm grl -> Only (GRSet.diff s (grl2set grl))
      in
    omodes := CSMap.set name new_mode !omodes

  let cache_solver_mode = Coq_elpi_lib_obj.add_obj_no_discharge "TC_Solver_omode" takeover
end

module Solver = struct
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

  type action = 
    | Create
    | Activate
    | Deactivate

  let covered1 env sigma classes i default =
    let ei = Evd.find_undefined sigma i in
    let ty = Evd.evar_concl ei in
    match Typeclasses.class_of_constr env sigma ty with
    | Some (_,(((cl: typeclass),_),_)) -> 
      let cl_impl = cl.Typeclasses.cl_impl in
      GRSet.mem cl_impl classes 
    | None -> default

  let covered omode env sigma s =
    match omode () with
    | Modes.AllButFor blacklist -> 
      Evar.Set.for_all (fun x -> not (covered1 env sigma blacklist x false)) s
    | Only whitelist ->
      Evar.Set.for_all (fun x -> covered1 env sigma whitelist x true) s


  let action_manager (qname, x) =
    let name = qname2str qname in
    match x with
    | Create -> Class_tactics.register_solver ~name (solve_TC qname, covered (fun () -> CSMap.get name !Modes.omodes));
    | Activate -> Class_tactics.activate_solver ~name
    | Deactivate -> Class_tactics.deactivate_solver ~name
    
  let cache_solver = Coq_elpi_lib_obj.add_obj_no_discharge "TC_Solver" action_manager
end
 

let set_solver_mode kind qname (l: Libnames.qualid list) = 
  let cache_solver_mode = Modes.cache_solver_mode in
  let empty = GRSet.empty in
  match kind with
  | "Add" -> Lib.add_leaf (cache_solver_mode (qname, Add l, false))
  | "Rm"  -> Lib.add_leaf (cache_solver_mode (qname, Rm l, false))
  | "All" -> Lib.add_leaf (cache_solver_mode (qname, Set (AllButFor empty), false))
  | "None"-> Lib.add_leaf (cache_solver_mode (qname, Set (Only empty), false))
  | "Set" -> let set = ref empty in
      List.iter (fun x -> set := GRSet.add (str2gr x) !set) l;
      Lib.add_leaf (cache_solver_mode (qname, Set (Only !set), false))
  | _ -> failwith "Invalid entry"


let solver_register l =
  Lib.add_leaf (Solver.cache_solver (l, Create));
  Lib.add_leaf (Modes.cache_solver_mode (l, Add [], true))

let solver_activate l = Lib.add_leaf (Solver.cache_solver (l, Activate))

let solver_deactivate l = Lib.add_leaf (Solver.cache_solver (l, Deactivate))
