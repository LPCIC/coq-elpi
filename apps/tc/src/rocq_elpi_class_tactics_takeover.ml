(* rocq-elpi: Coq terms as the object language of elpi                       *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

type aaction = ARm | AAdd | ASet | ANone | AAll


module Rocq_elpi_lib_obj = struct
let add_obj_no_discharge name cache =
  Libobject.(declare_object 
    (global_object_nodischarge name ~cache ~subst:None))

let add_superobj_no_discharge name cache =
  Libobject.(declare_object 
    (superglobal_object_nodischarge name ~cache ~subst:None))
end

open Util
open Typeclasses
open Elpi
open Elpi_plugin
open Rocq_elpi_utils

module GRSet = Names.GlobRef.Set
module CSMap = CString.Map

let qname2str observer =  String.concat "." observer
let str2gr = Rocq_elpi_utils.locate_simple_qualid

let elpi_fails program_name =
  let open Pp in
  let kind = "TC_Solve" in
  let name = show_qualified_name program_name in
  CErrors.user_err (strbrk (String.concat " " [
    "The elpi"; kind; name ; "failed without giving a specific error message.";
    "Please report this inconvenience to the authors of the program."
  ]))

module type M = sig
  type elt
  type t
  val empty : t
  val diff : t -> t -> t
  val union : t -> t -> t
  val add : elt -> t -> t
  val gr2elt : Names.GlobRef.t -> elt
  val mem : elt -> t -> bool
  val of_qualid_list : Libnames.qualid list -> t

end

(* Set of overridden class *)
module OSet : M = struct
  module M = GRSet

  type t = M.t
  type elt = M.elt
  let empty = M.empty
  let diff = M.diff
  let union = M.union
  let add = M.add
  let mem = M.mem
  let gr2elt (x: Names.GlobRef.t) : elt = x

  let of_qualid_list (x: Libnames.qualid list) : t = 
    let add s x = add (Rocq_elpi_utils.locate_simple_qualid x) s in
    List.fold_left add empty x
end

module Modes = struct
  
  (** override_mode *)
  type omode =
    | AllButFor of OSet.t
    | Only of OSet.t

  type action =
    | Set of omode
    | Add of OSet.t
    | Rm of OSet.t

  let omodes = ref (CSMap.empty : omode CSMap.t)

  let create_solver_omode solver =
    omodes := CSMap.add solver (Only OSet.empty) !omodes

  let takeover (qname, new_mode,c) =
    let name = qname2str qname in
    if c then create_solver_omode name else
    let old_mode = CSMap.find name !omodes in
    let new_mode =
      match old_mode, new_mode with
      | _, Set(mode) -> mode
      | AllButFor s, Add grl -> AllButFor (OSet.diff s grl)
      | AllButFor s, Rm grl -> AllButFor (OSet.union s grl)
      | Only s, Add grl -> Only (OSet.union s grl)
      | Only s, Rm grl -> Only (OSet.diff s grl)
      in
    omodes := CSMap.set name new_mode !omodes

  let cache_solver_mode = Rocq_elpi_lib_obj.add_superobj_no_discharge "TC_Solver_omode" takeover
end

module Solver = struct
  let solve_TC program = let open Class_tactics in { solver = fun env sigma ~depth ~unique ~best_effort ~goals ->
    let atts = [] in
    let gls = goals in
    let query ~base state =
      let loc = Elpi.API.State.get Rocq_elpi_builtins_synterp.invocation_site_loc state in
      let depth = 0 in
      let state, q, gls =
        Rocq_elpi_HOAS.solvegoals2query sigma gls loc ~main:[]
          ~in_elpi_tac_arg:Rocq_elpi_arg_HOAS.(in_elpi_tac ~loc:(to_coq_loc loc)) ~depth ~base state in
      let state, qatts = Rocq_elpi_vernacular.atts2impl loc Summary.Stage.Interp ~depth state atts q in
      let state = API.State.set Rocq_elpi_builtins.tactic_mode state true in
      state, qatts, gls
      in
    let loc = Loc.initial Loc.ToplevelInput in
    match Rocq_elpi_vernacular.Interp.get_and_compile ~loc program with
    | None -> assert false
    | Some (base,_) ->
      match Rocq_elpi_vernacular.Interp.run ~loc base (Fun (query ~base)) with
        | API.Execute.Success solution ->
            let sigma, sub_goals, to_shelve = Rocq_elpi_HOAS.solution2evd ~eta_contract_solution:true sigma solution (Evar.Set.of_list goals) in
            let sigma = Evd.shelve sigma sub_goals in
            sub_goals = [], sigma
        | API.Execute.NoMoreSteps -> CErrors.user_err Pp.(str "elpi run out of steps")
        | API.Execute.Failure -> elpi_fails program
        | exception (Rocq_elpi_utils.LtacFail (level, msg)) -> raise Not_found
  }

  type action = 
    | Create
    | Activate
    | Deactivate

  let covered1 env sigma classes i default =
    let ei = Evd.find_undefined sigma i in
    let ty = Evd.evar_concl ei in
    match Typeclasses.class_of_constr env sigma ty with
    | Some (_,((cl,_),_)) -> OSet.mem (OSet.gr2elt cl.cl_impl) classes 
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
    
  let cache_solver = Rocq_elpi_lib_obj.add_superobj_no_discharge "TC_Solver" action_manager
end
 

let set_solver_mode kind qname (l: Libnames.qualid list) = 
  let l = OSet.of_qualid_list l in
  let cache_solver_mode = Modes.cache_solver_mode in
  match kind with
  | AAdd -> Lib.add_leaf (cache_solver_mode (qname, Add l, false))
  | ARm  -> Lib.add_leaf (cache_solver_mode (qname, Rm l, false))
  | AAll -> Lib.add_leaf (cache_solver_mode (qname, Set (AllButFor OSet.empty), false))
  | ANone-> Lib.add_leaf (cache_solver_mode (qname, Set (Only OSet.empty), false))
  | ASet -> Lib.add_leaf (cache_solver_mode (qname, Set (Only l), false))

let solver_register l =
  Lib.add_leaf (Solver.cache_solver (l, Create));
  Lib.add_leaf (Modes.cache_solver_mode (l, Add OSet.empty, true))

let solver_activate l = Lib.add_leaf (Solver.cache_solver (l, Activate))

let solver_deactivate l = Lib.add_leaf (Solver.cache_solver (l, Deactivate))
