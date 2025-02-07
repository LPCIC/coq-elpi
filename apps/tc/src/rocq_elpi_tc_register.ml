(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_plugin
open Classes
open Rocq_elpi_arg_HOAS
open Names

type qualified_name = Rocq_elpi_utils.qualified_name

type loc_name_atts = (Loc.t * qualified_name * Attributes.vernac_flags)
  
(* Hack to convert a Coq GlobRef into an elpi string *)
let gref2elpi_term (gref: GlobRef.t) : Cmd.raw = 
  let gref_2_string gref = Pp.string_of_ppcmds (Printer.pr_global gref) in
  Cmd.String (gref_2_string gref)
  (* TODO: maybe returning an elpi term is cleaner, but this creates a loop in 
    stdppInj test *)
  (* Cmd.Term (CAst.make @@ Constrexpr.CRef(
    Libnames.qualid_of_string @@ gref_2_string gref,None)) *)

(* Returns the elpi term representing the type class received in argument *)
let observer_class (x : Typeclasses.typeclass) : Rocq_elpi_arg_HOAS.Cmd.raw list = 
  [Cmd.String "new_class"; gref2elpi_term x.cl_impl]

let observer_default_instance (x : Typeclasses.typeclass) : Rocq_elpi_arg_HOAS.Cmd.raw list = 
  [Cmd.String "default_instance";gref2elpi_term x.cl_impl]

let observer_coercion add (x : Typeclasses.typeclass) : Rocq_elpi_arg_HOAS.Cmd.raw list = 
  let name2str x = Cmd.String (Names.Name.print x |> Pp.string_of_ppcmds) in
  let proj = x.cl_projs |> List.map (fun (x: Typeclasses.class_method) -> x.meth_name) in
  let mode = if add then "add_coercions" else "remove_coercions" in
  Cmd.String mode :: List.map name2str proj

(** 
  Returns the list of Cmd.raw arguments to be passed to the elpi program in charge 
  to compile instances. The arguments are [Inst, TC, Locality, Prio] where: 
  - Inst     : is the elpi Term for the current instance
  - TC       : is the elpi Term for the type class implemented by Inst
  - Locality : is the elpi String [Local|Global|Export] for the locality of Inst 
  - Prio     : is the elpi Int N representing the priority of the instance. N is:  
                | -1 if the instance has no user-defined priority 
                |  N if the instance has the user-defined priority N
*)
let observer_instance ({locality; instance; info; class_name} : instance) : Rocq_elpi_arg_HOAS.Cmd.raw list = 
  let locality2elpi_string loc = 
    let hint2string = function 
    | Hints.Local -> "Local"
    | Export -> "Export"
    | SuperGlobal -> "Global" in
    Cmd.String (hint2string loc) in 
  let prio2elpi_int (prio: Typeclasses.hint_info) = 
    Cmd.Int (Option.default (-1) prio.hint_priority) in 
  [ Cmd.String "new_instance"; 
    gref2elpi_term instance; 
    gref2elpi_term class_name;
    locality2elpi_string locality;
    prio2elpi_int info
  ]

let class_runner f cl =
  let actions = [
    observer_coercion false; 
    observer_class; 
    observer_coercion true; 
    (* observer_default_instance *)
  ] in
  List.iter (fun obs -> f (obs cl)) actions

let inObservation =
  Libobject.declare_object @@
    Libobject.local_object "TC_HACK_OBSERVER_CLASSES"
      ~cache:(fun (run,cl) -> class_runner run cl)
      ~discharge:(fun x -> Some x)

let inObservation1 =
  Libobject.declare_object @@
    Libobject.local_object "TC_HACK_OBSERVER_INSTANCE"
      ~cache:(fun (run,inst) -> run @@ observer_instance inst)
      ~discharge:(fun (_,inst as x) -> if inst.locality = Local then None else Some x)

let observer_evt ((loc, name, atts) : loc_name_atts) (x : Event.t) = 
  let open Rocq_elpi_vernacular in
  let run_program e = Interp.run_program ~loc name ~syndata:None ~atts e in 
  match x with  
  | Event.NewClass cl -> Lib.add_leaf (inObservation (run_program,cl)) 
  | Event.NewInstance inst -> Lib.add_leaf (inObservation1 (run_program,inst))

module StringMap = Map.Make(String)

type observers = observer StringMap.t

let observers : observers ref = Summary.ref StringMap.empty ~name:"tc_observers"

let build_observer_name (observer : qualified_name) = 
  String.concat "." observer

type action = 
  | Create of string * loc_name_atts 
  | Activate of qualified_name 
  | Deactivate of qualified_name

let action_manager x = 
    match x with
  | Create (name, loc_name_atts) -> 
      let t1 = Sys.time () in
      begin
        try
          let observer = Classes.register_observer ~name (observer_evt loc_name_atts) in 
          observers := StringMap.add name observer !observers;
          Classes.activate_observer observer
        with e when CErrors.is_anomaly e ->
          Feedback.msg_warning Pp.(str (Printf.sprintf "%s already registered" name))
        end;
        let t2 = Sys.time () in
      if Rocq_elpi_tc_time.get_time_tc_bench () then Feedback.msg_debug Pp.(str @@ Printf.sprintf "[TC] register.ml time is %.5f" (t1 -. t2))
  | Activate observer -> 
      Classes.activate_observer (StringMap.find (build_observer_name observer) !observers)
  | Deactivate observer -> 
      Classes.deactivate_observer (StringMap.find (build_observer_name observer) !observers)


(* Take an action and execute it with the action manager *)
let inTakeover =
  let cache = action_manager
  in Libobject.(declare_object 
    (superglobal_object_nodischarge "TC_HACK_OBSERVER" ~cache ~subst:None))

(* Adds a new observer in coq and activate it *)
let register_observer ((_, name, _) as lna : loc_name_atts) = 
  let obs_name = build_observer_name name in
  Lib.add_leaf (inTakeover (Create (obs_name, lna)))

let activate_observer (observer : qualified_name) = 
  Lib.add_leaf (inTakeover (Activate observer))

let deactivate_observer (observer : qualified_name) = 
  Lib.add_leaf (inTakeover (Deactivate observer))
