open Elpi_plugin
open Classes
open Coq_elpi_arg_HOAS

type qualified_name = Coq_elpi_utils.qualified_name

type loc_name_atts = (Loc.t * qualified_name * Attributes.vernac_flags)
  
let gref2elpi_term (gref: Names.GlobRef.t) : Cmd.raw = 
  let gref_2_string gref = Pp.string_of_ppcmds (Names.GlobRef.print gref) in
  let normalize_string s = 
    String.split_on_char '.' s |> List.rev |> List.hd |>
    String.split_on_char ',' |> List.hd  in
  Cmd.Term (CAst.make @@ Constrexpr.CRef(
    Libnames.qualid_of_string @@ normalize_string @@ gref_2_string gref,None))

let observer_class (x : Typeclasses.typeclass) : Coq_elpi_arg_HOAS.Cmd.raw list = 
  [gref2elpi_term x.cl_impl]

let observer_instance ({locality; instance; info; class_name} : instance) : Coq_elpi_arg_HOAS.Cmd.raw list = 
  let locality2elpi_string loc = 
    let hint2string = function 
    | Hints.Local -> "Local"
    | Export | SuperGlobal -> "Global" in
    Cmd.String (hint2string loc) in 
  let prio2elpi_int (prio: Typeclasses.hint_info) = 
    Cmd.Int (Option.default 0 prio.hint_priority) in 
  [
    gref2elpi_term instance; 
    gref2elpi_term class_name;
    locality2elpi_string locality;
    prio2elpi_int info
  ]


let observer_evt ((loc, name, atts) : loc_name_atts) (x : Event.t) = 
  let open Coq_elpi_vernacular in
  let run_program e = run_program loc name ~atts e in 
  run_program @@ match x with  
  | Event.NewClass cl -> observer_class cl
  | Event.NewInstance inst -> observer_instance inst

let inTakeover =
  let cache (loc, name, atts) = 
    let observer1 = Classes.register_observer 
                    ~name:(String.concat "." name) 
                    (observer_evt (loc, name, atts))
    in
    Classes.activate_observer observer1
  in
  Libobject.(declare_object 
    (superglobal_object_nodischarge "TC_HACK_OBSERVER" ~cache ~subst:None))

let register_observer (x : loc_name_atts) = 
  Lib.add_leaf (inTakeover x)