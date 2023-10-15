open Elpi_plugin

type qualified_name = Coq_elpi_utils.qualified_name

type solver = (Loc.t * qualified_name * Attributes.vernac_flags)
let solvers : solver list ref = ref []

let observer (x : Classes.Event.t) ((loc, name, atts) : solver) = 
  let open Coq_elpi_vernacular in
  let open Coq_elpi_arg_HOAS in 
  let run_program e = run_program loc name ~atts [e] in 
  let gref_2_string gref = Pp.string_of_ppcmds (Names.GlobRef.print gref) in
  let normalize_string s = 
    let s = List.hd (String.split_on_char ',' s) in 
    let s = if String.starts_with ~prefix:"(" s then 
        String.sub s 1 (String.length s - 1) else s in 
    Cmd.String s in
  let add_aux gref = run_program (normalize_string (gref_2_string gref)) in
  add_aux @@ match x with  
  | Classes.Event.NewClass x -> x.cl_impl
  | Classes.Event.NewInstance x -> x.instance

let observer (x : Classes.Event.t) =
  List.iter (observer x) !solvers

let register_observer (loc, name, atts : solver) = 
  solvers := (loc, name, atts) :: !solvers;
  let observer = Classes.register_observer ~name:(String.concat "." name) observer in
  Classes.activate_observer observer