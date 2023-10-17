open Elpi_plugin
open Classes

type qualified_name = Coq_elpi_utils.qualified_name

type loc_name_atts = (Loc.t * qualified_name * Attributes.vernac_flags)

let observer_evt ((loc, name, atts) : loc_name_atts) (x : Event.t) = 
  let open Coq_elpi_vernacular in
  let open Coq_elpi_arg_HOAS in 
  let run_program e = run_program loc name ~atts [e] in 
  let gref_2_string gref = Pp.string_of_ppcmds (Names.GlobRef.print gref) in
  let normalize_string s = 
    Printf.printf "Adding : %s\n" s;
    let s = String.split_on_char '.' s |> List.rev |> List.hd in
    let s = String.split_on_char ',' s |> List.hd in 
    Cmd.String s in
  let add_aux gref = run_program (normalize_string (gref_2_string gref)) in
  add_aux @@ match x with  
  | Event.NewClass x -> x.cl_impl
  | Event.NewInstance x -> x.instance

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

(* type hint_term =
  | IsGlobRef of Names.GlobRef.t
  | IsConstr of Constr.t * Univ.ContextSet.t option (* None if monomorphic *)

let hack : Hints.hint_term -> hint_term = fun x ->
  (
    assert (Coq_config.version = "8.18.0");
    Obj.magic x
  ) *)

    (* EConstr.kind x
    | Constr.Constant
    | Constr.Contructor
    | Constr.Inductive
    | Constr..... *)

(* let _ = 
  let sigma, env = 
    let env = Global.env () in Evd.(from_env env, env) in 
  Hints.pr_hint_db_by_name env sigma "typeclass_instances" |> ignore; 
  Printer.pr_constr_env env sigma |> ignore *)