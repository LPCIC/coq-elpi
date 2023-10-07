let _ = Mltop.add_known_module "coq-elpi-tc.plugin"

(* # 3 "src/coq_elpi_tc_hook.mlg" *)
 

open Elpi
open Elpi_plugin
open Coq_elpi_arg_syntax
open Coq_elpi_vernacular


let elpi_typeclass_hook program env sigma ~flags v ~inferred ~expected =
  let loc = API.Ast.Loc.initial "(unknown)" in
  let atts = [] in
  let sigma, goal = Evarutil.new_evar env sigma expected in
  let goal_evar, _ = EConstr.destEvar sigma goal in
  let query ~depth state =
    let state, (loc, q), gls =
      Coq_elpi_HOAS.goals2query sigma [goal_evar] loc ~main:(Coq_elpi_HOAS.Solve [v; inferred])
        ~in_elpi_tac_arg:Coq_elpi_arg_HOAS.in_elpi_tac_econstr ~depth state in
    let state, qatts = atts2impl loc ~depth state atts q in
    let state = API.State.set Coq_elpi_builtins.tactic_mode state true in
    state, (loc, qatts), gls
  in
  let cprogram, _ = get_and_compile program in
  match run ~static_check:false cprogram (`Fun query) with
  | API.Execute.Success solution ->
     let gls = Evar.Set.singleton goal_evar in
     let sigma, _, _ = Coq_elpi_HOAS.solution2evd sigma solution gls in
     if Evd.is_defined sigma goal_evar then Some (sigma, goal) else None
  | API.Execute.NoMoreSteps
  | API.Execute.Failure -> None
  | exception (Coq_elpi_utils.LtacFail (level, msg)) -> None

let add_typeclass_hook =
  let typeclass_hook_program = Summary.ref ~name:"elpi-typeclass" None in
  let typeclass_hook env sigma ~flags v ~inferred ~expected =
    match !typeclass_hook_program with
    | None -> None
    | Some h -> elpi_typeclass_hook h env sigma ~flags v ~inferred ~expected in
  let name = "elpi-typeclass" in
  Coercion.register_hook ~name typeclass_hook;
  let inCoercion =
    let cache program =
      typeclass_hook_program := Some program;
      Coercion.activate_hook ~name in
    let open Libobject in
    declare_object
    @@ superglobal_object_nodischarge "ELPI-COERCION" ~cache ~subst:None in
  fun program -> Lib.add_leaf (inCoercion program)



let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-elpi-tc.plugin") ~command:"ElpiCoercion" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Elpi", 
                                     Vernacextend.TyTerminal ("TypeclassFallbackTactic", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_qualified_name), 
                                     Vernacextend.TyNil))), (let coqpp_body p
                                                            atts = Vernacextend.vtdefault (fun () -> 
                                                                   
# 54 "src/coq_elpi_tc_hook.mlg"
                                                                                      
     let () = ignore_unknown_attributes atts in
     add_typeclass_hook (snd p) 
                                                                   ) in fun p
                                                            ?loc ~atts ()
                                                            -> coqpp_body p
                                                            (Attributes.parse any_attribute atts)), None))]

