let _ = Mltop.add_known_module "coq-elpi-cs.plugin"

# 3 "src/coq_elpi_cs_hook.mlg"
 

open Elpi
open Elpi_plugin
open Coq_elpi_arg_syntax
open Coq_elpi_vernacular
module Evarconv = Evarconv
module Evarconv_hacked = Evarconv_hacked


let elpi_cs_hook program env sigma lhs rhs =
  let (lhead, largs) = EConstr.decompose_app sigma lhs in
  let (rhead, rargs) = EConstr.decompose_app sigma rhs in
  if (EConstr.isConst sigma lhead && Structures.Structure.is_projection (fst (EConstr.destConst sigma lhead))) || 
	 (EConstr.isConst sigma rhead && Structures.Structure.is_projection (fst (EConstr.destConst sigma rhead)))
  then begin
	  let loc = API.Ast.Loc.initial "(unknown)" in
	  let atts = [] in
	  (*let sigma, ty = Typing.type_of env sigma lhs in*)
	  let sigma, (ty, _) = Evarutil.new_type_evar env sigma Evd.univ_flexible in
	  let { Coqlib.eq } = Coqlib.build_coq_eq_data () in
	  let sigma, eq = EConstr.fresh_global env sigma eq in
	  let t = EConstr.mkApp (eq,[|ty;lhs;rhs|]) in
	  let sigma, goal = Evarutil.new_evar env sigma t in
	  let goal_evar, _ = EConstr.destEvar sigma goal in
	  let query ~depth state =
		 let state, (loc, q), gls =
			Coq_elpi_HOAS.goals2query sigma [goal_evar] loc ~main:(Coq_elpi_HOAS.Solve [])
			  ~in_elpi_tac_arg:Coq_elpi_arg_HOAS.in_elpi_tac_econstr ~depth state in
		 let state, qatts = atts2impl loc Summary.Stage.Interp ~depth state atts q in
		 let state = API.State.set Coq_elpi_builtins.tactic_mode state true in
		 state, (loc, qatts), gls
	  in
	  match Interp.get_and_compile program with
	  | None -> None
	  | Some (cprogram, _) ->
		 match Interp.run ~static_check:false cprogram (`Fun query) with
		 | API.Execute.Success solution ->
			let gls = Evar.Set.singleton goal_evar in
			let sigma, _, _ = Coq_elpi_HOAS.solution2evd sigma solution gls in
			let ty_evar, _ = EConstr.destEvar sigma ty in
			  Some (Evd.remove (Evd.remove sigma ty_evar) goal_evar)
		 | API.Execute.NoMoreSteps
		 | API.Execute.Failure -> None
    | exception (Coq_elpi_utils.LtacFail (level, msg)) -> None
  end
  else None

let add_cs_hook =
  let cs_hook_program = Summary.ref ~name:"elpi-cs" None in
  let cs_hook env sigma proj pat =
	Feedback.msg_info (Pp.str "run");
    match !cs_hook_program with
    | None -> None
    | Some h -> elpi_cs_hook h env sigma proj pat in
  let name = "elpi-cs" in
  Evarconv_hacked.register_hook ~name cs_hook;
  let inCs =
    let cache program =
      cs_hook_program := Some program;
	Feedback.msg_info (Pp.str "activate");

      Evarconv_hacked.activate_hook ~name in
    let open Libobject in
    declare_object
    @@ superglobal_object_nodischarge "ELPI-CS" ~cache ~subst:None in
  fun program -> Lib.add_leaf (inCs program)



let () = Vernacextend.static_vernac_extend ~plugin:(Some "coq-elpi-cs.plugin") ~command:"ElpiCS" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Elpi", 
                                     Vernacextend.TyTerminal ("CSFallbackTactic", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_qualified_name), 
                                     Vernacextend.TyNil))), (let coqpp_body p
                                                            atts = Vernactypes.vtdefault (fun () -> 
                                                                   
# 74 "src/coq_elpi_cs_hook.mlg"
                                                                                
     let () = ignore_unknown_attributes atts in
     add_cs_hook (snd p) 
                                                                   ) in fun p
                                                            ?loc ~atts ()
                                                            -> coqpp_body p
                                                            (Attributes.parse any_attribute atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Elpi", 
                                    Vernacextend.TyTerminal ("Override", 
                                    Vernacextend.TyTerminal ("CS", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_qualified_name), 
                                                                   Vernacextend.TyNil)))), 
         (let coqpp_body p atts = Vernactypes.vtdefault (fun () -> 
# 77 "src/coq_elpi_cs_hook.mlg"
                                                                             
     Evarconv.set_evar_conv Evarconv_hacked.evar_conv_x 
                                  ) in fun p
         ?loc ~atts () -> coqpp_body p (Attributes.parse any_attribute atts)), None))]

