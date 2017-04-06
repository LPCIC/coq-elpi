module G = Globnames
module E = Elpi_runtime
module C = Constr

open Names
open Glob_term

open Coq_elpi_utils
open Coq_elpi_HOAS

(* ***************** $custom Coq predicates  ***************************** *)

let type_err api args expected =
 err Pp.(str api ++ str"got" ++ prlist str (List.map E.show_term args) ++
                    str"expects" ++ str expected)

let () =
  let open Elpi_util in

  (* Print (debugging) *)  
  Elpi_runtime.register_custom "$say" (fun ~depth ~env _ args ->
      let b = Buffer.create 80 in
      let fmt = Format.formatter_of_buffer b in
      Format.fprintf fmt "@[<hov 1>%a@]@\n%!"
        Elpi_runtime.Pp.(pplist (uppterm depth [] 0 env) " ") args;
    Feedback.msg_info (Pp.str (Buffer.contents b));
    []);

  (* Nametab access *)  
  Elpi_runtime.register_custom "$locate" (fun ~depth ~env _ args ->
    match List.map (kind ~depth) args with
    | [E.CData c;ret] when E.cstring.Elpi_util.CData.isc c ->
        let qualid =
          Libnames.qualid_of_string (Elpi_ast.Func.show (E.cstring.Elpi_util.CData.cout c)) in
        let gr =
          try 
             match Nametab.locate_extended qualid with
             | G.TrueGlobal gr -> gr
             | G.SynDef sd -> 
                match Syntax_def.search_syntactic_definition sd with
                | _, Notation_term.NRef gr -> gr
                | _ -> assert false (* too complex *)
          with Not_found -> CErrors.user_err ~hdr:"elpi" Pp.(str "Not found: " ++ Libnames.pr_qualid qualid) in
        [E.App (E.Constants.eqc, in_elpi_gr gr, [ret])]
    | _ -> assert false);

  (* Kernel's environment access *)  
  E.register_custom "$coq-env-const" (fun ~depth ~env _ args ->
    match List.map (kind ~depth) args with
    | [E.CData gr; ret_bo; ret_ty] when isgr gr ->
        let gr = grout gr in
        begin match gr with
        | G.ConstRef c ->
             let ty, _u = Global.type_of_global_in_context (Global.env()) gr in
             let bo = Option.get (Global.body_of_constant c) in
             [E.App (E.Constants.eqc, constr2lp ty, [ret_ty]);
              E.App (E.Constants.eqc, constr2lp bo, [ret_bo]); ]
        | _ -> err Pp.(str"$coq-env-cons on a non-constant") end
    | _ -> type_err "$coq-env-const" args "reference");

  (* Kernel's type checker *)  
  E.register_custom "$coq-typecheck" (fun ~depth ~env _ args ->
    match List.map (kind ~depth) args with
    | [t;ret] ->
        let t = lp2constr t in
        Printf.eprintf "T: %s\n" (Pp.string_of_ppcmds (Printer.pr_lconstr t));
        let j = Safe_typing.typing (Global.safe_env ()) t in
        let ty = constr2lp (Safe_typing.j_type j) in
        [E.App (E.Constants.eqc, ty, [ret])]
    | _ -> assert false);
  
  (* Type inference *)  
  E.register_custom "$coq-elaborate" (fun ~depth ~env _ args ->
    match List.map (kind ~depth) args with
    | [t;ret_t;ret_ty] ->
        let t = lp2constr t in
        let env = Global.env () in
        let gt = Detyping.detype false [] env Evd.empty t in
        let gt =
          let rec map = function
            | GEvar _ -> mkGHole
            | x -> Glob_ops.map_glob_constr map x in
          map gt in
        let evd = ref (Evd.from_env env) in
        let j = Pretyping.understand_judgment_tcc env evd gt in
        let t = constr2lp (Environ.j_val j) in
        let ty = constr2lp (Environ.j_type j) in
        [E.App (E.Constants.eqc, t, [ret_t]);
         E.App (E.Constants.eqc, ty, [ret_ty])]
    | _ -> assert false)
  
;;


