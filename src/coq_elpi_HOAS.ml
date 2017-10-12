(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module API = Elpi_API
module G = Globnames
module E = API.Extend.Data
module CD = struct
  include API.Extend.CData
  include API.Extend.Data.C
end
module R = API.Execute
module U = API.Extend.Utils
module P = API.Extend.Pp
module CC = API.Extend.Compile
module CS = API.Extend.CustomConstraint
module C = Constr
open Names
open Coq_elpi_utils
open API.Data

(* ************************************************************************ *)
(* ****************** HOAS of Coq terms and goals ************************* *)
(* See also coq-term.elpi (terms)                                           *)
(* ************************************************************************ *)

(* {{{ CData ************************************************************** *)

(* names *)
let namein, isname, nameout =
  let open CD in
  let { cin; isc; cout } = declare {
    data_name = "Name.t";
    data_pp = (fun fmt x ->
      Format.fprintf fmt "\"%s\"" (Pp.string_of_ppcmds (Nameops.pr_name x)));
    data_eq = (fun _ _ -> true);
    data_hash = (fun _ -> 0);
  } in
  cin, isc, cout
;;
let in_elpi_name x = E.CData (namein x)

let is_coq_name = function
  | E.CData n -> isname n
  | _ -> false

let in_coq_name = function
  | E.CData n when isname n -> nameout n
  | (E.UVar (r,_,_) | E.AppUVar(r,_,_))
    when r.E.contents == E.Constants.dummy ->
      Name.Anonymous
  | E.Discard -> Name.Anonymous
  | x -> err Pp.(str"Not a name: " ++ str (P.Raw.show_term x))

(* universes *)
let univin, isuniv, univout =
  let open CD in
  let { cin; isc; cout } = declare {
    data_name = "Univ.Universe.t";
    data_pp = (fun fmt x ->
      Format.fprintf fmt "%s" (Pp.string_of_ppcmds (Univ.Universe.pr x)));
    data_eq = Univ.Universe.equal;
    data_hash = Univ.Universe.hash;
  } in
  cin, isc, cout
;;
let prop   = E.Constants.from_string "prop"
let typc   = E.Constants.from_stringc "typ"
let sortc  = E.Constants.from_stringc "sort"
let in_elpi_sort s =
  E.App(sortc,
    (match s with
    | Sorts.Prop Sorts.Null -> prop
    | Sorts.Prop Sorts.Pos -> E.App(typc,E.CData (univin Univ.type0_univ),[])
    | Sorts.Type u -> E.App(typc,E.CData (univin u),[])), [])
let in_elpi_flex_sort t = E.App(sortc, E.App(typc, t, []), [])

(* constants *)
let grin, isgr, grout =
  let open CD in
  let { cin; isc; cout } = declare {
    data_name = "Globnames.global_reference";
    data_pp = (fun fmt x ->
     Format.fprintf fmt "\"%s\"" (Pp.string_of_ppcmds (Printer.pr_global x)));
    data_eq = G.eq_gr;
    data_hash = G.RefOrdered.hash;
  } in
  cin, isc, cout
;;
let indtc  = E.Constants.from_stringc "indt"
let indcc  = E.Constants.from_stringc "indc"
let constc = E.Constants.from_stringc "const"
let in_elpi_gr r =
  let open Globnames in
  match r with
  | (VarRef _ | ConstRef _) -> E.App(constc,E.CData (grin r),[])
  | IndRef _ -> E.App(indtc,E.CData (grin r),[])
  | ConstructRef _ -> E.App(indcc,E.CData (grin r),[])


let mpin, ismp, mpout =
  let open CD in
  let { cin; isc; cout } = declare {
    data_name = "ModPath.t";
    data_pp = (fun fmt x ->
            Format.fprintf fmt "\"%s\"" (Names.ModPath.to_string x));
    data_eq = Names.ModPath.equal;
    data_hash = Names.ModPath.hash;
  } in
  cin, isc, cout
;;
let mptyin, istymp, mptyout =
  let open CD in
  let { cin; isc; cout } = declare {
    data_name = "ModTypePath.t";
    data_pp = (fun fmt x ->
            Format.fprintf fmt "\"%s\"" (Names.ModPath.to_string x));
    data_eq = Names.ModPath.equal;
    data_hash = Names.ModPath.hash;
  } in
  cin, isc, cout
;;

let in_elpi_modpath ~ty mp = E.CData (if ty then mptyin mp else mpin mp)
let is_modpath = function E.CData x -> ismp x | _ -> false
let is_modtypath = function E.CData x -> istymp x | _ -> false
let in_coq_modpath = function
  | E.CData x when ismp x -> mpout x
  | E.CData x when istymp x -> mptyout x
  | _ -> assert false

(* ********************************* }}} ********************************** *)

(* {{{ constants (app, lam, ...) ****************************************** *)
(* binders *)
let lamc   = E.Constants.from_stringc "lam"
let in_elpi_lam n s t = E.App(lamc,in_elpi_name n,[s;E.Lam t])

let prodc  = E.Constants.from_stringc "prod"
let in_elpi_prod n s t = E.App(prodc,in_elpi_name n,[s;E.Lam t])

let letc   = E.Constants.from_stringc "let"
let in_elpi_let n b s t = E.App(letc,in_elpi_name n,[s;b;E.Lam t])

(* other *)
let appc   = E.Constants.from_stringc "app"
let in_elpi_app_Arg hd args =
    match hd, args with
    | E.Const c, [] -> assert false
    | E.Const c, x :: xs -> E.App(c,x,xs)
    | E.App(c,x,xs), _ -> E.App(c,x,xs@args)
    | _ -> assert false
    
let in_elpi_appl hd (args : E.term list) =
  if args = [] then hd
  else E.App(appc,U.list_to_lp_list (hd :: args),[])
let in_elpi_app hd (args : E.term array) =
  in_elpi_appl hd (Array.to_list args)

let matchc = E.Constants.from_stringc "match"
let in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs =
  E.App(matchc,t, [rt; U.list_to_lp_list bs])

let fixc   = E.Constants.from_stringc "fix"
let in_elpi_fix name rno ty bo =
  E.App(fixc,in_elpi_name name,[CD.of_int rno; ty; E.Lam bo])

(* implicit *)
let hole   = E.Constants.from_string "hole"
let in_elpi_implicit = hole

(* bool *)
let tt = E.Constants.from_string "tt"
let ff = E.Constants.from_string "ff"
let in_elpi_tt = tt
let in_elpi_ff = ff

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : Evd.evar_map -> elpi *************************************** *)

let command_mode_cc =
  CC.State.declare ~name:"coq-elpi:command-mode-compiler"
    ~init:(fun () -> true)
    ~pp:(fun fmt b -> Format.fprintf fmt "%b" b)
let command_mode =
  CS.declare ~name:"coq-elpi:command-mode"
    ~init:(CS.CompilerState (command_mode_cc, fun x -> x))
    ~pp:(fun fmt b -> Format.fprintf fmt "%b" b)

let command_mode = CS.get command_mode 

type state = Compile of CC.State.t | Run of CS.t

module CoqEngine_HOAS : sig 

  type coq_engine  = {
   env : Environ.env; (* global env *)
   evd : Evd.evar_map; (* universe constraints *)
   ev2arg : ev2arg option;
   solution2ev : Evar.t CString.Map.t;
  }
  and ev2arg
   
  val engine_cc : coq_engine CC.State.component
  val engine : coq_engine CS.component

  val evd_of_engine : coq_engine -> Evd.evar_map
  val names_ctx_of_engine : coq_engine -> Id.t list

  val in_elpi_evar : state -> Evar.t -> state * E.term

end = struct

 type coq_engine = {
   env : Environ.env;
   evd : Evd.evar_map;
   ev2arg : ev2arg option;
   solution2ev : Evar.t CString.Map.t;
 }
 and ev2arg = E.term Evar.Map.t
 (* The term is an Arg, so after compilation it loses any sense *)

 let pp fmt t = Format.fprintf fmt "evmap" (* FIXME *)

 let evd_of_engine { evd } = evd
 let names_ctx_of_engine { env } =
    let named_ctx = Environ.named_context env in
    Context.Named.fold_inside
      (fun acc x -> Context.Named.Declaration.get_id x :: acc)
      ~init:[] named_ctx

 let init () =
   let env = Global.env () in
   {
     env;
     evd = Evd.from_env env;
     ev2arg = Some Evar.Map.empty;
     solution2ev = CString.Map.empty;
   }
 
 let engine_cc : coq_engine CC.State.component =
   CC.State.declare ~name:"coq-elpi:evmap-compiler-state" ~init ~pp

 let engine : coq_engine CS.component =
   CS.declare ~name:"coq-elpi:evmap-constraint-type" ~pp
     ~init:(CS.CompilerState(engine_cc,fun t -> { t with ev2arg = None }))

 let evar_name_hint evd k =
   Option.default "G" (Option.map Names.Id.to_string (Evd.evar_ident k evd))

 let in_elpi_evar orig k =
   match orig with
   | Compile state ->
       let { ev2arg; evd } as e = CC.State.get engine_cc state in
       begin try  orig, Evar.Map.find k (Option.get ev2arg)
       with Not_found ->
         let name_hint = evar_name_hint evd k in
         let state, name, t = CC.fresh_Arg state ~name_hint ~args:[] in
         let { ev2arg; solution2ev } as c = CC.State.get engine_cc state in
         let solution2ev = CString.Map.add name k solution2ev in
         let ev2arg = Option.map (Evar.Map.add k t) ev2arg in
         let c = { c with ev2arg; solution2ev } in
         Compile (CC.State.set engine_cc state c), t
       end
   | Run state ->
       (* TODO: generate goals as "declare-evar Ctx Ev Ty" and
        * add them to the runtime *)
         err Pp.(str"Evar creation at tactic time not supported")
end

open CoqEngine_HOAS

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : Constr.t -> elpi ******************************************* *)

let rec pos name cur = function
  | [] -> None
  | Name n :: _ when Names.Id.equal n name -> Some cur
  | _ :: xs -> pos name (cur+1) xs

let mkApp t l =
  match t, l with
  | E.Const c, [] -> t
  | E.Const c, x::xs -> E.App(c,x,xs)
  | _ -> assert false

let get_evd = function
  | Compile s -> evd_of_engine (CC.State.get engine_cc s)
  | Run s -> evd_of_engine (CS.get engine s)

let get_names_ctx = function
  | Compile s -> names_ctx_of_engine (CC.State.get engine_cc s)
  | Run s -> names_ctx_of_engine (CS.get engine s)

let check_univ_inst univ_inst =
  if not (Univ.Instance.is_empty univ_inst) then
    nYI "HOAS universe polymorphism"

let constr2lp named_ctx ~depth state t =
  let nctx_len = List.length named_ctx in
  let rec aux ctx state t = match C.kind t with
    | C.Rel n -> state, E.Constants.of_dbl (nctx_len + ctx - n)
    | C.Var n ->
         state, begin match pos n 0 named_ctx with
         | Some i -> E.Constants.of_dbl i
         | None -> in_elpi_gr (G.VarRef n)
         end
    | C.Meta _ -> nYI "HOAS for Meta"
    | C.Evar (k,args) ->
         let state, t = in_elpi_evar state k in
         let section_len = List.length (get_names_ctx state) in
         let args = Array.sub args 0 (Array.length args - section_len) in
         let state, args = CArray.fold_map (aux ctx) state args in
         state, mkApp t (CArray.rev_to_list args)
    | C.Sort s -> state, in_elpi_sort s
    | C.Cast (t,_,ty) ->
         let state, t = aux ctx state t in
         let state, ty = aux ctx state ty in
         let state, self = aux (ctx+1) state (Constr.mkRel 1) in
         state, in_elpi_let Names.Name.Anonymous t ty self
    | C.Prod(n,s,t) ->
         let state, s = aux ctx state s in
         let state, t = aux (ctx+1) state t in
         state, in_elpi_prod n s t
    | C.Lambda(n,s,t) ->
         let state, s = aux ctx state s in
         let state, t = aux (ctx+1) state t in
         state, in_elpi_lam n s t
    | C.LetIn(n,b,s,t) ->
         let state, b = aux ctx state b in
         let state, s = aux ctx state s in
         let state, t = aux (ctx+1) state t in
         state, in_elpi_let n b s t
    | C.App(hd,args) ->
         let state, hd = aux ctx state hd in
         let state, args = CArray.fold_map (aux ctx) state args in
         state, in_elpi_app hd args
    | C.Const(c,i) ->
         check_univ_inst i;
         state, in_elpi_gr (G.ConstRef c)
    | C.Ind(ind,i) ->
         check_univ_inst i;
         state, in_elpi_gr (G.IndRef ind)
    | C.Construct(construct,i) ->
         check_univ_inst i;
         state, in_elpi_gr (G.ConstructRef construct)
    | C.Case((*{ C.ci_ind; C.ci_npar; C.ci_cstr_ndecls; C.ci_cstr_nargs }*)_,
             rt,t,bs) ->
         let state, t = aux ctx state t in
         let state, rt = aux ctx state rt in
         let state, bs = CArray.fold_map (aux ctx) state bs in
         state,
         in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt 
           (Array.to_list bs)
    | C.Fix(([| rarg |],_),([| name |],[| typ |], [| bo |])) ->
         let state, typ = aux ctx state typ in
         let state, bo = aux (ctx+1) state bo in
         state, in_elpi_fix name rarg typ bo
    | C.Fix _ -> nYI "HOAS for mutual fix"
    | C.CoFix _ -> nYI "HOAS for cofix"
    | C.Proj _ -> nYI "HOAS for primitive projections"
  in
    aux depth state t
;;

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : Goal.t -> elpi ********************************************** *)

let declc = E.Constants.from_stringc "decl"
let defc = E.Constants.from_stringc "def"
let declare_evc = E.Constants.from_stringc "declare-evar"
let declare_goal_evc = E.Constants.from_stringc "declare-goal-evar"
let evarc = E.Constants.from_stringc "evar"
let true_t = E.Constants.from_string "true"
let solvec = E.Constants.from_stringc "solve"
let goalc = E.Constants.from_stringc "goal"
let goal_namec = E.Constants.from_stringc "goal-name"

let mk_pi_arrow hyp rest =
  E.App(E.Constants.pic, E.Lam (E.App(E.Constants.implc,hyp,[rest])), [])

let mk_decl c name ty = E.App(declc, c, [in_elpi_name name; ty])
let mk_def c name bo norm ty = E.App(defc,c,[in_elpi_name name; bo; norm; ty])

let mkArg name_hint lvl = function
  | Compile state ->
      let args = CList.init lvl E.Constants.of_dbl in
      let state, name, t = CC.fresh_Arg ~name_hint ~args state in
      Compile state, name,t 
  | Run _ -> err Pp.(str"mkArg called at runtime")

let in_elpi_ctx ~depth state ctx k =
  let open Context.Named.Declaration in
  let rec aux depth (ctx, ctx_len) hyps state = function
    | [] -> k (ctx, ctx_len) (List.rev hyps) ~depth state
    | LocalAssum (name, ty) :: rest ->
        let name = Name name in
        let state, ty = constr2lp (ctx @ [Anonymous]) ~depth state ty in
        let c = E.Constants.of_dbl (depth + ctx_len) in
        let hyp = mk_decl c name ty in
        let state, rest =
          aux depth (ctx @ [name],ctx_len+1) ((hyp, depth+ctx_len+1) :: hyps) state rest in
        state, mk_pi_arrow hyp rest
    | LocalDef (name,bo,ty) :: rest ->
        let name = Name name in (* TODO: optimize append *)
        let state, ty = constr2lp (ctx @ [Anonymous]) ~depth state ty in
        let state, bo = constr2lp (ctx @ [Anonymous]) ~depth state bo in
        let state, _, norm = mkArg "norm" ctx_len state in
        let c = E.Constants.of_dbl (depth + ctx_len) in
        let hyp = mk_def c name bo norm ty in
        let state, rest =
          aux depth (ctx @ [name],ctx_len+1) ((hyp, depth+ctx_len+1) :: hyps) state rest in
        state, mk_pi_arrow hyp rest
  in
    aux depth ([],0) [] state (List.rev ctx)

let in_elpi_evar_concl t k (ctx, ctx_len) evar_scope hyps ~depth state =
  let state, t = constr2lp ctx ~depth state t in
  let args = CList.init evar_scope E.Constants.of_dbl in
  let state, c = in_elpi_evar state k in
  let hyps =
    List.map (fun (t,from) -> U.move ~from ~to_:(depth+ctx_len) t) hyps in
  state, U.list_to_lp_list hyps, (mkApp c args), t

let in_elpi_evar_declaration hyps ev t = E.App(declare_evc, hyps, [ev; t])
let in_elpi_goal_evar_declaration hyps ev t ev1 =
  E.App(declare_goal_evc, hyps, [ev; t; ev1])

let mk_goal hyps ev ty attrs =
  E.App(goalc,hyps,[ev;ty; U.list_to_lp_list attrs])

let in_elpi_solve name hyps ev t =
  let name = match name with None -> Anonymous | Some x -> Name x in
  let name = E.App(goal_namec, in_elpi_name name,[]) in
  E.App(solvec,E.Cons(mk_goal hyps ev t [name],E.Nil),[])

let info_of_evar state k =
  let open Context.Named in
  let evd = get_evd state in
  let { Evd.evar_concl } as info =
    Evarutil.nf_evar_info evd (Evd.find evd k) in
  let ctx = Environ.named_context_of_val (Evd.evar_filtered_hyps info) in
  let section = get_names_ctx state in
  let ctx = ctx |> List.filter (fun x ->
    not(CList.mem_f Id.equal (Declaration.get_id x) section)) in
  evar_concl, ctx

let in_elpi_evar_info ~depth state k =
  let evar_concl, ctx = info_of_evar state k in
  in_elpi_ctx ~depth state ctx (fun (ctx, ctx_len) hyps ~depth state ->
    let state, hyps, ev, t =
      in_elpi_evar_concl evar_concl k (ctx,ctx_len) ctx_len hyps ~depth state in
    state, in_elpi_evar_declaration hyps ev t)

let reachable_evarmap evd goal =
  let rec aux s =
    let s'=
      Evar.Set.fold (fun k s -> Evar.Set.union s 
        (Evarutil.undefined_evars_of_evar_info evd (Evd.find evd k))) s s in
    if Evar.Set.equal s s' then s else aux s' in
  Evar.Set.remove goal (aux (Evar.Set.singleton goal))

let on_Compile_state f = function
  | Compile s -> fun x -> let s, x = f s x in Compile s, x
  | _ -> assert false

let goal2query evd goal ?main ~depth state =
  let state = CC.State.set command_mode_cc state false in (* tactics *)
  let state = CC.State.update engine_cc state (fun x -> { x with evd }) in
  let state = Compile state in
  if not (Evd.is_undefined evd goal) then
    err Pp.(str (Printf.sprintf "Evar %d is not a goal" (Evar.repr goal)));
  let evar_concl, ctx = info_of_evar state goal in
  let goal_name = Evd.evar_ident goal evd in
  let state, query =
    in_elpi_ctx ~depth state ctx (fun (ctx, ctx_len) hyps ~depth state ->
      match main with
      | None ->
          let state, hyps, ev, goal_ty =
            in_elpi_evar_concl evar_concl goal
              (ctx @ [Anonymous], ctx_len+1) ctx_len hyps ~depth state in
          let ev1 = E.Constants.of_dbl (depth+ctx_len) in
          let g = in_elpi_goal_evar_declaration hyps ev goal_ty ev1 in
          let q = in_elpi_solve goal_name hyps ev1 goal_ty in
          state, E.App(E.Constants.sigmac,E.Lam(E.App(E.Constants.andc,g,[q])),[])
      | Some text ->
          let state, hyps, ev, goal_ty =
            in_elpi_evar_concl evar_concl goal (ctx, ctx_len) ctx_len hyps ~depth state in
          let g = in_elpi_evar_declaration hyps ev goal_ty in
          let state, q = on_Compile_state (CC.lp ~depth) state text in 
          state, E.App(E.Constants.andc,g,[q])) in
  let state, evarmap_query = Evar.Set.fold (fun k (state, q) ->
     let state, e = in_elpi_evar_info ~depth state k in
     state, E.App(E.Constants.andc, e, [q]))
    (reachable_evarmap evd goal) (state, query) in
  match state with
  | Compile state -> state, evarmap_query
  | Run _ -> assert false

let mkName x = Name x

let constr2lp ?(proof_ctx=[]) ~depth state t =
  let state = Run state in
  match constr2lp proof_ctx ~depth state t with
  | Run state, t -> state, t
  | Compile _, _ -> assert false

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : elpi -> Constr.t * Evd.evar_map ***************************** *)

let in_coq_hole () =
  C.mkConst (Constant.make2
    (ModPath.MPfile (DirPath.make [Id.of_string "elpi";Id.of_string "elpi"]))
    (Label.make "hole"))

let new_univ state =
  CS.update_return engine state (fun ({ evd } as x) ->
    let evd, v = Evd.new_univ_level_variable UState.UnivRigid evd in
    { x with evd }, Univ.Universe.make v)

let add_constraints state c = CS.update engine state (fun ({ evd } as x) ->
  { x with evd = Evd.add_universe_constraints evd c })

let type_of_global state r = CS.update_return engine state (fun x ->
  let ty, ctx = Global.type_of_global_in_context x.env r in
  let evd =
    Evd.merge_context_set Evd.univ_rigid x.evd
      (Univ.ContextSet.of_context ctx) in
  { x with evd }, ty)

let new_evar info state =
  CS.update_return engine state (fun ({ evd } as x) ->
     let evd, k = Evd.new_evar evd info in
     { x with evd }, k)

let normalize_univs state = CS.update engine state (fun ({ evd } as x) ->
  let ctx = Evd.evar_universe_context evd in
  let ctx = Evd.normalize_evar_universe_context ctx in
  { x with evd = Evd.set_universe_context evd ctx })

let restrict_univs state u = CS.update engine state (fun ({ evd } as x) ->
  let evd = Evd.restrict_universe_context evd u in
  { x with evd })

let is_sort ~depth x =
  match kind depth x with
  | E.App(s,_,[]) -> sortc == s
  | _ -> false

let is_prod ~depth x =
  match kind depth x with
  | E.App(s,_,[_;_]) -> prodc == s
  | _ -> false

let is_globalc x = x == constc || x == indtc || x == indcc

let find_evar var syntactic_constraints depth x =
  let is_evar depth t =
    match kind depth t with
    | E.App(c,x,[t]) when c == evarc -> Some(x,t)
    | _ -> None in
  try
    CList.find_map (fun { E.goal = (depth,concl); context } ->
      match is_evar depth concl with
      | Some((E.UVar(r,_,_)|E.AppUVar(r,_,_)),ty) when r == var ->
          Some (context, (depth,ty))
      | _ -> None) syntactic_constraints
  with Not_found ->
    err Pp.(str"The term contains " ++
      str(pp2string P.(term depth [] 0 [||]) x) ++
      str" that has no declared type in the constraint store:" ++ spc() ++
      str(pp2string P.(list (fun fmt { E.goal = (depth,t) } ->
             term depth [] 0 [||] fmt t) ",")
          syntactic_constraints))

let nth_name l n =
  match List.nth l n with
  | Name id -> id
  | Anonymous -> assert false

type lp2c_state = {
  ref2evk : (E.term_attributed_ref * Evar.t) list;
  state : CS.t;      
}

let on_state f ({ state } as orig) =
  let state, t = f state in
  { orig with state }, t

let get_id = function Name.Anonymous -> Id.of_string "_" | Name x -> x

let rec of_elpi_ctx syntactic_constraints (names,n_names) ctx state =

  let mk_fresh =
    let i = ref 0 in
    fun n ->
      incr i;
      Name.mk_name
        (Id.of_string_soft (Printf.sprintf "_elpi_renamed_%s_%d_" n !i)) in
  let in_coq_fresh_name name names =
    match in_coq_name name with
    | Name.Anonymous as x -> x
    | Name.Name id as x when List.mem x names -> mk_fresh (Id.to_string id)
    | x -> x in

(* TODO: try with spurious ctx items, lifting is probably wrong XXX *)
  let aux names state t = lp2constr syntactic_constraints state names 0 t in
  let of_elpi_ctx_entry n_names names ~depth t state =
(*           Printf.eprintf "ctx: %s\n" (API.Extend.Pp.Raw.show_term t); *)
    match kind depth t with
    | E.App(c,v,[name;ty]) when c == declc && is_coq_name name ->
        let name = in_coq_fresh_name name names in
        let id = get_id name in
        let state, ty = aux (names @ [Name.Anonymous]) state ty in
        Some(state, name, Context.Named.Declaration.LocalAssum(id,ty))
    | E.App(c,v,[name;bo;_;ty]) when c == defc && is_coq_name name ->
        let name = in_coq_fresh_name name names in
        let id = get_id name in
        let state, ty = aux (names @ [Name.Anonymous]) state ty in
        let state, bo = aux (names @ [Name.Anonymous]) state bo in
        Some(state, name, Context.Named.Declaration.LocalDef(id,bo,ty))
    | _ -> None
  in
    CList.fold_right (fun (depth,t) (n_names,names,nctx,state as orig) ->
      match of_elpi_ctx_entry n_names names ~depth t state with
      | None -> orig
      | Some (state, name, ctx_entry) ->
          n_names+1,names @ [ name ], ctx_entry :: nctx, state)
    ctx (n_names,names,[],state)

(* names |- depth\ t *)
and lp2constr syntactic_constraints state names depth t =

  let rec aux (names,depth as ctx) state t = match kind depth t with

    | E.App(s,p,[]) when sortc == s && p == prop -> state, C.mkProp
    | E.App(s,E.App(t,c,[]),[]) when sortc == s && typc == t ->
        begin match kind depth c with
        | E.CData x when isuniv x -> state, C.mkType (univout x)
        | E.UVar _ | E.AppUVar _ ->
           let state, t = on_state new_univ state in
           state, C.mkType t
        | _ -> assert false
        end

    (* constants *)
    | E.App(c,E.CData gr,[]) when indtc == c && isgr gr ->
       let gr = grout gr in
       if not (G.isIndRef gr) then
         err Pp.(str"not an inductive type: " ++ Printer.pr_global gr);
       state, C.mkInd (G.destIndRef gr)
    | E.App(c,E.CData gr,[]) when indcc == c && isgr gr ->
       let gr = grout gr in
       if not (G.isConstructRef gr) then
         err Pp.(str"not a constructor: " ++ Printer.pr_global gr);
       state, C.mkConstruct (G.destConstructRef gr)
    | E.App(c,E.CData gr,[]) when constc == c && isgr gr ->
       begin match grout gr with
       | G.VarRef v -> state, C.mkVar v
       | G.ConstRef v -> state, C.mkConst v
       | x -> err Pp.(str"not a constant: " ++ Printer.pr_global x)
       end

    (* binders *)
    | E.App(c,name,[s;t]) when lamc == c || prodc == c ->
        let name = in_coq_name name in
        let state, s = aux ctx state s in
        let state, t = aux_lam ctx state t in
        if lamc == c then state, C.mkLambda (name,s,t)
        else state, C.mkProd (name,s,t)
    | E.App(c,name,[s;b;t]) when letc == c ->
        let name = in_coq_name name in
        let state,s = aux ctx state s in
        let state,b = aux ctx state b in
        let state,t = aux_lam ctx state t in
        state, C.mkLetIn (name,b,s,t)
        
    | E.Const n as c ->
       if c == hole then 
         state, in_coq_hole ()
       else if n >= 0 then
         let n_names = List.length names in
         if n < n_names then state, C.mkVar(nth_name names n)
         else if n < depth then state, C.mkRel(depth - n)
         else 
           err Pp.(str"wrong bound variable (BUG):" ++ str (E.Constants.show n))
       else
          err Pp.(str"wrong constant:" ++ str (E.Constants.show n))

    (* app *)
    | E.App(c,x,[]) when appc == c ->
         (match U.lp_list_to_list depth x with
         | x :: xs -> 
            let state,x = aux ctx state x in
            let state,xs = CList.fold_map (aux ctx) state xs in
            state, C.mkApp (x,Array.of_list xs)
         | _ -> assert false) (* TODO *)
    
    (* match *)
    | E.App(c,t,[rt;bs]) when matchc == c ->
        let state, t = aux ctx state t in
        let state, rt = aux ctx state rt in
        let state, bt =
          CList.fold_map (aux ctx) state (U.lp_list_to_list depth bs) in
        let ind =
          (* XXX fixme reduction *)
          let rec aux t o = match C.kind t with
            | C.Lambda(_,s,t) -> aux t (Some s)
            | _ -> match o with
              | None -> assert false (* wrong shape of rt XXX *)
              | Some t ->
                 match safe_destApp t with
                 | C.Ind i, _ -> fst i
                 | _ -> assert false (* wrong shape of rt XXX *)
          in
            aux rt None in
        let ci =
          Inductiveops.make_case_info (Global.env()) ind C.RegularStyle in
        state, C.mkCase (ci,rt,t,Array.of_list bt)

    (* fix *)
    | E.App(c,name,[rno;ty;bo]) when fixc == c ->
        let name = in_coq_name name in
        let state, ty = aux ctx state ty in
        let state, bo = aux_lam ctx state bo in
        let rno =
          match kind depth rno with
          | E.CData n when CD.is_int n -> CD.to_int n
          | _ -> err Pp.(str"Not an int: " ++ str (P.Raw.show_term rno)) in
        state, C.mkFix (([|rno|],0),([|name|],[|ty|],[|bo|]))
    
    (* evar *)
    | (E.UVar (r,_,_) | E.AppUVar (r,_,_)) as x ->
        let args =
          match x with
          | E.UVar (_,vardepth,ano) ->
               CList.init (vardepth+ano) E.Constants.of_dbl
          | E.AppUVar (_,vardepth,args) ->
               CList.init vardepth E.Constants.of_dbl @ args
          | _ -> assert false in
        begin try
          let ext_key = List.assq r state.ref2evk in
          let state, args = CList.fold_map (aux ctx) state args in
          let section_args =
            List.map Constr.mkVar (get_names_ctx (Run state.state)) in
          let ev = Term.mkEvar (ext_key,Array.of_list (List.rev args @ List.rev section_args)) in
          state, ev
        with Not_found ->
          let context, ty = find_evar r syntactic_constraints depth x in
          let state, k = declare_evar context ty state in
          let state = { state with ref2evk = (r,k) :: state.ref2evk } in
          let x =
            (* eta contraction in elpi *)
            let missing = List.length context - List.length args in
            if missing <= 0 then x else 
          match x with
          | E.UVar (r,vardepth,ano) -> E.UVar (r,vardepth,ano+missing)
          | E.AppUVar (r,vardepth,xs) ->
               E.AppUVar (r,vardepth,xs @ CList.init missing (fun i ->
                        E.Constants.of_dbl (i+List.length args)))
          | _ -> assert false  
            in
          aux ctx state x
        end

    (* errors *)
    | E.Lam _ as x ->
         err Pp.(str "out of place lambda: "++
                 str (pp2string P.(term depth [] 0 [||]) x))

    | x -> err Pp.(str"Not a HOAS term:" ++ str (P.Raw.show_term x))

  and aux_lam (ns,depth) s t = match kind depth t with
    | E.Lam t -> aux (ns,depth+1) s t
    | E.UVar(r,d,ano) -> aux (ns,depth+1) s (E.UVar(r,d,ano+1))
    | E.AppUVar(r,d,args) ->
         aux (ns,depth+1) s (E.AppUVar(r,d,args@[E.Constants.of_dbl depth]))
    | _ -> err Pp.(str"not a lambda")


  (* evar info read back *)

  and declare_evar ctx (depth,concl) state =
    let n_names, names, named_ctx, state =
      of_elpi_ctx syntactic_constraints ([],0) ctx state in
    let state, ty = aux (names,n_names) state concl in
    let named_ctx =
      named_ctx @ Environ.named_context (CS.get engine state.state).env in
    let info = Evd.make_evar (Environ.val_of_named_context named_ctx) ty in
    let state, k = on_state (new_evar info) state in
    state, k

  in
    aux (names,List.length names+depth) state t

(* ********************************* }}} ********************************** *)

(* {{{ E.solution -> Evd.evar_map ***************************************** *)

let eat_n_lambdas t upto =
  let open E in
  let rec aux n t =
    if n = upto then t
    else match t with
      | Lam t -> aux (n+1) t
      | UVar(r,d,a) -> aux (n+1) (UVar(r,d,a+1))
      | AppUVar(r,d,a) -> aux (n+1) (AppUVar(r,d,a@[Constants.of_dbl n]))
      | _ -> assert false
  in
    aux 0 t

let in_coq_solution {
   arg_names; assignments; custom_constraints; constraints
 } =
   let { solution2ev } = CS.get engine custom_constraints in
   let syntactic_constraints = E.constraints constraints in
     CString.Map.fold (fun name k state ->
       let t = assignments.(StrMap.find name arg_names) in
       let _, ctx = info_of_evar (Run state.state) k in 
       let names, n_names = 
         Context.Named.fold_inside
           (fun (acc,n) x ->
              Name (Context.Named.Declaration.get_id x) :: acc, n+1)
           ~init:([],0) ctx in
       let t = eat_n_lambdas (E.of_term t) n_names in
       let state, t =
         lp2constr syntactic_constraints state names 0 t in
       { state with state = CS.update engine state.state (fun ({ evd } as x) ->
               { x with evd = Evd.define k t evd })})
     solution2ev { ref2evk = []; state = custom_constraints }

let tclSOLUTION2EVD solution =
   let { state; ref2evk } = in_coq_solution solution in
   let open Proofview.Unsafe in
   let open Tacticals.New in
   tclTHEN
     (tclEVARS (CS.get engine state).evd)
     (tclSETGOALS (List.map snd ref2evk))


(* ********************************* }}} ********************************** *)

(* {{{ Recordops -> elpi ************************************************** *)

open Recordops

(* Record foo A1..Am := K { f1; .. fn }.   -- m params, n fields 
 * Canonical c (x1 : b1)..(xk : bk) := K p1..pm t1..tn.
 *
 *   fi v1..vm ? rest1  ==  (ci w1..wr) rest2
 *   
 *   ?i : bi
 *   vi =?= pi[xi/?i]
 *   wi =?= ui[xi/?i]
 *   ?  == c ?1 .. ?k
 *   rest1 == rest2
 *   ?j =<= (ci w1..wr)    -- default proj, ti = xj
 *   ci == gr
 *
 *   unif (const fi) [V1,..VM, C | R1] (const ci) [W1,..WR| R2] M U :-
 *     of (app[c, ?1,..?k]) _ CR, -- saturate
 *     hd-beta CR [] (indc _) [P1,..PM,T1,..TN],
 *     unify-list-U Vi Pi,
 *     Ti = app[const ci|U1,..,UN],
 *     unify-list-U Wi Ui,
 *     unify-eq C CR,
 *     unify-list-eq R1 R2.
 *
 *)

let canonical_solution2lp ~depth state
  ((proj_gr,patt), {
  o_DEF = solution;       (* c *)
  o_CTX = uctx_set;
  o_INJ = def_val_pos;    (* Some (j \in [0-n]) if ti = xj *)
  o_TABS = types;         (* b1 .. bk *)
  o_TPARAMS = params;     (* p1 .. pm *)
  o_NPARAMS = nparams;    (* m *)
  o_TCOMPS = cval_args }) (* u1..ur *)
=
  let proj = in_elpi_gr proj_gr in
  let state, solution = constr2lp ~depth state solution in
  let value =
    match patt with
    | Const_cs val_head_gr -> in_elpi_gr val_head_gr
    | Prod_cs -> in_elpi_prod Anonymous in_elpi_implicit in_elpi_implicit
    | Sort_cs Sorts.InProp -> in_elpi_sort Sorts.prop
    | Sort_cs _ -> in_elpi_sort Sorts.set
    | Default_cs -> in_elpi_implicit in
  state, E.App(E.Constants.from_stringc "canonical",proj,[value;solution])
;;
(* ********************************* }}} ********************************** *)

(* {{{ Typeclasses -> elpi ************************************************ *)

open Typeclasses

(* Record foo A1..Am := K { f1; .. fn }.   -- m params, n fields 
 * Canonical c (x1 : b1)..(xk : bk) := K p1..pm t1..tn.
 *
 *   fi v1..vm ? rest1  ==  (ci w1..wr) rest2
 *   
 *   ?i : bi
 *   vi =?= pi[xi/?i]
 *   wi =?= ui[xi/?i]
 *   ?  == c ?1 .. ?k
 *   rest1 == rest2
 *   ?j =<= (ci w1..wr)    -- default proj, ti = xj
 *   ci == gr
 *
 *   unif (const fi) [V1,..VM, C | R1] (const ci) [W1,..WR| R2] M U :-
 *     of (app[c, ?1,..?k]) _ CR, -- saturate
 *     hd-beta CR [] (indc _) [P1,..PM,T1,..TN],
 *     unify-list-U Vi Pi,
 *     Ti = app[const ci|U1,..,UN],
 *     unify-list-U Wi Ui,
 *     unify-eq C CR,
 *     unify-list-eq R1 R2.
 *
 *)

let instance2lp ~depth state instance =
  let solution = Typeclasses.instance_impl instance in
  let priority = Typeclasses.hint_priority instance in
  let priority = Option.default 0 priority in
  state, E.App(E.Constants.from_stringc "instance",
    in_elpi_gr solution,[E.C.of_int priority])
;;
(* ********************************* }}} ********************************** *)


let get_env state = (CC.State.get engine_cc state).env

let push_env state name =
  let open Context.Rel.Declaration in
  CC.State.update engine_cc state (fun ({ env } as x) ->
     { x with env = Environ.push_rel (LocalAssum(name,C.mkProp)) env })

let get_env_evd state =
  let { env; evd } = CS.get engine state in
  Environ.push_context_set (Evd.universe_context_set evd) env, evd

let get_current_env_evd hyps solution =
(*   let state = in_coq_solution solution in *)
  let _, names, named_ctx, lp2c_state = of_elpi_ctx (E.constraints solution.constraints) ([],0) hyps { ref2evk = []; state = solution.custom_constraints } in
  let { env; evd } as state = CS.get engine lp2c_state.state in
  let env = Environ.push_named_context named_ctx env in
(*
  let state = CS.set engine lp2c_state.state { state with env } in
  let env, evd = get_env_evd state in
*)
  lp2c_state.state, env, evd, names

let get_senv_evd state =
  let { evd } = CS.get engine state in
  let senv = Global.safe_env () in (* Fixme: put Stm.state into state? *)
  Safe_typing.push_context_set true (Evd.universe_context_set evd) senv, evd

let set_evd state evd = CS.update engine state (fun x -> { x with evd })

let grab_global_env state =
  CS.update engine state (fun x -> { x with env = Global.env () })

let lp2constr syntactic_constraints state ?(proof_ctx=[]) ~depth t =  
  let { state }, t =
    lp2constr syntactic_constraints { ref2evk = []; state } proof_ctx depth t in
  state, t

(* {{{ elpi -> Entries.mutual_inductive_entry **************************** *)

(* documentation of the Coq API
 
  Coq < Inductive foo (A : Type) (a : A) : A -> Prop := K : foo A a a.

  {Entries.mind_entry_record = None; mind_entry_finite = Decl_kinds.Finite;
   mind_entry_params =
    [(a, Entries.LocalAssumEntry _UNBOUND_REL_1);
     (A, Entries.LocalAssumEntry Type@{Top.1})];
   mind_entry_inds =
    [{Entries.mind_entry_typename = foo;
      mind_entry_arity = _UNBOUND_REL_2 -> Prop; mind_entry_template = false;
      mind_entry_consnames = [K];
      mind_entry_lc =
       [_UNBOUND_REL_3 _UNBOUND_REL_2 _UNBOUND_REL_1 _UNBOUND_REL_1]}];
   mind_entry_universes = Entries.Monomorphic_ind_entry Top.1 |= ;
   mind_entry_private = None}

  Coq < Inductive bar (n m : nat) : Prop := K (_ : bar n (S m)).

  {Entries.mind_entry_record = None; mind_entry_finite = Decl_kinds.Finite;
   mind_entry_params =
    [(m, Entries.LocalAssumEntry nat); (n, Entries.LocalAssumEntry nat)];
   mind_entry_inds =
    [{Entries.mind_entry_typename = bar; mind_entry_arity = Prop;
      mind_entry_template = false; mind_entry_consnames = [K];
      mind_entry_lc =
       [_UNBOUND_REL_3 _UNBOUND_REL_2 (S _UNBOUND_REL_1) ->
        _UNBOUND_REL_4 _UNBOUND_REL_3 _UNBOUND_REL_2]}];
   mind_entry_universes = Entries.Monomorphic_ind_entry ;
   mind_entry_private = None}
*
*)

let parameterc = E.Constants.from_stringc "parameter"
let constructorc = E.Constants.from_stringc "constructor"
let inductivec = E.Constants.from_stringc "inductive"
let coinductivec = E.Constants.from_stringc "coinductive"

let lp2inductive_entry ~depth state t =
  let open E in let open Entries in
  let aux_construtors depth params arity itname finiteness state ks =
    let ks = U.lp_list_to_list depth ks in
    let state, names_ktypes =
      CList.fold_map (fun state t ->
        match kind depth t with
        | App(c,E.CData name,[ty]) when CD.is_string name && c == constructorc ->
            let name = Id.of_string (CD.to_string name) in
            let state, ty = lp2constr [] ~depth state ty in
            state,(name, ty)
        | _ -> err Pp.(str"constructor expected: "  ++
                 str (pp2string P.(term depth [] 0 [||]) t)))
      state ks in
    let knames, ktypes = List.split names_ktypes in 
    let ktypes = (* Nice API in the Cq's kernel... *)
      List.map (Vars.subst1 (Constr.mkRel (1+List.length params))) ktypes in
    let used =
      List.fold_left (fun acc t ->
          Univ.LSet.union acc (Univops.universes_of_constr t))
        (Univops.universes_of_constr arity) ktypes in
    let used =
      List.fold_left (fun acc -> function
        | (_,LocalAssumEntry t) | (_,LocalDefEntry t) ->
          Univ.LSet.union acc (Univops.universes_of_constr t))
        used params in
    let state = normalize_univs (restrict_univs state used) in
    let _, evd = get_env_evd state in
    let oe = { Entries.
      mind_entry_typename = itname;
      mind_entry_arity = arity;
      mind_entry_template = false;
      mind_entry_consnames = knames;
      mind_entry_lc = ktypes } in
    state, { Entries.
      mind_entry_record = None;
      mind_entry_finite = finiteness;
      mind_entry_params = params;
      mind_entry_inds = [oe];
      mind_entry_universes =
            Entries.Monomorphic_ind_entry
              (snd (Evd.universe_context evd));
      mind_entry_private = None; }
  in
  let rec aux_decl depth params state t =
    match kind depth t with
    | App(c,E.CData name,[ty;decl]) when CD.is_string name && c == parameterc ->
        let name = Id.of_string (CD.to_string name) in
        let state, ty = lp2constr [] ~depth state ty in
        aux_lam depth ((name,LocalAssumEntry ty) :: params) state decl
    | App(c,E.CData name,[arity;ks])
      when CD.is_string name && (c == inductivec || c == coinductivec) ->
        let name = Id.of_string (CD.to_string name) in
        let fin =
          if c == inductivec then Decl_kinds.Finite
          else Decl_kinds.CoFinite in
        let state, arity = lp2constr [] ~depth state arity in
        begin match kind depth ks with
        | Lam t -> aux_construtors (depth+1) params arity name fin state t
        | _ -> err Pp.(str"lambda expected: "  ++
                 str (pp2string P.(term depth [] 0 [||]) ks))
        end
    | _ -> assert false

  and aux_lam depth params state t =
    match kind depth t with
    | Lam t -> aux_decl (depth+1) params state t
    | _ -> err Pp.(str"lambda expected: "  ++
                 str (pp2string P.(term depth [] 0 [||]) t))
                    
  in
    aux_decl depth [] state t

(* ********************************* }}} ********************************** *)

(* {{{  Declarations.module_body -> elpi ********************************** *)

let rec in_elpi_module_item path (name, item) = match item with
  | Declarations.SFBconst _ ->
      let c = Constant.make2 path name in
      [in_elpi_gr (Globnames.ConstRef c)]
  | Declarations.SFBmind { Declarations.mind_packets = [| _ |] } ->
      let i = (MutInd.make2 path name, 0) in
      [in_elpi_gr (Globnames.IndRef i)]
  | Declarations.SFBmind _ -> nYI "HOAS SFBmind"
  | Declarations.SFBmodule mb -> in_elpi_module mb
  | Declarations.SFBmodtype _ -> []

and in_elpi_module { Declarations.
  mod_mp;             (* Names.module_path *)
  mod_expr;           (* Declarations.module_implementation *)
  mod_type;           (* Declarations.module_signature *)
  mod_type_alg;       (* Declarations.module_expression option *)
  mod_constraints;    (* Univ.ContextSet.t *)
  mod_delta;          (* Mod_subst.delta_resolver *)
  mod_retroknowledge; (* Retroknowledge.action list *)
} =
  match mod_type with
  | Declarations.MoreFunctor _ -> nYI "functors"
  | Declarations.NoFunctor contents ->
      CList.flatten (CList.map (in_elpi_module_item mod_mp) contents)

let in_elpi_module x = U.list_to_lp_list (in_elpi_module x)

let rec in_elpi_modty_item (name, item) = match item with
  | Declarations.SFBconst _ ->
      [ CD.of_string (Label.to_string name) ]
  | Declarations.SFBmind { Declarations.mind_packets = [| _ |] } ->
      [ CD.of_string (Label.to_string name) ]
  | Declarations.SFBmind _ -> nYI "HOAS SFBmind"
  | Declarations.SFBmodule mb -> in_elpi_modty mb
  | Declarations.SFBmodtype _ -> []

and in_elpi_modty { Declarations.
  mod_type;           (* Declarations.modty_signature *)
} =
  match mod_type with
  | Declarations.MoreFunctor _ -> nYI "functors"
  | Declarations.NoFunctor contents ->
      CList.flatten (CList.map in_elpi_modty_item contents)

let in_elpi_module_type x = U.list_to_lp_list (in_elpi_modty x)

(* ********************************* }}} ********************************** *)



(* vim:set foldmethod=marker: *)
