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
module U = API.Extend.Utils
module P = API.Extend.Pp
module CC = API.Extend.Compile
module CS = API.Extend.CustomState
module C = Constr
module EC = EConstr
open Names
open Coq_elpi_utils

let debug = false

(* ************************************************************************ *)
(* ****************** HOAS of Coq terms and goals ************************* *)
(* See also coq-term.elpi (terms)                                           *)
(* ************************************************************************ *)

(* {{{ CData ************************************************************** *)

(* names *)
let namein, isname, nameout, name =
  let open CD in
  let { cin; isc; cout } as name  = declare {
    data_name = "Name.t";
    data_pp = (fun fmt x ->
      Format.fprintf fmt "`%s`" (Pp.string_of_ppcmds (Name.print x)));
    data_eq = (fun _ _ -> true);
    data_hash = (fun _ -> 0);
    data_hconsed = false;
  } in
  cin, isc, cout, name
;;
let in_elpi_name x = E.mkCData (namein x)

let is_coq_name ~depth t =
  match E.look ~depth t with
  | E.CData n -> isname n
  | _ -> false

let in_coq_name ~depth t =
  match E.look ~depth t with
  | E.CData n when isname n -> nameout n
  | E.CData n when CD.is_string n ->
     let s = CD.to_string n in
     if s = "_" then Name.Anonymous
     else Name.Name (Id.of_string s)
  | E.Discard -> Name.Anonymous
  | (E.UVar _ | E.AppUVar _) -> Name.Anonymous
  | _ -> err Pp.(str"Not a name: " ++ str (P.Raw.show_term t))

(* universes *)
let univin, isuniv, univout, univ =
  let open CD in
  let { cin; isc; cout } as univ = declare {
    data_name = "Univ.Universe.t";
    data_pp = (fun fmt x ->
      let s = Pp.string_of_ppcmds (Univ.Universe.pr x) in
      let l = string_split_on_char '.' s in
      let s = match List.rev l with
        | x :: y :: _ -> y ^ "." ^ x
        | _ -> s in
      Format.fprintf fmt "«%s»" s);
    data_eq = Univ.Universe.equal;
    data_hash = Univ.Universe.hash;
    data_hconsed = false;
  } in
  cin, isc, cout, univ
;;
let prop   = E.Constants.from_string "prop"
let typc   = E.Constants.from_stringc "typ"
let sortc  = E.Constants.from_stringc "sort"
let in_elpi_sort s =
  E.mkApp
    sortc
    (match s with
    | Sorts.Prop -> prop
    | Sorts.Set ->
        E.mkApp typc (E.mkCData (univin Univ.type0_univ)) []
    | Sorts.Type u -> E.mkApp typc (E.mkCData (univin u)) [])
    []

let in_elpi_flex_sort t = E.mkApp sortc (E.mkApp typc t []) []

(* constants *)
let grin, isgr, grout, gref =
  let open CD in
  let { cin; isc; cout } as x = declare {
    data_name = "Globnames.global_reference";
    data_pp = (fun fmt x ->
     Format.fprintf fmt "«%s»" (Pp.string_of_ppcmds (Printer.pr_global x)));
    data_eq = Names.GlobRef.equal;
    data_hash = G.RefOrdered.hash;
    data_hconsed = false;
  } in
  cin, isc, cout, x
;;
let indtc  = E.Constants.from_stringc "indt"
let indcc  = E.Constants.from_stringc "indc"
let constc = E.Constants.from_stringc "const"
let in_elpi_gr r =
  let open Globnames in
  match r with
  | (VarRef _ | ConstRef _) -> E.mkApp constc (E.mkCData (grin r)) []
  | IndRef _ -> E.mkApp indtc (E.mkCData (grin r)) []
  | ConstructRef _ -> E.mkApp indcc (E.mkCData (grin r)) []


let mpin, ismp, mpout, modpath =
  let open CD in
  let { cin; isc; cout } as x = declare {
    data_name = "ModPath.t";
    data_pp = (fun fmt x ->
            Format.fprintf fmt "«%s»" (Names.ModPath.to_string x));
    data_eq = Names.ModPath.equal;
    data_hash = Names.ModPath.hash;
    data_hconsed = false;
  } in
  cin, isc, cout, x
;;
let mptyin, istymp, mptyout, modtypath =
  let open CD in
  let { cin; isc; cout } as x = declare {
    data_name = "ModTypePath.t";
    data_pp = (fun fmt x ->
            Format.fprintf fmt "«%s»" (Names.ModPath.to_string x));
    data_eq = Names.ModPath.equal;
    data_hash = Names.ModPath.hash;
    data_hconsed = false;
  } in
  cin, isc, cout, x
;;

let in_elpi_modpath ~ty mp = E.mkCData (if ty then mptyin mp else mpin mp)
let is_modpath ~depth t =
  match E.look ~depth t with E.CData x -> ismp x | _ -> false
let is_modtypath ~depth t =
  match E.look ~depth t with E.CData x -> istymp x | _ -> false
let in_coq_modpath ~depth t =
  match E.look ~depth t with
  | E.CData x when ismp x -> mpout x
  | E.CData x when istymp x -> mptyout x
  | _ -> assert false

(* ********************************* }}} ********************************** *)

(* {{{ constants (app, lam, ...) ****************************************** *)
(* binders *)
let lamc   = E.Constants.from_stringc "lam"
let in_elpi_lam n s t = E.mkApp lamc (in_elpi_name n) [s;E.mkLam t]

let prodc  = E.Constants.from_stringc "prod"
let in_elpi_prod n s t = E.mkApp prodc (in_elpi_name n) [s;E.mkLam t]

let letc   = E.Constants.from_stringc "let"
let in_elpi_let n b s t = E.mkApp letc (in_elpi_name n) [s;b;E.mkLam t]

(* other *)
let appc   = E.Constants.from_stringc "app"
let in_elpi_app_Arg ~depth hd args =
    match E.look ~depth hd, args with
    | E.Const c, [] -> assert false
    | E.Const c, x :: xs -> E.mkApp c x xs
    | E.App(c,x,xs), _ -> E.mkApp c x (xs@args)
    | _ -> assert false
    
let in_elpi_appl hd (args : E.term list) =
  if args = [] then hd
  else E.mkApp appc (U.list_to_lp_list (hd :: args)) []
let in_elpi_app hd (args : E.term array) =
  in_elpi_appl hd (Array.to_list args)

let matchc = E.Constants.from_stringc "match"
let in_elpi_match (*ci_ind ci_npar ci_cstr_ndecls ci_cstr_nargs*) t rt bs =
  E.mkApp matchc t [rt; U.list_to_lp_list bs]

let fixc   = E.Constants.from_stringc "fix"
let in_elpi_fix name rno ty bo =
  E.mkApp fixc (in_elpi_name name) [CD.of_int rno; ty; E.mkLam bo]

(* implicit *)
let holec   = E.Constants.from_stringc "hole"
let in_elpi_implicit = E.mkConst holec

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
   ref2evk : (E.uvar_body * Evar.t) list;
   new_goals : string option;
  }
  and ev2arg
   
  val engine_cc : coq_engine CC.State.component
  val engine : coq_engine CS.component

  val evd_of_engine : coq_engine -> Evd.evar_map
  val names_ctx_of_engine : coq_engine -> Id.t list

  val in_elpi_evar : state -> Evar.t -> state * E.term

  val empty_from_env : Environ.env -> coq_engine

end = struct

 type coq_engine = {
   env : Environ.env;
   evd : Evd.evar_map;
   ev2arg : ev2arg option;
   solution2ev : Evar.t CString.Map.t;
   ref2evk : (E.uvar_body * Evar.t) list;
   new_goals : string option;
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


 let empty_aux env ev2arg =
   {
     env;
     evd = Evd.from_env env;
     ev2arg; 
     solution2ev = CString.Map.empty;
     ref2evk = [];
     new_goals = None;
   }

 let init () = empty_aux (Global.env ()) (Some Evar.Map.empty)

 let empty_from_env env = empty_aux env None 
 
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
let cc_set_command_mode s b = CC.State.set command_mode_cc s b
let cc_set_evd s evd = CC.State.update engine_cc s (fun x -> { x with evd })

let cs_set_ref2evk s ref2evk = CS.update engine s (fun x -> { x with ref2evk })
let cs_get_ref2evk s = (CS.get engine s).ref2evk

let cc_set_new_goals s n =
  CC.State.update engine_cc s (fun x -> { x with new_goals = Some n })
let cs_get_new_goals s = (CS.get engine s).new_goals

(* ********************************* }}} ********************************** *)

let cc_in_elpi_evar state k =
  match in_elpi_evar (Compile state) k with
  | Compile state, t -> state, t
  | Run _, _ -> assert false

(* {{{ HOAS : Constr.t -> elpi ******************************************* *)

let rec pos name cur = function
  | [] -> None
  | Name n :: _ when Names.Id.equal n name -> Some cur
  | Name _ :: xs -> pos name (cur+1) xs
  | Anonymous :: xs -> pos name cur xs

let cc_get_evd s = evd_of_engine (CC.State.get engine_cc s)
let cs_get_evd s = evd_of_engine (CS.get engine s)
let cs_set_evd state e = CS.update engine state (fun x -> { x with evd = e })

let cc_get_names_ctx s = names_ctx_of_engine (CC.State.get engine_cc s)
let cs_get_names_ctx s = names_ctx_of_engine (CS.get engine s)

let get_names_ctx = function
  | Compile s -> cc_get_names_ctx s
  | Run s -> cs_get_names_ctx s

let check_univ_inst univ_inst =
  if not (Univ.Instance.is_empty univ_inst) then
    nYI "HOAS universe polymorphism"

let cc_get_env state = (CC.State.get engine_cc state).env
let cs_get_env state = (CS.get engine state).env

let get_evd = function
  | Compile s -> cc_get_evd s
  | Run s -> cs_get_evd s

let get_env = function
  | Compile s -> cc_get_env s
  | Run s -> cs_get_env s

(* ******************************************* *)
(*  <---- depth ---->                          *)
(*  proof_ctx |- pis \ t                       *)
(* ******************************************* *)

type proof_ctx = Name.t list * int

let constr2lp (proof_ctx, proof_ctx_len) ~depth state t =
  assert(depth >= proof_ctx_len);
  let rec aux ctx state t = match C.kind t with
    | C.Rel n -> state, E.mkConst (ctx - n)
    | C.Var n ->
         state, begin match pos n 0 proof_ctx with
         | Some i -> E.mkConst i
         | None -> in_elpi_gr (G.VarRef n)
         end
    | C.Meta _ -> nYI "HOAS for Meta"
    | C.Evar (k,args) ->
         let state, t = in_elpi_evar state k in
         let section_len = List.length (get_names_ctx state) in
         let args = Array.sub args 0 (Array.length args - section_len) in
         let state, args = CArray.fold_left_map (aux ctx) state args in
         state, mkApp ~depth:ctx t (CArray.rev_to_list args)
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
         let state, args = CArray.fold_left_map (aux ctx) state args in
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
         let state, bs = CArray.fold_left_map (aux ctx) state bs in
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
  if debug then
    Feedback.msg_debug Pp.(str"term2lp: depth=" ++ int depth ++
      str " ctx=" ++ pr_sequence Name.print proof_ctx ++
      str " term=" ++Printer.pr_constr_env (get_env state) (get_evd state) t);
  let state, t = aux depth state t in
  if debug then
    Feedback.msg_debug Pp.(str"term2lp (out): " ++
      str (pp2string (P.term depth) t));
  state, t
;;

(* ********************************* }}} ********************************** *)

(* {{{ HOAS : elpi -> Constr.t * Evd.evar_map ***************************** *)

let in_coq_hole () =
  EC.mkConst (Constant.make2
    (ModPath.MPfile (DirPath.make [Id.of_string "elpi";Id.of_string "elpi"]))
    (Label.make "hole"))

let add_constraints state c = CS.update engine state (fun ({ evd } as x) ->
  { x with evd = Evd.add_universe_constraints evd c })

let new_univ state =
  CS.update_return engine state (fun ({ evd } as x) ->
    let evd, v = Evd.new_univ_level_variable UState.UnivRigid evd in
    let u = Univ.Universe.make v in
    let evd = Evd.add_universe_constraints evd
        (UnivProblem.Set.singleton (UnivProblem.ULe (Univ.type1_univ,u))) in
    { x with evd }, u)

let type_of_global state r = CS.update_return engine state (fun x ->
  let ty, ctx = Global.type_of_global_in_context x.env r in
  let inst, ctx = UnivGen.fresh_instance_from ctx None in
  let ty = Vars.subst_instance_constr inst ty in
  let evd = Evd.merge_context_set Evd.univ_rigid x.evd ctx in
  { x with evd }, ty)

let body_of_constant state c = CS.update_return engine state (fun x ->
  match Global.body_of_constant_body (Environ.lookup_constant c x.env) with
  | Some (bo, ctx) ->
     let inst, ctx = UnivGen.fresh_instance_from ctx None in
     let bo = Vars.subst_instance_constr inst bo in
     let evd = Evd.merge_context_set Evd.univ_rigid x.evd ctx in
     { x with evd }, Some bo
  | None -> x, None)

let new_evar info state =
  CS.update_return engine state (fun ({ evd } as x) ->
     let evd, k = Evd.new_evar evd info in
     { x with evd }, k)

let evar_arity k state =
  let { Evd.evar_hyps } = Evd.find (CS.get engine state).evd k in
  List.length (Environ.named_context_of_val evar_hyps)

let minimize_universes state = CS.update engine state (fun ({ evd } as x) ->
  { x with evd = Evd.minimize_universes evd })

let is_sort ~depth x =
  match E.look ~depth x with
  | E.App(s,_,[]) -> sortc == s
  | _ -> false

let is_prod ~depth x =
  match E.look ~depth x with
  | E.App(s,_,[_;_]) -> prodc == s
  | _ -> false

let is_globalc x = x == constc || x == indtc || x == indcc

let declc = E.Constants.from_stringc "decl"
let defc = E.Constants.from_stringc "def"
let evarc = E.Constants.from_stringc "evar"

exception Underclared_evar of int (*depth*) * E.term

let find_evar var syntactic_constraints depth x =
  let is_evar depth t =
    match E.look ~depth t with
    | E.App(c,x,[t;rx]) when c == evarc ->
          Some(E.look ~depth x,E.look ~depth rx,t)
    | _ -> None in
  try
    CList.find_map (fun { E.goal = (depth,concl); context } ->
      match is_evar depth concl with
      | Some((E.UVar(r,_,_)|E.AppUVar(r,_,_)),_,ty) when r == var ->
          Some (context, (depth,ty))
      | Some(_,(E.UVar(rx,_,_)|E.AppUVar(rx,_,_)),ty) when rx == var ->
          Some (context, (depth,ty))
      | _ -> None) syntactic_constraints
  with Not_found -> raise (Underclared_evar(depth,x))

exception Underclared_ctx_entry of int (*depth*) * E.term

let nth_name ~depth l n =
  match List.nth l n with
  | Name id -> id
  | Anonymous -> raise (Underclared_ctx_entry(depth,E.mkConst n))

let get_id = function Name.Anonymous -> Id.of_string "_" | Name x -> x


let rec of_elpi_ctx syntactic_constraints depth hyps state =

  let mk_fresh =
    let i = ref 0 in
    fun n ->
      incr i;
      Name.mk_name
        (Id.of_string_soft
          (Printf.sprintf "_elpi_renamed_%s_%d_" n !i)) in
  let in_coq_fresh_name ~depth name names =
    match in_coq_name ~depth name with
    | Name.Anonymous -> mk_fresh "Anonymous"
    | Name.Name id as x when List.mem x names ->
        mk_fresh (Id.to_string id)
    | x -> x in

  let aux names depth state t =
    lp2constr ~tolerate_undef_evar:false syntactic_constraints state names depth t in

  let of_elpi_ctx_entry (names,n_names as proof_ctx) ~depth e state =
    match e with
    | `Decl(name,ty) ->
        let name = in_coq_fresh_name ~depth name names in
        let id = get_id name in
        let state, ty = aux proof_ctx depth state ty in
        state, name, Context.Named.Declaration.LocalAssum(id,ty)
    | `Def(name,ty,bo) ->
        let name = in_coq_fresh_name ~depth name names in
        let id = get_id name in
        let state, ty = aux proof_ctx depth state ty in
        let state, bo = aux proof_ctx depth state bo in
        state, name, Context.Named.Declaration.LocalDef(id,bo,ty)
  in

  let select_ctx_entries { E.hdepth = depth; E.hsrc = t } =
    let isConst t = match E.look ~depth t with E.Const _ -> true | _ -> false in
    let destConst t = match E.look ~depth t with E.Const x -> x | _ -> assert false in
    match E.look ~depth t with
    | E.App(c,v,[name;ty]) when c == declc && isConst v ->
       Some (destConst v, depth, `Decl(name,ty))
    | E.App(c,v,[name;ty;bo;_]) when c == defc && isConst v ->
       Some (destConst v, depth, `Def (name,ty,bo))
    | _ ->
        if debug then            
          Feedback.msg_debug Pp.(str "skip entry" ++
            str(pp2string (P.term depth) t));
        None
  in
  let ctx_hyps = CList.map_filter select_ctx_entries hyps in
  let dbl2ctx =
    List.fold_right (fun (i,d,e) m ->
      if Int.Map.mem i m
      then err Pp.(str "Duplicate context entry for " ++
                   str(pp2string (P.term d) (E.mkConst i)))
      else Int.Map.add i (d,e) m)
    ctx_hyps Int.Map.empty in
  
  let rec ctx_entries ctx (n,n_no as proof_ctx) to_restrict state i =
    if i = depth then state, ctx, proof_ctx, to_restrict
    else (* context entry for the i-th variable *)
      if not (Int.Map.mem i dbl2ctx)
      then ctx_entries ctx (n@[Anonymous],n_no+1) (i::to_restrict) state (i+1)
      else
        let d, e = Int.Map.find i dbl2ctx in
        let state, name, e = of_elpi_ctx_entry proof_ctx ~depth:d e state in
        ctx_entries (e::ctx) (n@[name],n_no+1) to_restrict state (i+1)
  in
    ctx_entries [] ([],0) [] state 0

(* ***************************************************************** *)
(* <-- depth -->                                                     *)
(* names |- pis |- t                                                 *)
(*   |        \- lp fresh constans                                   *)
(*   \- proof_ctx                                                    *)
(* ***************************************************************** *)
and lp2constr ~tolerate_undef_evar syntactic_constraints state proof_ctx depth t =

  let rec aux (names,n_names as ctx) depth state t =
    match E.look ~depth t with

    | E.App(s,p,[]) when sortc == s && p == prop -> state, EC.mkProp
    | E.App(s,ty,[]) when sortc == s ->
        begin match E.look ~depth ty with
        | E.App(ty,c,[]) when typc == ty ->
            begin match E.look ~depth c with
            | E.CData x when isuniv x -> state, EC.mkType (univout x)
            | E.UVar _ | E.AppUVar _ | E.Discard ->
               let state, t = new_univ state in
               state, EC.mkType t
            | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Raw.show_term t))
            end
        | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Raw.show_term t))
        end

    (* constants *)
    | E.App(c,d,[]) when (indtc == c || indcc == c || constc == c) ->
       begin match E.look ~depth d with
       | E.CData gr when isgr gr ->
           begin match grout gr with
           | G.VarRef x       when constc == c -> state, EC.mkVar x
           | G.ConstRef x     when constc == c -> state, EC.mkConst x
           | G.ConstructRef x when indcc == c -> state, EC.mkConstruct x
           | G.IndRef x       when indtc == c -> state, EC.mkInd x
           | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Raw.show_term t))
          end
       | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Raw.show_term t))
       end

    (* binders *)
    | E.App(c,name,[s;t]) when lamc == c || prodc == c ->
        let name = in_coq_name ~depth name in
        let state, s = aux ctx depth state s in
        let state, t = aux_lam ctx depth state t in
        if lamc == c then state, EC.mkLambda (name,s,t)
        else state, EC.mkProd (name,s,t)
    | E.App(c,name,[s;b;t]) when letc == c ->
        let name = in_coq_name ~depth name in
        let state,s = aux ctx depth state s in
        let state,b = aux ctx depth state b in
        let state,t = aux_lam ctx depth state t in
        state, EC.mkLetIn (name,b,s,t)
        
    | E.Const n ->
                    
       if n == holec then 
         state, in_coq_hole ()
       else if n >= 0 then
         if n < n_names then state, EC.mkVar(nth_name ~depth names n)
         else if n < depth then state, EC.mkRel(depth - n)
         else 
           err Pp.(str"wrong bound variable (BUG):" ++ str (E.Constants.show n))
       else
          err Pp.(str"wrong constant:" ++ str (E.Constants.show n))

    (* app *)
    | E.App(c,x,[]) when appc == c ->
         (match U.lp_list_to_list ~depth x with
         | x :: xs -> 
            let state,x = aux ctx depth state x in
            let state,xs = CList.fold_left_map (aux ctx depth) state xs in
            state, EC.mkApp (x,Array.of_list xs)
         | _ -> assert false) (* TODO *)
    
    (* match *)
    | E.App(c,t,[rt;bs]) when matchc == c ->
        let state, t = aux ctx depth state t in
        let state, rt = aux ctx depth state rt in
        let state, bt =
          CList.fold_left_map (aux ctx depth) state (U.lp_list_to_list ~depth bs) in
        let ind =
          (* XXX fixme reduction *)
          let evd = cs_get_evd state in
          let rec aux t o = match EC.kind evd t with
            | C.Lambda(_,s,t) -> aux t (Some s)
            | _ -> match o with
              | None -> assert false (* wrong shape of rt XXX *)
              | Some t ->
                 match safe_destApp evd t with
                 | C.Ind i, _ -> fst i
                 | _ -> assert false (* wrong shape of rt XXX *)
          in
            aux rt None in
        let ci =
          Inductiveops.make_case_info (CS.get engine state).env ind C.RegularStyle in
        state, EC.mkCase (ci,rt,t,Array.of_list bt)

    (* fix *)
    | E.App(c,name,[rno;ty;bo]) when fixc == c ->
        let name = in_coq_name ~depth name in
        let state, ty = aux ctx depth state ty in
        let state, bo = aux_lam ctx depth state bo in
        let rno =
          match E.look ~depth rno with
          | E.CData n when CD.is_int n -> CD.to_int n
          | _ -> err Pp.(str"Not an int: " ++ str (P.Raw.show_term rno)) in
        state, EC.mkFix (([|rno|],0),([|name|],[|ty|],[|bo|]))
    
    (* evar *)
    | (E.UVar (r,_,_) | E.AppUVar (r,_,_)) as x ->
        let args =
          match x with
          | E.UVar (_,vardepth,ano) ->
               CList.init (vardepth+ano) E.mkConst
          | E.AppUVar (_,vardepth,args) ->
               CList.init vardepth E.mkConst @ args
          | _ -> assert false in
        begin try
          let ext_key = List.assq r (cs_get_ref2evk state) in
          let state, args = CList.fold_left_map (aux ctx depth) state args in
          let args = List.rev args in
          let section_args =
            CList.rev_map EC.mkVar (cs_get_names_ctx state) in
          let arity = evar_arity ext_key state in
          let ev =
            let all_args = args @ section_args in
            let nargs = List.length all_args in
            if nargs > arity then
              let args1, args2 = CList.chop (nargs - arity) all_args in
              EC.mkApp(EC.mkEvar (ext_key,Array.of_list args2),
                         CArray.rev_of_list args1)
            else EC.mkEvar (ext_key,Array.of_list (args @ section_args)) in
          state, ev
        with Not_found ->
          let context, ty =
            try find_evar r syntactic_constraints depth t 
            with Underclared_evar _ when tolerate_undef_evar ->
              [], (0, in_elpi_sort Sorts.Prop)
          in
          let state, k = declare_evar ~depth context ty state in
          let state = cs_set_ref2evk state ((r,k) :: cs_get_ref2evk state) in
          let x =
            (* eta contraction in elpi *)
            let missing = List.length context - List.length args in
            if missing <= 0 then t else 
              match x with
              | E.UVar (r,vardepth,ano) -> E.mkUVar r vardepth (ano+missing)
              | E.AppUVar (r,vardepth,xs) ->
                   let ano = List.length args in
                   let extra = CList.init missing (fun i -> E.mkConst(i+ano)) in
                   E.mkAppUVar r vardepth (xs @ extra)
              | _ -> assert false  
            in
          aux ctx depth state x
        end

    (* errors *)
    | E.Lam _ ->
         err Pp.(str "out of place lambda: "++
                 str (pp2string P.(term depth) t))

    | _ -> err Pp.(str"Not a HOAS term:" ++ str (P.Raw.show_term t))

  and aux_lam ctx depth s t = match E.look ~depth t with
    | E.Lam t -> aux ctx (depth+1) s t
    | E.UVar(r,d,ano) -> aux ctx (depth+1) s (E.mkUVar r d ano(*+1*))
    | E.AppUVar(r,d,args) ->
         aux ctx (depth+1) s (E.mkAppUVar r d args(*@[E.mkConst depth]*))
    | _ -> err Pp.(str"HOAS: expecting a lambda, got: " ++
             str(pp2string (P.term depth) t))


  (* evar info read back *)

  and declare_evar ~depth ctx (depth,concl) state =
    let state, named_ctx, (names,n_names), _ =
      of_elpi_ctx syntactic_constraints depth ctx state in
    if debug then
      Feedback.msg_debug Pp.(str"lp2constr: declare_evar ctx=" ++
        pr_sequence Name.print names ++ str" depth=" ++ int depth ++
        str " term=" ++ str(pp2string (P.term depth) concl));
    let state, ty = aux (names,n_names) depth state concl in
    let named_ctx =
      named_ctx @ EC.named_context (CS.get engine state).env in
    let info = Evd.make_evar (EC.val_of_named_context named_ctx) ty in
    let state, k = new_evar info state in
    state, k

  in
  try
    if debug then
      Feedback.msg_debug Pp.(str"lp2term: depth=" ++ int depth ++
        str " ctx=" ++ pr_sequence Name.print (fst proof_ctx) ++
        str " term=" ++ str (pp2string (P.term depth) t));
    let state, t = aux proof_ctx depth state t in
    if debug then
      Feedback.msg_debug Pp.(str"lp2term: out=" ++ 
        (Printer.pr_econstr_env (cs_get_env state) (cs_get_evd state) t));
    state, t
  with
  | Underclared_evar(depth,x) ->
    err Pp.(str"The term "++
      str(pp2string P.(term depth) t) ++ 
      str" contains the unification variable " ++
      str(pp2string P.(term depth) x) ++
      str" that has no declared type in the constraint store:" ++ spc() ++
      str(pp2string P.(list (fun fmt { E.goal = (depth,t) } ->
             term depth fmt t) ",")
          syntactic_constraints))
  | Underclared_ctx_entry(depth,x) ->
    err Pp.(str"The term "++
      str(pp2string P.(term depth) t) ++ 
      str" contains the name " ++
      str(pp2string P.(term depth) x) ++
      str" that has no declared type in the context")

let lp2constr ?(tolerate_undef_evar=false) syntactic_constraints state proof_ctx depth t =
  lp2constr ~tolerate_undef_evar syntactic_constraints state proof_ctx depth t      
let mk_pi_arrow hyp rest =
  E.mkApp E.Constants.pic (E.mkLam (E.mkApp E.Constants.implc hyp [rest])) []

let mk_decl c name ty = E.mkApp declc c [in_elpi_name name; ty]
let mk_def c name bo norm ty = E.mkApp defc c [in_elpi_name name; ty; bo; norm]

let cc_mkArg ~name_hint ~lvl state =
  let args = CList.init lvl E.mkConst in
  CC.fresh_Arg ~name_hint ~args state

let mkArg name_hint lvl = function
  | Compile state ->
      let state, name, t = cc_mkArg ~name_hint ~lvl state in
      Compile state, name,t 
  | Run _ -> err Pp.(str"mkArg called at runtime")

let in_elpi_ctx ~depth state ctx ?(mk_ctx_item=mk_pi_arrow) kont =
  let open Context.Named.Declaration in
  let rec aux depth (ctx, ctx_len as ctx_w_len) nm hyps state = function
    | [] -> kont (ctx, ctx_len) nm (List.rev hyps) ~depth state
    | LocalAssum (name, ty) :: rest ->
        let c = E.mkConst depth in
        let nm = Id.Map.add name depth nm in
        let name = Name name in
        let state, ty = constr2lp ctx_w_len ~depth:(depth+1) state ty in
        let hyp = mk_decl c name ty in
        let hyps = (hyp, depth+1) :: hyps in
        let ctx_w_len = ctx @ [name], ctx_len+1 in
        let state, rest = aux (depth+1) ctx_w_len nm hyps state rest in
        state, mk_ctx_item hyp rest
    | LocalDef (name,bo,ty) :: rest ->
        let c = E.mkConst depth in
        let nm = Id.Map.add name depth nm in
        let name = Name name in
        let state, ty = constr2lp ctx_w_len ~depth:(depth+1) state ty in
        let state, bo = constr2lp ctx_w_len ~depth:(depth+1) state bo in
        let state, _, norm = mkArg "norm" ctx_len state in
        let hyp = mk_def c name bo norm ty in
        let hyps = (hyp, depth+1) :: hyps in
        let ctx_w_len = ctx @ [name], ctx_len+1 in
        let state, rest = aux (depth+1) ctx_w_len nm hyps state rest in
        state, mk_ctx_item hyp rest
  in
    aux depth ([],0) Id.Map.empty [] state (List.rev ctx)

let cc_in_elpi_ctx ~depth state ctx ?mk_ctx_item kont =
  let kont ctx map hyps ~depth s =
    match s with
    | Compile s ->
        let s, t = kont ctx map hyps ~depth s in
        Compile s, t
    | Run _ -> assert false in
  match in_elpi_ctx ~depth (Compile state) ctx ?mk_ctx_item kont with
  | Compile state, t -> state, t
  | Run _, _ -> assert false

(* ********************************* }}} ********************************** *)

let cc_constr2lp proof_ctx ~depth state t =
  let state = Compile state in
  match constr2lp proof_ctx ~depth state t with
  | Compile state, t -> state, t
  | Run _, _ -> assert false

let constr2lp ?(proof_ctx=[],0) ~depth state t =
  let state = Run state in
  match constr2lp proof_ctx ~depth state t with
  | Run state, t -> state, t
  | Compile _, _ -> assert false

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
  state, E.mkApp E.Constants.(from_stringc "cs-instance") proj [value;solution]
;;
(* ********************************* }}} ********************************** *)

(* {{{ Typeclasses -> elpi ************************************************ *)

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
  state, E.mkApp (E.Constants.from_stringc "tc-instance")
    (in_elpi_gr solution) [E.C.of_int priority]
;;
(* ********************************* }}} ********************************** *)


let cs_get_solution2ev state = (CS.get engine state).solution2ev

let cc_push_env state name =
  let open Context.Rel.Declaration in
  CC.State.update engine_cc state (fun ({ env } as x) ->
     { x with env = Environ.push_rel (LocalAssum(name,C.mkProp)) env })

let get_global_env_evd state =
  let { env; evd } = CS.get engine state in
  Environ.push_context_set (Evd.universe_context_set evd) env, evd

let get_current_env_evd ~depth hyps solution =
  let syntatic_constraints = E.constraints solution.E.constraints in
(*   let state = in_coq_solution solution in *)
  let state = solution.E.state in
  let state, named_ctx, proof_context, _to_restrict =
    of_elpi_ctx syntatic_constraints depth hyps state in

  let { env; evd } = CS.get engine state in
(*
  Feedback.msg_debug Pp.(str "ctx: " ++
    Printer.pr_named_context env evd (Obj.magic named_ctx));
*)

  let env = EC.push_named_context named_ctx env in
(*
  let state = CS.set engine lp2c_state.state { state with env } in
  let env, evd = get_global_env_evd state in
*)
  state, env, evd, proof_context

let set_evd state evd = CS.update engine state (fun x -> { x with evd })

(* We reset the evar map since it depends on the env in which it was created *)
let grab_global_env state =
  let env = Global.env () in
  CS.update engine state (fun _ -> CoqEngine_HOAS.empty_from_env env)

let cs_lp2constr sc s ctx ~depth t = lp2constr sc s ctx depth t

let lp2constr ?tolerate_undef_evar syntactic_constraints state ?(proof_ctx=[],0) ~depth t =  
  let state = cs_set_ref2evk state [] in
  let state, t = lp2constr ?tolerate_undef_evar syntactic_constraints state proof_ctx depth t in
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
let recordc = E.Constants.from_stringc "record"
let fieldc = E.Constants.from_stringc "field"
let end_recordc = E.Constants.from_stringc "end-record"

type record_field_spec = { name : string; is_coercion : bool }

let force_name =
  let n = ref 0 in      
  function
  | Name.Name x -> x
  | _ ->
     incr n; Id.of_string (Printf.sprintf "_missing_parameter_name_%d_" !n)

let lp2inductive_entry ~depth state t =
  let open E in let open Entries in

  (* turns a prefix of the arity (corresponding to the non-uniform parameters)
   * into a context *)
  let decompose_nu_arity evd arity nupno msg =
    let ctx, rest = EC.decompose_prod_assum evd arity in
    let n = Context.Rel.length ctx in
    if n < nupno then err Pp.(int nupno ++
      str" non uniform parameters declared, but only " ++ int n ++
      str " products found in " ++ str msg);
    let unpctx = CList.lastn nupno ctx in
    let ctx = CList.firstn (n - nupno) ctx in
    let nuparams = unpctx |> List.map (function
      | Context.Rel.Declaration.LocalAssum(n,t) ->
          force_name n, `LocalAssumEntry t
      | Context.Rel.Declaration.LocalDef(n,b,_) ->
          force_name n, `LocalDefEntry b) in
    nuparams, EC.it_mkProd_or_LetIn rest ctx in

  (* To check if all constructors share the same context of non-uniform
   * parameters *)
  let rec cmp_nu_ctx evd k ~arity_nuparams:c1 c2 =
    match c1, c2 with
    | [], [] -> ()
    | (n1,`LocalAssumEntry t1) :: c1, (n2,`LocalAssumEntry t2) :: c2 ->
        if not (EC.eq_constr_nounivs evd (EC.Vars.lift 1 t1) t2) && 
           not (EC.isEvar evd t2) then
          err Pp.(str"in constructor " ++ Id.print k ++
            str" the type of " ++
            str"non uniform argument " ++ Id.print n2 ++
            str" is different from the type declared in the inductive"++
            str" type arity as " ++ Id.print n1);
      cmp_nu_ctx evd k ~arity_nuparams:c1 c2
    | _ -> assert false in

  let aux_construtors depth params nupno arity itname finiteness state ks =

    let params = List.map (fun (x,y) -> force_name x,y) params in
    let paramno = List.length params in

    (* decode constructors' types *)
    let state, names_ktypes =
      CList.fold_left_map (fun state t ->
        match look ~depth t with
        | App(c,name,[ty]) when c == constructorc ->
            begin match look ~depth name with
            | CData name when CD.is_string name ->
              let name = Id.of_string (CD.to_string name) in
              let state, ty = lp2constr [] ~depth state ty in
              state,(name, ty)
            | _ -> err Pp.(str"@gref expected: "  ++
                 str (pp2string P.(term depth) name))
            end
        | _ -> err Pp.(str"constructor expected: "  ++
                 str (pp2string P.(term depth) t)))
      state ks in
    let knames, ktypes = List.split names_ktypes in 

    let env, evd = get_global_env_evd state in

    (* Handling of non-uniform parameters *)
    let arity, nuparams, ktypes =
      if nupno = 0 then arity, [], ktypes
      else
        let nuparams, arity =
          decompose_nu_arity evd arity nupno "inductive type arity" in
        let replace_nup name t =
          let cur_nuparams, t =
            decompose_nu_arity evd t nupno
              (" constructor " ^ Id.to_string name) in
          cmp_nu_ctx evd name ~arity_nuparams:nuparams cur_nuparams;
          t
         in
        let ktypes = List.map2 replace_nup knames ktypes in
        arity, nuparams, ktypes in

    (* Relocation to match Coq's API.
     * From
     *  Params, Ind, NuParams |- ktys
     * To
     *  Ind, Params, NuParams |- ktys
     *)
    let ktypes = ktypes |> List.map (fun t ->
      let subst = CList.init (nupno + paramno + 1) (fun i ->
        if i < nupno then EC.mkRel (i+1)
        else if i = nupno then
          let ind = EC.mkRel (nupno + paramno + 1) in
          if paramno = 0 then ind
          else
            let ps =
              CArray.init paramno (fun i -> EC.mkRel (nupno + paramno - i)) in
            EC.mkApp (ind,ps)
        else EC.mkRel i) in
      EC.Vars.substl subst t
    ) in

    let params = nuparams @ params in

    let state = minimize_universes state in
    let ktypes = List.map (EC.to_constr evd) ktypes in
    let params = List.map (function
      | x, `LocalAssumEntry t -> x, LocalAssumEntry(EC.to_constr evd t)
      | x, `LocalDefEntry t -> x, LocalDefEntry(EC.to_constr evd t))
      params in
    let arity = EC.to_constr evd arity in
    let used =
      List.fold_left (fun acc t ->
          Univ.LSet.union acc (EConstr.universes_of_constr evd (EConstr.of_constr t)))
        (EConstr.universes_of_constr evd (EConstr.of_constr arity)) ktypes in
    let used =
      List.fold_left (fun acc -> function
        | (_,LocalAssumEntry t) | (_,LocalDefEntry t) ->
          Univ.LSet.union acc (EConstr.universes_of_constr evd (EConstr.of_constr t)))
        used params in
    let evd = Evd.restrict_universe_context evd used in
    
    let oe = {
      mind_entry_typename = itname;
      mind_entry_arity = arity;
      mind_entry_template = false;
      mind_entry_consnames = knames;
      mind_entry_lc = ktypes } in
    state, {
      mind_entry_record = None;
      mind_entry_finite = finiteness;
      mind_entry_params = params;
      mind_entry_inds = [oe];
      mind_entry_universes =
            Monomorphic_ind_entry (Evd.universe_context_set evd);
      mind_entry_private = None; }
  in
  let rec aux_fields depth ind fields =
    match E.look ~depth fields with
    | App(c,coercion,[n; ty; fields]) when c == fieldc ->
      begin match E.look ~depth n, E.look ~depth fields with
      | CData name, Lam fields when CD.is_string name ->
        let fs, tf = aux_fields (depth+1) ind fields in
        let is_coercion = in_elpi_tt = coercion in
        let name = CD.to_string name in
        { name; is_coercion } :: fs,
          in_elpi_prod (in_coq_name ~depth n) ty tf
      | _ -> err Pp.(str"field/end-record expected: "++
                   str (pp2string P.(term depth) fields))
      end
    | Const c when c == end_recordc -> [], ind
    | _ ->  err Pp.(str"field/end-record expected: "++ 
                 str (pp2string P.(term depth) fields))
  in

  let rec aux_decl depth params state t =
    match E.look ~depth t with
    | App(c,name,[ty;decl]) when is_coq_name ~depth name && c == parameterc ->
        let name = in_coq_name ~depth name in
        let state, ty = lp2constr [] ~depth state ty in
        aux_lam depth ((name,`LocalAssumEntry ty) :: params) state decl
    | App(c,name,[nupno;arity;ks])
      when (c == inductivec || c == coinductivec) ->
      begin match E.look ~depth name, E.look ~depth nupno  with
      | CData name, CData nupno when CD.is_string name && CD.is_int nupno ->
        let name = Id.of_string (CD.to_string name) in
        let nupno = CD.to_int nupno in
        let fin =
          if c == inductivec then Declarations.Finite
          else Declarations.CoFinite in
        let state, arity = lp2constr [] ~depth state arity in
        begin match E.look ~depth ks with
        | Lam t -> 
            let ks = U.lp_list_to_list ~depth:(depth+1) t in
            let state, idecl = 
              aux_construtors (depth+1) params nupno arity name fin state ks in
            state, idecl, None
        | _ -> err Pp.(str"lambda expected: "  ++
                 str (pp2string P.(term depth) ks))
        end
      | _ -> err Pp.(str"@id and int expected, got: "++ 
                 str (pp2string P.(term depth) name) ++ str " " ++
                 str (pp2string P.(term depth) nupno))
      end
    | App(c,name,[arity;kn;fields]) when c == recordc ->
      begin match E.look ~depth name, E.look ~depth kn with
      | CData name, CData kname when CD.is_string name && CD.is_string kname ->
        let state, arity = lp2constr [] ~depth state arity in
        let name = Id.of_string (CD.to_string name) in
        let fields = U.move ~from:depth ~to_:(depth+1) fields in
        (* We simulate the missing binders for the inductive *)
        let ind = E.mkConst depth in
        let depth = depth + 1 in
        let fields_names_coercions, kty = aux_fields depth ind fields in
        let k = [mkApp constructorc kn [kty]] in
        let state, idecl =
          aux_construtors depth params 0 arity name Declarations.Finite state k in
        state, idecl, Some fields_names_coercions
      | _ -> err Pp.(str"@id expected, got: "++ 
                 str (pp2string P.(term depth) name))
      end
    | _ -> err Pp.(str"(co)inductive/record expected: "++ 
                 str (pp2string P.(term depth) t))
  and aux_lam depth params state t =
    match E.look ~depth t with
    | Lam t -> aux_decl (depth+1) params state t
    | _ -> err Pp.(str"lambda expected: "  ++
                 str (pp2string P.(term depth) t))
                    
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

and in_elpi_module : 'a.'a Declarations.generic_module_body -> E.term list =
  fun { Declarations.
  mod_mp;             (* Names.module_path *)
  mod_expr;           (* Declarations.module_implementation *)
  mod_type;           (* Declarations.module_signature *)
  mod_type_alg;       (* Declarations.module_expression option *)
  mod_constraints;    (* Univ.ContextSet.t *)
  mod_delta;          (* Mod_subst.delta_resolver *)
  mod_retroknowledge; (* Retroknowledge.action list *)
} ->
  match mod_type with
  | Declarations.MoreFunctor _ -> nYI "functors"
  | Declarations.NoFunctor contents ->
      CList.flatten (CList.map (in_elpi_module_item mod_mp) contents)

let rec in_elpi_modty_item (name, item) = match item with
  | Declarations.SFBconst _ ->
      [ Label.to_string name ]
  | Declarations.SFBmind { Declarations.mind_packets = [| _ |] } ->
      [ Label.to_string name ]
  | Declarations.SFBmind _ -> nYI "HOAS SFBmind"
  | Declarations.SFBmodule mb -> in_elpi_modty mb
  | Declarations.SFBmodtype _ -> []

and in_elpi_modty : 'a.'a Declarations.generic_module_body -> string list =
  fun { Declarations.mod_type; (* Declarations.modty_signature *) } ->
  match mod_type with
  | Declarations.MoreFunctor _ -> nYI "functors"
  | Declarations.NoFunctor contents ->
      CList.flatten (CList.map in_elpi_modty_item contents)

let in_elpi_module (x : Declarations.module_body) = in_elpi_module x

let in_elpi_module_type (x : Declarations.module_type_body) = in_elpi_modty x

(* ********************************* }}} ********************************** *)

let is_unspecified_term ~depth x =
  match E.look ~depth x with
  | E.Discard -> true
  | (E.UVar _ | E.AppUVar _) -> true
  | x -> E.kool x = in_elpi_implicit

(* {{{  elpi -> elpi ******************************************************** *)

let clausec = E.Constants.from_stringc "clause"
let beforec = E.Constants.from_stringc "before"
let afterc = E.Constants.from_stringc "after"

let in_elpi_clause ~depth t =
  let get_clause_name ~depth name =
    match E.look ~depth name with
    | E.CData n when CD.is_string n -> CD.to_string n
    | _ -> err Pp.(str "Clause name not a string") in
  match E.look ~depth t with     
  | E.App(c,name,[grafting;clause]) when c == clausec ->
       let name =
         if is_unspecified_term ~depth name then None
         else Some(get_clause_name ~depth name) in
       let graft =
         if is_unspecified_term ~depth grafting then None
         else match E.look ~depth grafting with
         | E.App(c,name,[]) when c == beforec ->
             Some(`Before, get_clause_name ~depth name)
         | E.App(c,name,[]) when c == afterc ->
             Some(`After, get_clause_name ~depth name) 
         | _ -> err Pp.(str "Ill formed grafting specification") in
       U.clause_of_term ?name ?graft ~depth clause
  | _ -> err Pp.(str"Ill formed clause")

(* ********************************* }}} ********************************** *)

(* vim:set foldmethod=marker: *)
